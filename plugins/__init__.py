"""Plugin discovery and loading system."""

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
from fastapi import FastAPI
from fastapi.responses import HTMLResponse, Response


PLUGINS_DIR = Path(__file__).parent
LOADED_PLUGINS = []

# Persistent pip install location (survives container restarts)
_PIP_TARGET = Path(os.environ.get("CONFIG_DIR", "/config")) / "pip_packages"


def _install_requirements(plugin_dir: Path, plugin_id: str):
    """Install plugin requirements.txt to a persistent location."""
    req_file = plugin_dir / "requirements.txt"
    if not req_file.exists():
        return True

    _PIP_TARGET.mkdir(parents=True, exist_ok=True)
    pip_target = str(_PIP_TARGET)

    # Add to sys.path if not already there
    if pip_target not in sys.path:
        sys.path.insert(0, pip_target)

    # Check if already installed (marker file)
    marker = _PIP_TARGET / f".installed_{plugin_id}"
    req_hash = str(hash(req_file.read_text()))
    if marker.exists() and marker.read_text().strip() == req_hash:
        return True  # Already installed, same requirements

    print(f"[Plugin] Installing requirements for '{plugin_id}' (this can take a while for large deps)...")
    try:
        result = subprocess.run(
            [sys.executable, "-m", "pip", "install",
             "--target", pip_target,
             "--quiet",
             "-r", str(req_file)],
            capture_output=True, text=True, timeout=1800,
        )
        if result.returncode == 0:
            marker.write_text(req_hash)
            print(f"[Plugin] Requirements installed for '{plugin_id}'")
            return True
        else:
            err_lower = result.stderr.lower() if result.stderr else ""
            if "read-only" in err_lower or "permission denied" in err_lower:
                print(f"[Plugin] Optional dependencies not installed for '{plugin_id}' — functionality may be limited. Install dependencies manually or configure an external service if available.")
            else:
                print(f"[Plugin] Failed to install requirements for '{plugin_id}': {result.stderr[:300]}")
            return False
    except Exception as e:
        err_lower = str(e).lower()
        if "read-only" in err_lower or "permission denied" in err_lower:
            print(f"[Plugin] Optional dependencies not installed for '{plugin_id}' — functionality may be limited. Install dependencies manually or configure an external service if available.")
        else:
            print(f"[Plugin] Error installing requirements for '{plugin_id}': {e}")
        return False


def load_plugins(app: FastAPI, context: dict):
    """Discover and load all plugins from built-in and user directories."""

    # Collect plugin directories — user plugins first so they override built-in
    plugin_dirs = []
    user_plugins_dir = os.environ.get("SLOPSMITH_PLUGINS_DIR")
    if user_plugins_dir:
        user_path = Path(user_plugins_dir)
        if user_path.is_dir() and user_path != PLUGINS_DIR:
            plugin_dirs.append(user_path)
    if PLUGINS_DIR.is_dir():
        plugin_dirs.append(PLUGINS_DIR)

    if not plugin_dirs:
        return

    # Add persistent pip target to sys.path
    pip_target = str(_PIP_TARGET)
    if _PIP_TARGET.exists() and pip_target not in sys.path:
        sys.path.insert(0, pip_target)

    loaded_ids = set()

    for plugins_base_dir in plugin_dirs:
        for plugin_dir in sorted(plugins_base_dir.iterdir()):
            if not plugin_dir.is_dir():
                continue

            manifest_path = plugin_dir / "plugin.json"
            if not manifest_path.exists():
                continue

            try:
                manifest = json.loads(manifest_path.read_text())
            except Exception as e:
                print(f"[Plugin] Failed to read {manifest_path}: {e}")
                continue

            plugin_id = manifest.get("id")
            if not plugin_id:
                continue

            if plugin_id in loaded_ids:
                print(f"[Plugin] Skipping duplicate '{plugin_id}' from {plugins_base_dir}")
                continue
            loaded_ids.add(plugin_id)

            # Install plugin requirements if present
            _install_requirements(plugin_dir, plugin_id)

            # Add plugin directory to sys.path so it can import its own modules
            plugin_dir_str = str(plugin_dir)
            if plugin_dir_str not in sys.path:
                sys.path.insert(0, plugin_dir_str)

            # Load routes using importlib to avoid module name collisions
            routes_file = manifest.get("routes")
            if routes_file:
                try:
                    module_name = f"plugin_{plugin_id}_routes"
                    spec = importlib.util.spec_from_file_location(
                        module_name, str(plugin_dir / routes_file))
                    routes_module = importlib.util.module_from_spec(spec)
                    sys.modules[module_name] = routes_module
                    spec.loader.exec_module(routes_module)
                    if hasattr(routes_module, "setup"):
                        routes_module.setup(app, context)
                        print(f"[Plugin] Loaded routes for '{plugin_id}'")
                except Exception as e:
                    print(f"[Plugin] Failed to load routes for '{plugin_id}': {e}")
                    import traceback
                    traceback.print_exc()

            LOADED_PLUGINS.append({
                "id": plugin_id,
                "name": manifest.get("name", plugin_id),
                "nav": manifest.get("nav"),
                "has_screen": bool(manifest.get("screen")),
                "has_script": bool(manifest.get("script")),
                "has_settings": bool(manifest.get("settings")),
                "_dir": plugin_dir,
                "_manifest": manifest,
            })
            print(f"[Plugin] Registered '{plugin_id}' ({manifest.get('name', '')})")


def _check_plugin_update(plugin_dir: Path) -> dict | None:
    """Check if a plugin's git repo has updates available."""
    git_dir = plugin_dir / ".git"
    if not git_dir.exists():
        return None
    try:
        # Fetch latest from remote (quick, refs only)
        subprocess.run(
            ["git", "fetch", "--quiet"],
            cwd=str(plugin_dir), capture_output=True, timeout=15,
        )
        # Compare local HEAD with remote tracking branch
        result = subprocess.run(
            ["git", "rev-list", "HEAD..@{u}", "--count"],
            cwd=str(plugin_dir), capture_output=True, text=True, timeout=10,
        )
        if result.returncode != 0:
            return None
        behind = int(result.stdout.strip())
        # Get current and remote commit hashes
        local = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=str(plugin_dir), capture_output=True, text=True, timeout=5,
        ).stdout.strip()
        remote = subprocess.run(
            ["git", "rev-parse", "--short", "@{u}"],
            cwd=str(plugin_dir), capture_output=True, text=True, timeout=5,
        ).stdout.strip()
        return {"behind": behind, "local": local, "remote": remote}
    except Exception:
        return None


def register_plugin_api(app: FastAPI):
    """Register the plugin discovery API endpoints."""

    @app.get("/api/plugins")
    def list_plugins():
        return [
            {
                "id": p["id"],
                "name": p["name"],
                "nav": p["nav"],
                "has_screen": p["has_screen"],
                "has_script": p["has_script"],
                "has_settings": p["has_settings"],
            }
            for p in LOADED_PLUGINS
        ]

    @app.get("/api/plugins/updates")
    def check_updates():
        """Check all plugins for available git updates."""
        updates = {}
        for p in LOADED_PLUGINS:
            info = _check_plugin_update(p["_dir"])
            if info and info["behind"] > 0:
                updates[p["id"]] = {
                    "name": p["name"],
                    "behind": info["behind"],
                    "local": info["local"],
                    "remote": info["remote"],
                }
        return {"updates": updates}

    @app.post("/api/plugins/{plugin_id}/update")
    def update_plugin(plugin_id: str):
        """Pull latest changes for a plugin. Stashes local edits first."""
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                git_dir = p["_dir"] / ".git"
                if not git_dir.exists():
                    return {"error": "Not a git repository"}
                cwd = str(p["_dir"])
                try:
                    # Stash any local modifications so pull doesn't fail
                    subprocess.run(
                        ["git", "stash", "--quiet"],
                        cwd=cwd, capture_output=True, timeout=10,
                    )
                    result = subprocess.run(
                        ["git", "pull", "--ff-only"],
                        cwd=cwd, capture_output=True, text=True, timeout=30,
                    )
                    if result.returncode != 0:
                        # Restore stash on failure
                        subprocess.run(
                            ["git", "stash", "pop", "--quiet"],
                            cwd=cwd, capture_output=True, timeout=10,
                        )
                        return {"error": result.stderr[:500]}
                    return {"ok": True, "message": result.stdout.strip()}
                except Exception as e:
                    return {"error": str(e)}
        return {"error": "Plugin not found"}

    @app.get("/api/plugins/{plugin_id}/screen.html")
    def plugin_screen_html(plugin_id: str):
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                screen_file = p["_dir"] / p["_manifest"].get("screen", "screen.html")
                if screen_file.exists():
                    return HTMLResponse(screen_file.read_text(encoding="utf-8"))
        return HTMLResponse("", status_code=404)

    @app.get("/api/plugins/{plugin_id}/screen.js")
    def plugin_screen_js(plugin_id: str):
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                script_file = p["_dir"] / p["_manifest"].get("script", "screen.js")
                if script_file.exists():
                    return Response(script_file.read_text(encoding="utf-8"), media_type="application/javascript")
        return Response("", status_code=404)

    @app.get("/api/plugins/{plugin_id}/settings.html")
    def plugin_settings_html(plugin_id: str):
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                settings = p["_manifest"].get("settings", {})
                settings_file = p["_dir"] / (settings.get("html", "settings.html") if isinstance(settings, dict) else "settings.html")
                if settings_file.exists():
                    return HTMLResponse(settings_file.read_text())
        return HTMLResponse("", status_code=404)
