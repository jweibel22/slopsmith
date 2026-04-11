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

    print(f"[Plugin] Installing requirements for '{plugin_id}'...")
    try:
        result = subprocess.run(
            [sys.executable, "-m", "pip", "install",
             "--target", pip_target,
             "--quiet",
             "-r", str(req_file)],
            capture_output=True, text=True, timeout=120,
        )
        if result.returncode == 0:
            marker.write_text(req_hash)
            print(f"[Plugin] Requirements installed for '{plugin_id}'")
            return True
        else:
            print(f"[Plugin] Failed to install requirements for '{plugin_id}': {result.stderr[:300]}")
            return False
    except Exception as e:
        print(f"[Plugin] Error installing requirements for '{plugin_id}': {e}")
        return False


def load_plugins(app: FastAPI, context: dict):
    """Discover and load all plugins from the plugins/ directory."""
    if not PLUGINS_DIR.is_dir():
        return

    # Add persistent pip target to sys.path
    pip_target = str(_PIP_TARGET)
    if _PIP_TARGET.exists() and pip_target not in sys.path:
        sys.path.insert(0, pip_target)

    for plugin_dir in sorted(PLUGINS_DIR.iterdir()):
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

    @app.get("/api/plugins/{plugin_id}/screen.html")
    def plugin_screen_html(plugin_id: str):
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                screen_file = p["_dir"] / p["_manifest"].get("screen", "screen.html")
                if screen_file.exists():
                    return HTMLResponse(screen_file.read_text())
        return HTMLResponse("", status_code=404)

    @app.get("/api/plugins/{plugin_id}/screen.js")
    def plugin_screen_js(plugin_id: str):
        for p in LOADED_PLUGINS:
            if p["id"] == plugin_id:
                script_file = p["_dir"] / p["_manifest"].get("script", "screen.js")
                if script_file.exists():
                    return Response(script_file.read_text(), media_type="application/javascript")
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
