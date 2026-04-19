"""Tests for lib/tunings.py: semitone-offset → human-readable tuning name."""

import pytest

from tunings import tuning_name


# ── Standard tunings (all six strings share the same offset) ─────────────────

STANDARD_CASES = [
    ([0, 0, 0, 0, 0, 0], "E Standard"),
    ([-1, -1, -1, -1, -1, -1], "Eb Standard"),
    ([-2, -2, -2, -2, -2, -2], "D Standard"),
    ([-3, -3, -3, -3, -3, -3], "C# Standard"),
    ([-4, -4, -4, -4, -4, -4], "C Standard"),
    ([-5, -5, -5, -5, -5, -5], "B Standard"),
    ([-6, -6, -6, -6, -6, -6], "Bb Standard"),
    ([-7, -7, -7, -7, -7, -7], "A Standard"),
    ([1, 1, 1, 1, 1, 1], "F Standard"),
    ([2, 2, 2, 2, 2, 2], "F# Standard"),
]


@pytest.mark.parametrize("offsets,expected", STANDARD_CASES)
def test_standard_tunings(offsets, expected):
    assert tuning_name(offsets) == expected


# ── Drop tunings (low string 2 semitones below the rest) ─────────────────────
# The auto-generator handles these; the explicit "Drop D" / "Drop C" entries in
# the named-tunings dict are effectively dead code because the auto-generator
# fires first and produces the same string.

DROP_CASES = [
    ([-2, 0, 0, 0, 0, 0], "Drop D"),
    ([-4, -2, -2, -2, -2, -2], "Drop C"),
    ([-3, -1, -1, -1, -1, -1], "Drop C#"),
    ([-5, -3, -3, -3, -3, -3], "Drop B"),
    ([-7, -5, -5, -5, -5, -5], "Drop A"),
    ([-8, -6, -6, -6, -6, -6], "Drop Ab"),
]


@pytest.mark.parametrize("offsets,expected", DROP_CASES)
def test_drop_tunings_auto_generated(offsets, expected):
    assert tuning_name(offsets) == expected


# ── Named tunings (non-drop patterns the auto-generator doesn't catch) ───────

NAMED_CASES = [
    ([-2, -2, 0, 0, 0, 0], "Double Drop D"),
    ([0, 0, 0, -1, 0, 0], "Open G"),
    ([-2, -2, 0, 0, -2, -2], "Open D"),
    ([-2, 0, 0, 0, -2, 0], "DADGAD"),
    ([0, 2, 2, 1, 0, 0], "Open E"),
    ([-2, 0, 0, 2, 3, 2], "Open D (alt)"),
]


@pytest.mark.parametrize("offsets,expected", NAMED_CASES)
def test_named_tunings(offsets, expected):
    assert tuning_name(offsets) == expected


# ── Fallback: unrecognized offsets stringify as space-joined numbers ─────────

def test_fallback_unrecognized_offsets():
    assert tuning_name([-3, -1, 0, 1, 2, 3]) == "-3 -1 0 1 2 3"


def test_fallback_with_seven_strings():
    # Seven-string guitar standard offsets — not a recognized pattern, so falls through.
    # (The standard dict only matches when len >= 6 AND all offsets identical; adding
    # a seventh offset here makes the "all identical" check still true, so this would
    # match E Standard if the seventh value were 0. Use a non-standard seven-string
    # offset array instead.)
    assert tuning_name([-5, 0, 0, 0, 0, 0, 0]) == "-5 0 0 0 0 0 0"


# ── Edge cases ───────────────────────────────────────────────────────────────

def test_empty_list_falls_through_to_fallback():
    assert tuning_name([]) == ""


def test_too_short_list_falls_through_to_fallback():
    # Fewer than 6 offsets — neither standard, drop, nor named match; fallback stringifies.
    assert tuning_name([-2, 0, 0]) == "-2 0 0"


def test_standard_dict_takes_precedence_over_numeric_fallback():
    # A list of 6 zeros could theoretically also hit the named-tunings tuple lookup
    # (if (0,0,0,0,0,0) were in there), but the standard-tuning branch runs first.
    # This test pins the priority.
    assert tuning_name([0, 0, 0, 0, 0, 0]) == "E Standard"


def test_drop_pattern_takes_precedence_over_named_dict():
    # [-2, 0, 0, 0, 0, 0] is in the named dict as "Drop D", but the drop-pattern
    # auto-generator fires first and produces the same string. The named dict entry
    # is effectively dead code for this case — this test documents the behavior.
    assert tuning_name([-2, 0, 0, 0, 0, 0]) == "Drop D"
