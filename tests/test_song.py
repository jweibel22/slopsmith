"""Tests for lib/song.py wire-format serialization (pure, no fixtures)."""

import pytest

from song import (
    Anchor,
    Arrangement,
    Chord,
    ChordTemplate,
    HandShape,
    Note,
    arrangement_from_wire,
    arrangement_to_wire,
    chord_from_wire,
    chord_to_wire,
    note_from_wire,
    note_to_wire,
)


# ── Note round-trip ──────────────────────────────────────────────────────────

def test_note_minimal_round_trip():
    n = Note(time=1.0, string=2, fret=5)
    assert note_from_wire(note_to_wire(n)) == n


def test_note_with_every_technique_round_trip():
    n = Note(
        time=0.5, string=0, fret=3,
        sustain=0.25,
        slide_to=7,
        slide_unpitch_to=9,
        bend=1.0,
        hammer_on=True, pull_off=True,
        harmonic=True, harmonic_pinch=True,
        palm_mute=True, mute=True,
        tremolo=True, accent=True,
        tap=True,
    )
    assert note_from_wire(note_to_wire(n)) == n


def test_note_link_next_is_not_round_tripped():
    """link_next is deliberately omitted from the wire format.

    Acknowledged behavior, not a regression — chord linking is derived elsewhere.
    Pinning this so nobody "fixes" it accidentally and breaks downstream assumptions.
    """
    n = Note(time=0.0, string=0, fret=0, link_next=True)
    assert note_to_wire(n) == {
        "t": 0.0, "s": 0, "f": 0, "sus": 0.0,
        "sl": -1, "slu": -1, "bn": 0,
        "ho": False, "po": False,
        "hm": False, "hp": False,
        "pm": False, "mt": False,
        "tr": False, "ac": False, "tp": False,
    }
    assert note_from_wire(note_to_wire(n)).link_next is False


def test_note_time_rounded_to_three_decimals():
    n = Note(time=1.23456789, string=0, fret=0)
    assert note_to_wire(n)["t"] == 1.235


def test_note_bend_zero_serializes_as_integer_zero():
    # note_to_wire uses `round(bend, 1) if bend else 0` — the else branch returns int 0.
    # from_wire then float()s it back. Pin this quirk so a refactor doesn't surprise callers.
    wire = note_to_wire(Note(time=0.0, string=0, fret=0, bend=0.0))
    assert wire["bn"] == 0
    assert isinstance(wire["bn"], int)


def test_note_bend_nonzero_rounded_to_one_decimal():
    n = Note(time=0.0, string=0, fret=0, bend=1.75)
    assert note_to_wire(n)["bn"] == 1.8


# ── Chord round-trip ─────────────────────────────────────────────────────────

def test_chord_with_multiple_notes_round_trip():
    c = Chord(
        time=2.0,
        chord_id=5,
        high_density=False,
        notes=[
            Note(time=2.0, string=0, fret=3),
            Note(time=2.0, string=1, fret=5),
            Note(time=2.0, string=2, fret=5),
        ],
    )
    assert chord_from_wire(chord_to_wire(c)) == c


def test_chord_high_density_round_trip():
    c = Chord(
        time=1.5, chord_id=2, high_density=True,
        notes=[Note(time=1.5, string=0, fret=0)],
    )
    assert chord_from_wire(chord_to_wire(c)) == c


def test_chord_notes_inherit_chord_time_on_deserialization():
    """chord_note_to_wire strips each note's time; chord_from_wire replays the chord time.

    So notes constructed with mismatched times are normalized by the round-trip.
    """
    c = Chord(
        time=3.0, chord_id=0,
        notes=[
            Note(time=99.0, string=0, fret=0),  # will be normalized to 3.0
            Note(time=42.5, string=1, fret=1),  # will be normalized to 3.0
        ],
    )
    result = chord_from_wire(chord_to_wire(c))
    assert all(n.time == 3.0 for n in result.notes)


# ── Arrangement round-trip ───────────────────────────────────────────────────

def test_arrangement_empty_round_trip():
    arr = Arrangement(name="Lead")
    assert arrangement_from_wire(arrangement_to_wire(arr)) == arr


def test_arrangement_full_round_trip():
    arr = Arrangement(
        name="Rhythm",
        tuning=[-2, 0, 0, 0, 0, 0],
        capo=2,
        notes=[
            Note(time=1.0, string=0, fret=3, palm_mute=True),
            Note(time=1.5, string=1, fret=5, hammer_on=True),
        ],
        chords=[
            Chord(
                time=2.0, chord_id=1, high_density=True,
                notes=[
                    Note(time=2.0, string=0, fret=0),
                    Note(time=2.0, string=1, fret=2),
                ],
            ),
        ],
        anchors=[
            Anchor(time=0.0, fret=1, width=4),
            Anchor(time=10.0, fret=7, width=5),
        ],
        hand_shapes=[
            HandShape(chord_id=1, start_time=2.0, end_time=2.5),
        ],
        chord_templates=[
            ChordTemplate(
                name="Em",
                fingers=[-1, -1, 2, 3, -1, -1],
                frets=[0, 2, 2, 0, 0, 0],
            ),
        ],
    )
    assert arrangement_from_wire(arrangement_to_wire(arr)) == arr


def test_arrangement_default_tuning_is_six_zeros():
    arr = Arrangement(name="Bass")
    assert arr.tuning == [0, 0, 0, 0, 0, 0]


def test_arrangement_from_wire_missing_fields_use_defaults():
    # Minimal wire dict — every list field defaults to empty, capo to 0,
    # tuning to six zeros.
    arr = arrangement_from_wire({"name": "Lead"})
    assert arr.name == "Lead"
    assert arr.tuning == [0, 0, 0, 0, 0, 0]
    assert arr.capo == 0
    assert arr.notes == []
    assert arr.chords == []
    assert arr.anchors == []
    assert arr.hand_shapes == []
    assert arr.chord_templates == []


# ── Dataclass defaults ───────────────────────────────────────────────────────

def test_note_defaults():
    n = Note(time=0.0, string=0, fret=0)
    assert n.sustain == 0.0
    assert n.slide_to == -1
    assert n.slide_unpitch_to == -1
    assert n.bend == 0.0
    assert n.hammer_on is False
    assert n.pull_off is False
    assert n.harmonic is False
    assert n.harmonic_pinch is False
    assert n.palm_mute is False
    assert n.mute is False
    assert n.tremolo is False
    assert n.accent is False
    assert n.link_next is False
    assert n.tap is False


def test_anchor_default_width_is_four():
    a = Anchor(time=0.0, fret=1)
    assert a.width == 4


def test_chord_default_high_density_is_false():
    c = Chord(time=0.0, chord_id=0)
    assert c.high_density is False
    assert c.notes == []
