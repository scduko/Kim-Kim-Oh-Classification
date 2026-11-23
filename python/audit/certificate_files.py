"""Paths to the records of Certificates 4.1–4.3 and the pinned Lean generator's inputs."""
from pathlib import Path
from shutil import copyfile

AUDIT = Path(__file__).resolve().parent
CERTIFICATES = AUDIT.parent / "certificates"
LOCAL_STEPS = CERTIFICATES / "local_progression_steps.tsv"
BLOCK_PAIRS = CERTIFICATES / "binary_block_pairs.json.gz"
LAST_COLUMN_BOUNDS = CERTIFICATES / "last_column_bounds.json.gz"
GRAM_MATRICES = CERTIFICATES / "bounded_gram_matrices.txt.gz"
REPRESENTATION_WITNESSES = CERTIFICATES / "representation_witnesses.jsonl.gz"

_LEAN_INPUTS = {
    LAST_COLUMN_BOUNDS: AUDIT / "coverage.json.gz",
    REPRESENTATION_WITNESSES: AUDIT / "witnesses.jsonl.gz",
}


def refresh_lean_input(output):
    """Refresh the historical filename only when regenerating the corresponding default record."""
    source = output.resolve()
    if source in _LEAN_INPUTS:
        copyfile(source, _LEAN_INPUTS[source])
