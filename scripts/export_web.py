"""Assemble the project into one input for the Lean web editor."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["CenterDomination", "CenterCounts", "CenterFan", "CenterRealization", "CenterObstruction"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    options = parser.parse_args()
    imports = {"import " + name for name in MODULES}
    chunks = []
    for name in MODULES:
        source = (ROOT / (name + ".lean")).read_text(encoding="utf-8")
        chunks.append("".join(line for line in source.splitlines(keepends=True)
                              if line.rstrip("\n") not in imports))
    options.output.write_bytes("\n".join(chunks).encode("utf-8"))


if __name__ == "__main__":
    main()

