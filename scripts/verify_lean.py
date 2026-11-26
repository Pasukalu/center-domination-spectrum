"""Run Lake, check every printed axiom closure, and replay the complete import graph."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
MODULES = ["CenterDomination", "CenterCounts", "CenterFan", "CenterRealization"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(command, logfile):
    print("Running", " ".join(command), flush=True)
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = result.stdout.decode("utf-8", errors="replace")
    (OUT / logfile).write_text(text, encoding="utf-8")
    print(text, flush=True)
    result.check_returncode()
    return text


def main():
    OUT.mkdir(exist_ok=True)
    names = []
    for module in MODULES:
        src = (ROOT / (module + ".lean")).read_text(encoding="utf-8")
        if re.search(r"\b(?:sorry|admit|sorryAx|native_decide|axiom)\b", src):
            raise ValueError("Unreviewed proof primitive in " + module)
        names.extend(re.findall(r"^#print axioms (\S+)$", src, re.M))
    if not names or len(names) != len(set(names)):
        raise ValueError("The audit declaration list is empty or contains duplicates")
    run(["lake", "build"], "build.log")
    temporary = tempfile.NamedTemporaryFile(prefix="Audit_", suffix=".lean", dir=ROOT, delete=False)
    path = Path(temporary.name)
    try:
        with temporary:
            text = "import CenterRealization\n" + "\n".join("#print axioms " + n for n in names)
            temporary.write((text + "\n").encode("utf-8"))
        output = run(["lake", "env", "lean", str(path)], "axioms.log")
    finally:
        path.unlink(missing_ok=True)
    seen = {}
    for name, dependencies in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        seen[name] = {a.strip() for a in dependencies.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        seen[name] = set()
    for name in names:
        if name not in seen or seen[name] - ALLOWED:
            raise ValueError(f"Missing declaration or disallowed axiom for {name}: {seen.get(name)}")
    run(["lake", "env", "leanchecker", "--fresh", "CenterRealization"], "kernel.log")
    print(f"Checked {len(names)} axiom closures and replayed the module from a fresh environment.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))

