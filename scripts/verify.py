"""Run reproducible checks; fails immediately on any failed subprocess.

Use --lake with an explicit executable path when Lake is not on PATH.
--clean asks Lake to remove only this project's generated build artifacts.
"""

import argparse
import subprocess
import sys
from pathlib import Path


def run(command, **kwargs):
    print("RUN:", " ".join(map(str, command)), flush=True)
    return subprocess.run(command, check=True, **kwargs)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--clean", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    lake = args.lake
    if args.clean:
        run([lake, "clean"], cwd=root)
    run([lake, "build"], cwd=root)
    audit = run([lake, "env", "lean", "Audit.lean"], cwd=root,
                capture_output=True, text=True, encoding="utf-8")
    run([sys.executable, "scripts/audit_axioms.py"], cwd=root,
        input=audit.stdout + audit.stderr, text=True, encoding="utf-8")
    run([lake, "env", "leanchecker", "--verbose", "JSP690"], cwd=root)
    run([lake, "env", "leanchecker", "--fresh", "--verbose", "JSP690"], cwd=root)
    run([sys.executable, "scripts/crosscheck.py"], cwd=root)
    run([sys.executable, "-m", "unittest", "discover", "-s", "scripts",
         "-p", "test_*.py", "-v"], cwd=root)
    print("ALL VERIFICATION COMMANDS PASSED.")


if __name__ == "__main__":
    main()
