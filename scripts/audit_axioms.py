"""Fail closed unless all expected Lean axiom reports use only the allowlist.

Usage: lake env lean Audit.lean | python3 scripts/audit_axioms.py
The caller must also check the Lean command's exit status (e.g. bash pipefail).
"""

import re
import sys


EXPECTED = {
    "JSP690.binaryColorings_complete",
    "JSP690.binary_obstruction",
    "JSP690.edge_deletion_certificates",
    "JSP690.vertex_deletion_certificates",
    "JSP690.liGraph_chromatic_number",
    "JSP690.liGraph_all_proper_subgraphs",
    "JSP690.liGraph_deleted_edge_chromatic_two",
    "JSP690.liGraph_deleted_vertex_chromatic_two",
    "JSP690.jsp000690",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    text = sys.stdin.read()
    print(text, end="")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    seen = set()
    for name, raw in reports:
        if name in seen:
            raise SystemExit(f"Duplicate report: {name}")
        seen.add(name)
        unexpected = {a.strip() for a in raw.split(",") if a.strip()} - ALLOWED
        if unexpected:
            raise SystemExit(f"UNAPPROVED AXIOMS in {name}: {sorted(unexpected)}")
    if seen != EXPECTED:
        raise SystemExit(f"Missing/extra axiom reports: {sorted(seen ^ EXPECTED)}")
    if re.search(r"\berror:|\buses 'sorry'", text):
        raise SystemExit("Lean reported an error or placeholder")
    print("AXIOM AUDIT PASS: all 9 expected declarations use only the allowlist.")


if __name__ == "__main__":
    main()
