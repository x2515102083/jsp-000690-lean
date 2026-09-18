"""Fail closed unless every named root reports only the standard Lean axioms."""
from __future__ import annotations
import re
import sys
from pathlib import Path

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
TARGETS = (
    'JSP690.binaryColorings_complete',
    'JSP690.jsp000690',
    'JSP690Transversal.star_card_le_three',
    'JSP690Transversal.pair_system_card_le_six',
    'JSP690Transversal.deletion_witness',
    'JSP690Transversal.degree_le_six',
    'JSP690Transversal.critical_nonempty',
    'JSP690Transversal.exists_positive_degree_le_six',
    'JSP690Transversal.no_transversal_critical_minimum_degree_seven',
    'JSP690Transversal.deletion_transversal_exactly_two',
    'JSP690Transversal.complete_five_properties',
    'JSP690Complete.complete_resolution',
)
PATTERN = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.MULTILINE)


def audit(text: str) -> dict[str, list[str]]:
    matches = PATTERN.findall(text)
    if len(matches) != len(TARGETS):
        raise ValueError(f'Expected {len(TARGETS)} reports; found {len(matches)}')
    result: dict[str, list[str]] = {}
    for name, raw in matches:
        if name not in TARGETS or name in result:
            raise ValueError(f'Unexpected or repeated target: {name}')
        axioms = [a.strip() for a in raw.split(',') if a.strip()]
        if len(set(axioms)) != len(axioms):
            raise ValueError(f'Repeated axiom in {name}')
        unknown = set(axioms) - ALLOWED
        if unknown:
            raise ValueError(f'Unapproved axioms in {name}: {sorted(unknown)}')
        result[name] = sorted(axioms)
    if set(result) != set(TARGETS):
        raise ValueError('Missing audited root')
    return result


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python scripts/audit_axioms.py AXIOM_LOG')
    result = audit(Path(sys.argv[1]).read_text(encoding='utf-8'))
    print(f'AXIOM_AUDIT_PASS {len(result)} exact roots; standard allowlist only')

if __name__ == '__main__':
    main()
