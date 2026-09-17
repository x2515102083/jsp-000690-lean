"""Regression tests ensure the axiom-report parser fails closed."""

import subprocess
import sys
import unittest
from pathlib import Path

from audit_axioms import EXPECTED


def valid_report():
    return "\n".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for name in sorted(EXPECTED)
    ) + "\n"


def accepted(text):
    result = subprocess.run(
        [sys.executable, str(Path(__file__).with_name("audit_axioms.py"))],
        input=text, text=True, capture_output=True, check=False,
    )
    return result.returncode == 0


class AxiomAuditTests(unittest.TestCase):
    def test_standard_axioms_accepted(self):
        self.assertTrue(accepted(valid_report()))

    def test_placeholder_rejected(self):
        self.assertFalse(accepted(valid_report().replace("propext", "sorryAx", 1)))

    def test_native_trust_rejected(self):
        self.assertFalse(accepted(valid_report().replace("propext", "Lean.ofReduceBool", 1)))

    def test_custom_axiom_rejected(self):
        self.assertFalse(accepted(valid_report().replace("propext", "unproved_hypothesis", 1)))

    def test_missing_output_rejected(self):
        self.assertFalse(accepted(""))
        self.assertFalse(accepted("\n".join(valid_report().splitlines()[1:])))

    def test_duplicate_rejected(self):
        self.assertFalse(accepted(valid_report() + valid_report().splitlines()[0]))

    def test_error_rejected(self):
        self.assertFalse(accepted(valid_report() + "\nAudit.lean:1: error: failed"))


if __name__ == "__main__":
    unittest.main()
