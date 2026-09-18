"""Regression tests for rejecting incomplete or unsafe audit records."""
import unittest
from audit_axioms import TARGETS, audit


def good() -> str:
    return '\n'.join(f"'{x}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" for x in TARGETS)

class AuditTests(unittest.TestCase):
    def test_good_multiline(self):
        self.assertEqual(len(audit(good())), 12)
    def test_standard_subset(self):
        self.assertEqual(len(audit(good().replace('propext,\n Classical.choice,\n Quot.sound','propext'))),12)
    def test_missing(self):
        with self.assertRaises(ValueError): audit(good().replace(TARGETS[0], 'wrong'))
    def test_truncated(self):
        with self.assertRaises(ValueError): audit(good()[:-1])
    def test_duplicate(self):
        with self.assertRaises(ValueError): audit(good()+f"\n'{TARGETS[0]}' depends on axioms: []")
    def test_sorry(self):
        with self.assertRaises(ValueError): audit(good().replace('Quot.sound', 'sorryAx', 1))
    def test_native(self):
        with self.assertRaises(ValueError): audit(good().replace('Quot.sound','Lean.ofReduceBool',1))
    def test_custom(self):
        with self.assertRaises(ValueError): audit(good().replace('Quot.sound','Hidden.unproved',1))
    def test_empty_log(self):
        with self.assertRaises(ValueError): audit('')
    def test_repeated_axiom(self):
        with self.assertRaises(ValueError): audit(good().replace('Quot.sound','propext',1))

if __name__ == '__main__': unittest.main()
