import unittest
from verify_complete import scan, parse_axioms

class CompleteAuditTests(unittest.TestCase):
    def test_good_report(self):
        self.assertEqual(parse_axioms("'A.t' depends on axioms: [propext, Quot.sound]\n", {'A.t'}),
                         {'A.t':['propext','Quot.sound']})
    def test_no_axioms_report(self):
        self.assertEqual(parse_axioms("'A.t' does not depend on any axioms\n", {'A.t'}),
                         {'A.t': []})
    def test_empty_report(self):
        with self.assertRaises(ValueError): parse_axioms('', {'A.t'})
    def test_wrong_target(self):
        with self.assertRaises(ValueError): parse_axioms("'A.u' depends on axioms: []", {'A.t'})
    def test_duplicate(self):
        with self.assertRaises(ValueError): parse_axioms("'A.t' depends on axioms: []\n"*2, {'A.t'})
    def test_extra_output(self):
        with self.assertRaises(ValueError): parse_axioms("error: fail\n'A.t' depends on axioms: []", {'A.t'})
    def test_bad_axioms(self):
        for ax in ('sorryAx','Lean.ofReduceBool','NewAssumption'):
            with self.subTest(ax=ax), self.assertRaises(ValueError):
                parse_axioms("'A.t' depends on axioms: ["+ax+"]", {'A.t'})
    def test_missing_one(self):
        with self.assertRaises(ValueError): parse_axioms("'A.t' depends on axioms: []", {'A.t','A.u'})
    def test_forbidden_constructs(self):
        for word in ('sorry','admit','axiom','native_decide','unsafe','implemented_by','extern'):
            with self.subTest(word=word), self.assertRaises(ValueError): scan('theorem t : True := by '+word)
    def test_nested_comments(self):
        self.assertIn('theorem',scan('/- sorry /- admit -/ axiom -/\ntheorem t : True := by trivial'))
    def test_line_comments(self):
        self.assertIn('theorem',scan('-- sorry\ntheorem t : True := by trivial'))
    def test_unclosed_comment(self):
        with self.assertRaises(ValueError): scan('/- hidden')

if __name__ == '__main__': unittest.main()
