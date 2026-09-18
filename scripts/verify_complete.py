"""Rebuild both interpretations, audit every local theorem, and replay modules.
This is contributor-run verification, not an independent kernel implementation.
SPDX-License-Identifier: MIT
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCES = {'JSP690.lean': 'JSP690', 'Transversal.lean': 'JSP690Transversal',
           'Complete690.lean': 'JSP690Complete'}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REQUIRED = {'JSP690.jsp000690', 'JSP690Transversal.pair_card_le_six',
            'JSP690Transversal.degree_le_six', 'JSP690Transversal.no_minimum_degree_seven',
            'JSP690Transversal.degree_bound_sharp', 'JSP690Complete.erdos834_both',
            'JSP690Complete.every_transversal_degree_le_six'}
PINS = {'mathlib':'5ed2965256430c3649e86755f9576b54eca72435',
        'plausible':'118aa17ee84656b8bd727fef7c458ee8c833385c',
        'LeanSearchClient':'ddf04cf3949fa556442341e87d47f9f6e6074707',
        'importGraph':'e928b72544873815af278d38681b31c0293588e3',
        'proofwidgets':'106ff4fafc74ef4ac99d81dbf3ab399118f497a5',
        'aesop':'355695d523e41d0554926416cba2a2b3544fbbc9',
        'Qq':'6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259',
        'batteries':'f2effa3d803fda822b1f97b806c47cf2adfbcbc2',
        'Cli':'e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204'}

def code_only(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j == -1 else j
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)

def scan(text: str) -> str:
    code = code_only(text)
    if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b', code):
        raise ValueError('Forbidden proof or trust-expanding construct')
    return code

def parse_axioms(text: str, targets: set[str]) -> dict[str, list[str]]:
    found = {}
    for line in text.splitlines():
        stripped = line.strip()
        m = re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]", stripped)
        no_axioms = re.fullmatch(r"'([^']+)' does not depend on any axioms", stripped)
        if m:
            name = m[1]
            raw_axioms = m[2]
        elif no_axioms:
            name = no_axioms[1]
            raw_axioms = ''
        else:
            if line.strip():
                raise ValueError('Unexpected audit output: ' + line[:150])
            continue
        if name not in targets or name in found:
            raise ValueError('Unexpected or duplicate theorem report: ' + name)
        axioms = [x.strip() for x in raw_axioms.split(',') if x.strip()]
        if not set(axioms) <= ALLOWED:
            raise ValueError('Unapproved axiom dependency: ' + name)
        found[name] = axioms
    if set(found) != targets:
        raise ValueError('Missing theorem reports: ' + ', '.join(sorted(targets - set(found))))
    return found

def main() -> None:
    os.chdir(ROOT)
    out = ROOT / 'evidence-complete'
    out.mkdir(exist_ok=True)
    started = time.time()
    summary = {'status':'running', 'independent_human_review':False,
               'independent_kernel_implementation':False, 'dependency_source_rebuild':False}
    def run(args: list[str], filename: str, timeout: int = 900) -> str:
        print('+ ' + ' '.join(args), flush=True)
        p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           encoding='utf-8', errors='replace', timeout=timeout)
        (out / filename).write_text(p.stdout, encoding='utf-8')
        print(p.stdout[-16000:], flush=True)
        if p.returncode:
            raise RuntimeError(f'{args[0]} exited {p.returncode}: {filename}')
        return p.stdout
    try:
        if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.0':
            raise ValueError('Wrong toolchain pin')
        version = run(['lake','env','lean','--version'], 'version.log')
        if 'version 4.34.0,' not in version or '293d5d0c0c3f3dded4688b3ccd6a33939ac5102b' not in version:
            raise ValueError('Unexpected compiler version')
        lock = (ROOT / 'lake-manifest.json').read_bytes()
        packages = json.loads(lock)['packages']
        if {p['name']:p['rev'] for p in packages} != PINS or len(packages) != len(PINS):
            raise ValueError('Dependency lock does not match exact revision allowlist')
        for name, sha in PINS.items():
            actual = subprocess.check_output(['git','-C',str(ROOT/'.lake/packages'/name),
                                              'rev-parse','HEAD'], text=True).strip()
            if actual != sha:
                raise ValueError('Wrong dependency checkout: ' + name)
        targets = set()
        hashes = {}
        for filename, namespace in SOURCES.items():
            raw = (ROOT/filename).read_bytes()
            hashes[filename] = hashlib.sha256(raw).hexdigest()
            code = scan(raw.decode('utf-8'))
            names = re.findall(r'^\s*(?:theorem|lemma)\s+([A-Za-z0-9_]+)', code, re.M)
            if not names:
                raise ValueError('No theorem declarations in ' + filename)
            targets.update(namespace+'.'+n for n in names)
        if not REQUIRED <= targets:
            raise ValueError('Required roots missing from source inventory')
        run(['lake','build'], 'build.log')
        for filename in SOURCES:
            run(['lake','env','lean','-DwarningAsError=true',filename], filename+'.log')
        audit = 'import Complete690\n\n' + '\n'.join('#print axioms '+t for t in sorted(targets)) + '\n'
        (ROOT/'AuditGenerated.lean').write_text(audit, encoding='utf-8')
        report = run(['lake','env','lean','-DwarningAsError=true','AuditGenerated.lean'], 'axioms.log')
        summary['axioms'] = parse_axioms(report, targets)
        statements = 'import Complete690\nset_option pp.universes true\n' + '\n'.join(
            '#print '+n for n in ['JSP690.SimpleThreeUniform','JSP690.Proper',
            'JSP690.ChromaticCriticalThree','JSP690.AllProperSubgraphsTwoColorable',
            'JSP690Transversal.Hits','JSP690Transversal.Covers','JSP690Transversal.TauExactly',
            'JSP690Transversal.TauCriticalThree']) + '\n' + '\n'.join('#check '+n for n in sorted(REQUIRED))+'\n'
        (ROOT/'StatementAudit.lean').write_text(statements, encoding='utf-8')
        run(['lake','env','lean','-DwarningAsError=true','StatementAudit.lean'], 'statements.log')
        for module in ('JSP690','Transversal','Complete690'):
            run(['lake','env','leanchecker','--verbose',module], 'replay-'+module+'.log')
        run([sys.executable,'scripts/crosscheck.py'], 'chromatic-crosscheck.log')
        run([sys.executable,'scripts/crosscheck_transversal.py'], 'transversal-crosscheck.log')
        run([sys.executable,'-m','unittest','discover','-s','scripts','-p','test_*.py','-v'], 'tests.log')
        if (ROOT/'lake-manifest.json').read_bytes() != lock:
            raise ValueError('Dependency lockfile changed during verification')
        for filename, digest in hashes.items():
            if hashlib.sha256((ROOT/filename).read_bytes()).hexdigest() != digest:
                raise ValueError('Source changed during verification')
        summary.update(status='pass', source_sha256=hashes, theorem_count=len(targets),
                       dependency_revisions=PINS, manifest_sha256=hashlib.sha256(lock).hexdigest(),
                       compiler=version.strip(), kernel_replay='same Lean kernel; imported dependencies reused')
    except Exception as exc:
        summary.update(status='fail', error=str(exc))
        raise
    finally:
        summary['elapsed_seconds'] = round(time.time()-started, 3)
        (out/'verification.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
        print('Complete verification: '+summary['status'],flush=True)

if __name__ == '__main__':
    main()
