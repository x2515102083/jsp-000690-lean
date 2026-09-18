"""Reproduce the complete two-reading proof, with explicit fail-closed checks.

Run bootstrap.py and fetch the pinned Mathlib cache first; see README.md.
No external solver output is used as a Lean proof premise.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

from audit_axioms import audit

ROOT = Path(__file__).resolve().parents[1]
MODULES = ('JSP690', 'Transversal', 'Complete')
PINNED = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
OLD_SOURCE_HASH = '3c2534ffabec4a5775ea1b36a04a96d5deddc04389775b8e1309f47e2dc7642d'


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='verification-output')
    args = parser.parse_args()
    out = Path(args.output).resolve()
    out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('PYTHONOPTIMIZE', None)
    env['LEAN_NUM_THREADS'] = '1'
    report: dict = {
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'github_sha': env.get('GITHUB_SHA'),
        'github_run_id': env.get('GITHUB_RUN_ID'),
        'verification_scope': 'Fresh project elaboration and per-module Lean kernel replay; imported pinned Mathlib compiled cache is trusted. Not fresh replay of all imports or independent human/kernel review.',
        'steps': [], 'success': False,
    }
    locks = {p: digest(ROOT / p) for p in PINNED}

    def run(name: str, command: list[str], timeout: int = 900) -> str:
        print(f'RUN {name}: {command}', flush=True)
        start = time.monotonic()
        log = out / f'{name}.log'
        with log.open('w', encoding='utf-8') as stream:
            try:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=timeout, check=False)
                code = result.returncode
            except subprocess.TimeoutExpired:
                stream.write('\nVERIFICATION TIMEOUT\n')
                code = 124
        report['steps'].append({'name': name, 'command': command, 'exit_code': code,
                                'seconds': round(time.monotonic() - start, 3)})
        text = log.read_text(encoding='utf-8')
        print(text, end='' if text.endswith('\n') else '\n', flush=True)
        if code:
            raise RuntimeError(f'{name} failed: exit {code}; see {log}')
        return text

    try:
        if digest(ROOT / 'JSP690.lean') != OLD_SOURCE_HASH:
            raise RuntimeError('The original chromatic source was changed')
        expected = json.loads((ROOT / 'source-hashes.json').read_text(encoding='utf-8'))
        for path, sha in expected.items():
            if digest(ROOT / path) != sha:
                raise RuntimeError(f'Source hash mismatch: {path}')
        for module in (*MODULES, 'Audit'):
            text = (ROOT / f'{module}.lean').read_text(encoding='utf-8')
            if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text):
                raise RuntimeError(f'Forbidden proof token in {module}')
        run('dependency-pins-before', [sys.executable, 'bootstrap.py'])
        report['lean_version'] = run('lean-version', ['lake', 'env', 'lean', '--version']).strip()
        if '4.32.1' not in report['lean_version']:
            raise RuntimeError('Unexpected Lean version')
        run('build', ['lake', 'build'])
        for module in MODULES:
            run('elaborate-' + module,
                ['lake', 'env', 'lean', '-DwarningAsError=true', '-o',
                 f'.lake/build/lib/lean/{module}.olean', f'{module}.lean'])
        axioms = run('axioms', ['lake', 'env', 'lean', '-DwarningAsError=true', 'Audit.lean'])
        report['axioms'] = audit(axioms)
        print('AXIOM_AUDIT_PASS 12 exact roots; standard allowlist only', flush=True)
        run('kernel-replay', ['lake', 'env', 'leanchecker', '--verbose', *MODULES])
        run('audit-regressions', [sys.executable, 'scripts/test_audit.py'])
        run('chromatic-crosscheck', [sys.executable, 'scripts/crosscheck.py'])
        run('transversal-crosscheck', [sys.executable, 'scripts/transversal_crosscheck.py'])
        run('dependency-pins-after', [sys.executable, 'bootstrap.py'])
        if locks != {p: digest(ROOT / p) for p in PINNED}:
            raise RuntimeError('Toolchain or dependency lockfiles changed during verification')
        if any(digest(ROOT / p) != sha for p, sha in expected.items()):
            raise RuntimeError('Audited sources changed during verification')
        report['source_sha256'] = expected
        report['success'] = True
        print('COMPLETE_TWO_READING_VERIFICATION_PASS', flush=True)
    except Exception as exc:
        report['error'] = str(exc)
        raise
    finally:
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        (out / 'summary.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')

if __name__ == '__main__':
    main()
