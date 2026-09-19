"""Clean rebuild and explicit axiom audit of the complete theorem dependency graph.

Only this project's generated build files are temporary. The prepared Mathlib
cache is read-only. The JSON receipt records source hashes, versions and the
audited axiom sets; it is a reproducibility aid, not a substitute for Lean.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import time

from run_lean import resolve_lean

ROOT = Path(__file__).resolve().parent
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib-project', type=Path, default=ROOT,
                        help='Lake project containing .lake/packages (default: this project).')
    parser.add_argument('--lean', type=Path,
                        help='Optional compiler override; normally resolved through elan/PATH.')
    parser.add_argument('--output', type=Path, default=ROOT / 'verification')
    args = parser.parse_args()
    args.mathlib_project = args.mathlib_project.expanduser().resolve()
    compiler = resolve_lean(args.lean)
    output = args.output.expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    # A failed rerun must not leave an old PASS looking like the current result.
    (output / 'receipt.json').write_text(json.dumps({
        'status': 'IN_PROGRESS',
        'started_at_utc': datetime.now(timezone.utc).isoformat(),
    }, indent=2) + '\n')
    if (ROOT / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.30.0':
        raise RuntimeError('The project lean-toolchain does not match the audited pin.')
    if f'rev = "{PIN}"' not in (ROOT / 'lakefile.toml').read_text():
        raise RuntimeError('The project Mathlib requirement does not match the audited pin.')
    mathlib = args.mathlib_project / '.lake/packages/mathlib'
    if not mathlib.is_dir():
        raise RuntimeError('Mathlib is missing. Run lake update and lake exe cache get '
                           'in formal_global, or pass --mathlib-project.')
    revision = subprocess.check_output(
        ['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != PIN:
        raise RuntimeError(f'Mathlib revision mismatch: {revision}')
    dirty = subprocess.check_output(
        ['git', '-C', str(mathlib), 'status', '--porcelain', '--untracked-files=no'],
        text=True).strip()
    if dirty:
        raise RuntimeError('Mathlib has tracked source modifications; audit stopped.')
    version = subprocess.check_output([compiler, '--version'], cwd=ROOT, text=True).strip()
    if not version.startswith('Lean (version 4.30.0,'):
        raise RuntimeError(f'Lean version mismatch: {version}')

    ordered, seen, visiting = [], set(), set()

    def visit(path):
        if path in seen:
            return
        if path in visiting:
            raise RuntimeError(f'Import cycle: {path}')
        visiting.add(path)
        source = (ROOT / path).read_text()
        for module in re.findall(r'^import\s+([A-Za-z0-9_.]+)', source, re.MULTILINE):
            if module == 'LCR' or module.startswith('LCR.'):
                visit(Path(module.replace('.', '/') + '.lean'))
        visiting.remove(path)
        seen.add(path)
        ordered.append(path)

    visit(Path('Audit.lean'))
    hashes = {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in ordered}
    tooling = ['run_lean.py', 'verify.py', 'lean-toolchain', 'lakefile.toml']
    tooling_hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in tooling}
    start = time.monotonic()
    records, log = [], []
    with tempfile.TemporaryDirectory(prefix='lcr-clean-lean-') as fresh:
        for index, path in enumerate(ordered, 1):
            print(f'[{index}/{len(ordered)}] Checking {path}', flush=True)
            tick = time.monotonic()
            result = subprocess.run([
                sys.executable, str(ROOT / 'run_lean.py'),
                '--mathlib-project', str(args.mathlib_project), '--lean', compiler,
                '--build-dir', fresh, str(path)
            ], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log.append(f'\n===== {path} =====\n{result.stdout}')
            records.append({'file': str(path), 'returncode': result.returncode,
                            'seconds': round(time.monotonic() - tick, 3)})
            if result.returncode:
                (output / 'build.log').write_text(''.join(log))
                print(result.stdout, flush=True)
                raise RuntimeError(f'Lean rejected {path}')
    combined = ''.join(log)
    (output / 'build.log').write_text(combined)
    if "declaration uses 'sorry'" in combined or 'sorryAx' in combined:
        raise RuntimeError('A placeholder proof appeared in the build/audit output.')
    audited = {}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", combined):
        axioms = {s.strip() for s in body.split(',') if s.strip()}
        if not axioms <= ALLOWED:
            raise RuntimeError(f'Unexpected axioms in {name}: {sorted(axioms - ALLOWED)}')
        audited[name] = sorted(axioms)
    required = {'LCR.global_probit_counterexample', 'LCR.not_injective_2LCR1_five',
                'LCR.not_injective_2LCR_five', 'LCR.not_injective_2LCR1_four',
                'LCR.not_injective_2LCR_four', 'LCR.correctedGaussianSeed_exact',
                'LCR.correctedGaussianSeed_error'}
    if len(audited) < 24 or not required <= audited.keys():
        raise RuntimeError('The expected final theorem audits were not all present.')
    for path in ordered:
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != hashes[str(path)]:
            raise RuntimeError(f'Source changed during the audit: {path}')
    for path, expected in tooling_hashes.items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'Verification tooling changed during the audit: {path}')
    receipt = {'status': 'PASS', 'clean_project_build': True, 'lean_trust_level': 0,
               'completed_at_utc': datetime.now(timezone.utc).isoformat(),
               'lean_version': version, 'mathlib_revision': revision,
               'seconds': round(time.monotonic() - start, 3), 'modules': records,
               'source_sha256': hashes, 'tooling_sha256': tooling_hashes,
               'audited_axioms': audited}
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'PASS: {len(ordered)} cleanly rebuilt modules; '
          f'{len(audited)} theorem dependency audits; only standard foundational axioms.', flush=True)
    print(f'Build log: {output / "build.log"}', flush=True)
    print(f'Receipt: {output / "receipt.json"}', flush=True)


if __name__ == '__main__':
    main()
