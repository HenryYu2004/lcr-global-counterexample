"""Package audited sources and release documents from this repository only."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=REPOSITORY / 'dist/global_counterexample_lean_verified.zip')
    args = parser.parse_args()
    receipt = json.loads((ROOT / 'verification/receipt.json').read_text())
    if receipt['status'] != 'PASS':
        raise RuntimeError('A passing clean verification is required before packaging.')

    entries = []
    for filename, expected in receipt['source_sha256'].items():
        source = (ROOT / filename).resolve()
        source.relative_to(ROOT)
        if hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'Audited source changed: {filename}')
        entries.append(source)
    for filename, expected in receipt.get('tooling_sha256', {}).items():
        if hashlib.sha256((ROOT / filename).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f'Audited verification tooling changed: {filename}')

    entries += [ROOT / name for name in [
        'README.md', 'lean-toolchain', 'lakefile.toml', 'run_lean.py', 'verify.py',
        'make_bundle.py', 'verification/build.log', 'verification/receipt.json',
    ]]
    entries += [REPOSITORY / 'paper' / name for name in [
        'global_counterexample.pdf', 'global_counterexample.tex', 'README_global.md',
    ]]
    entries += [REPOSITORY / 'auxiliary_exact_arithmetic' / name for name in [
        'exact_interval_certificate.py', 'exact_gaussian_alias.py',
    ]]
    entries += [REPOSITORY / 'numerical_checks' / name for name in [
        'check_probit_counterexample.py', 'probit_numerical_check.json',
        'check_probit_quadrature.py', 'probit_quadrature_check.json',
    ]]
    entries += [REPOSITORY / name for name in [
        'README.md', 'AI_PROVENANCE.md', '.gitignore', '.github/workflows/lean.yml',
    ]]
    if (ROOT / 'lake-manifest.json').is_file():
        entries.append(ROOT / 'lake-manifest.json')

    target = args.output.expanduser().resolve()
    if target in [source.resolve() for source in entries]:
        raise RuntimeError('The archive cannot overwrite a release input.')
    target.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED) as bundle:
        for source in entries:
            bundle.write(source, source.relative_to(REPOSITORY).as_posix())
        bundle.writestr('README.txt',
            'The paper is in paper/. The completed Lean proof, reproducibility guide,\n'
            'clean-build log and axiom-audit receipt are in formal_global/.\n'
            'Start with README.md and formal_global/LCR/Main.lean.\n'
            'The auxiliary exact-arithmetic Python checks are not trusted premises\n'
            'of the final Lean theorems. numerical_checks/ contains separate\n'
            'high-precision diagnostics, not formal certificates. Mathlib binaries\n'
            'are not bundled. See AI_PROVENANCE.md for the AI contribution statement.\n')
    with zipfile.ZipFile(target) as bundle:
        problem = bundle.testzip()
        if problem:
            raise RuntimeError(f'Archive integrity failure: {problem}')
    print(f'Created {target} ({len(entries) + 1} files, {target.stat().st_size} bytes)')


if __name__ == '__main__':
    main()
