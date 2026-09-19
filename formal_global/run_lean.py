"""Compile project modules with kernel checking and isolated project outputs.

Dependencies default to this project's .lake/packages directory. An existing
Lake project's dependency cache can optionally be reused without modifying it.
"""
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def resolve_lean(override=None):
    """Resolve the compiler selected by lean-toolchain, without a local path."""
    if override is not None:
        # Do not resolve a shim's symlink: elan chooses its behavior by argv[0].
        return str(override.expanduser().absolute())
    elan = shutil.which('elan')
    if elan:
        result = subprocess.run([elan, 'which', 'lean'], cwd=ROOT,
                                text=True, capture_output=True)
        if result.returncode == 0:
            return result.stdout.strip()
    lean = shutil.which('lean')
    if lean:
        return lean
    raise RuntimeError('Lean was not found. Install elan and prepare the pinned '
                       'toolchain, or pass --lean /path/to/lean.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+')
    parser.add_argument('--mathlib-project', type=Path, default=ROOT,
                        help='Lake project containing .lake/packages (default: this project).')
    parser.add_argument('--lean', type=Path,
                        help='Optional compiler override; normally resolved through elan/PATH.')
    parser.add_argument('--build-dir', type=Path,
                        help='Separate project output directory, for example for a clean audit.')
    args = parser.parse_args()
    compiler = resolve_lean(args.lean)
    packages = args.mathlib_project.expanduser().resolve() / '.lake/packages'
    dependencies = sorted(packages.glob('*/.lake/build/lib/lean'))
    if not (packages / 'mathlib').is_dir() or not dependencies:
        parser.error('Mathlib dependencies are unavailable. Run lake update and '
                     'lake exe cache get in formal_global first, or pass --mathlib-project.')
    build = (args.build_dir or (ROOT / '.lake/build/lib/lean')).resolve()
    build.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    # Exclude preexisting project oleans and inherited LEAN_PATH deliberately.
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in [build, *dependencies])
    for filename in args.files:
        source = Path(filename)
        if not source.is_absolute():
            source = ROOT / source
        source = source.resolve()
        relative = source.relative_to(ROOT)
        if source.suffix != '.lean':
            parser.error(f'Not a Lean source file: {filename}')
        target = build / relative.with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            [compiler, '--trust=0', '-o', str(target), str(relative)],
            cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
        print('CHECKED', relative, flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
