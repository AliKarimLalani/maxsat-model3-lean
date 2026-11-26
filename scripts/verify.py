#!/usr/bin/env python3
"""Run with `lake env python3 scripts/verify.py` after dependencies are installed.

Recompile every project source in dependency order with warnings as errors,
audit all theorem dependencies, and record source hashes and actual exits.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

root = Path(__file__).resolve().parents[1]
out = root / '.lake/build/lib/lean'
logs = root / 'verification'
out.mkdir(parents=True, exist_ok=True)
logs.mkdir(exist_ok=True)
env = dict(os.environ)
env['LEAN_PATH'] = str(out) + os.pathsep + env.get('LEAN_PATH', '')
version = subprocess.check_output(['lean', '--version'], text=True).strip()
sources = {'.'.join(p.relative_to(root).with_suffix('').parts): p
           for p in (root / 'Model3MaxSAT').glob('*.lean')}
sources['Model3MaxSAT'] = root / 'Model3MaxSAT.lean'
sources['Audit'] = root / 'Audit.lean'
order = []
visiting = set()
def visit(name):
    if name in order:
        return
    assert name not in visiting, ('cyclic imports', name)
    visiting.add(name)
    for dependency in re.findall(r'^import\s+(\S+)', sources[name].read_text(), re.M):
        if dependency in sources:
            visit(dependency)
    visiting.remove(name)
    order.append(name)
for name in sorted(sources):
    visit(name)

results = []
for module in order:
    source = sources[module]
    target = out / Path(*module.split('.')).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = ['lean', '-DwarningAsError=true', '--root=' + str(root),
           '-o', str(target), str(source)]
    result = subprocess.run(cmd, env=env, text=True, capture_output=True)
    log = (version + '\nMathlib commit: f897ebcf72cd16f89ab4577d0c826cd14afaafc7\n'
           + 'Command: ' + ' '.join(cmd) + '\n\n' + result.stdout + result.stderr
           + '\nExit status: ' + str(result.returncode) + '\n')
    (logs / (source.stem + '.log')).write_text(log)
    entry = {'file': str(source.relative_to(root)), 'exit_status': result.returncode,
             'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
    results.append(entry)
    print(json.dumps(entry), flush=True)
    if result.returncode:
        print(log, flush=True)
        raise SystemExit(result.returncode)

audit = (logs / 'Audit.log').read_text()
reported = re.findall(r'depends on axioms: \[([^\]]*)\]', audit)
found = {a.strip() for line in reported for a in line.split(',') if a.strip()}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert found <= allowed, found - allowed
for source in sources.values():
    text = re.sub(r'/-[\s\S]*?-/', '', source.read_text())
    text = re.sub(r'--[^\n]*', '', text)
    bad = re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', text)
    assert bad is None, (source, bad.group(0))
    assert 'skipKernel' not in text
summary = {'lean': version, 'mathlib_commit': 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7',
           'files': results,
           'audited_theorems': (root / 'Audit.lean').read_text().count('#print axioms'),
           'axiom_allowlist_passed': True, 'source_token_check_passed': True,
           'main_upper_bound_proved': True,
           'main_theorem': 'Model3MaxSAT.randomized_model3_competitiveRatio_le',
           'note': 'All construction, switching, moment, energy and averaging dependencies are proved.'}
(logs / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('All sources compiled. All theorem axiom reports pass. Main upper bound proved.', flush=True)
