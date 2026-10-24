#!/usr/bin/env python3
"""Derive the minimal repository from the full one.

    python3 make_minimal.py FULL OUT

FULL is a copy of the full repository (it must hold doc/depcensus/ from the census); OUT is
created and must not exist. The minimal repository keeps only the library HPC, and of its
modules only those the classification needs, found from the census:

1. U: the modules holding a declaration that the two final theorems use (doc/depcensus/used.txt).
2. K: U closed under "requires": module Y requires module X when a constant of Y refers to a
   constant of X (doc/depcensus/edges.tsv). So every declaration left in a kept module, used or
   not, still finds everything it refers to.
3. Modules that define syntax, macros, notation or elaborators, or set attributes on other
   modules' constants, leave no trace in the edges. Each such module that a kept module imports,
   directly or through other modules, is kept as well, and step 2 is repeated. Comments and
   string literals are removed before the search for these commands.
4. Every other module of HPC's import closure is removed. A kept module that imported a removed
   one imports instead what the removed one imported, as far as it is kept or outside HPC, so
   that nothing a kept module could see before is lost.

Axioms.lean and axioms.txt keep the entries of declarations in kept modules, in their order; a
comment that labels #print lines is kept when one of them is. The census was made before the
rename of HPC/Chains/Aux.lean; its module names are mapped. A module of the closure that the
census does not list must hold nothing but imports and comments, or the script stops; modules
whose length differs from the census's are listed in the report. Nothing inside a kept module is
changed except its import lines.
"""
import collections
import os
import re
import shutil
import sys

FULL, OUT = sys.argv[1:3]
TARGET = 'HPC.BJ59.BJ59E'
RENAME = {'HPC.Chains.Aux': 'HPC.Chains.Auxiliary'}
SPECIAL = re.compile(r'^\s*(?:@\[.*\]\s*)?'
                     r'(?:(?:private|protected|noncomputable|scoped(?:\[[^\]]*\])?|local)\s+)*'
                     r'(macro|macro_rules|syntax|notation|notation3|infix|infixl|infixr|prefix|'
                     r'postfix|elab|elab_rules|declare_syntax_cat|initialize|builtin_initialize|'
                     r'register_\w+|simproc|dsimproc|simproc_decl|run_cmd|run_elab|run_meta|'
                     r'deriving\s+instance|export)\b'
                     r'|^\s*attribute\s*\[(?!\s*local)', re.M)
IMPORT = re.compile(r'^import\s+(\S+)\s*$')
FULL_URL = 'https://github.com/DavidVFeldman/homogeneous-plane-continua'
HPC_LEAN = """import HPC.BJ59.BJ59E

/-!
# HPC: the classification of homogeneous plane continua

`HPC.BJ59.BJ59E` holds the final theorems `HPC.BJ59.ho16_classification₄` and
`HPC.BJ59.ho16_classification_plane₄`. This repository keeps the modules that hold a declaration
they use and the modules that declarations in kept modules refer to; see `README.md`.
-/
"""
README = """# Homogeneous plane continua in Lean: the modules of the classification

This repository holds the modules of the Lean formalization in the repository
[homogeneous-plane-continua][full] that the proof of the classification of homogeneous plane
continua draws on. The documentation, the records and the other modules are in the full
repository.

[full]: """ + FULL_URL + """

The two final theorems, `HPC.BJ59.ho16_classification₄` and
`HPC.BJ59.ho16_classification_plane₄`, are in `HPC/BJ59/BJ59E.lean`.

## How this repository was made

`scripts/make_minimal.py` derives it from the full repository, using the full repository's
dependency census (`doc/depcensus/` there; its README says which state of the sources it
describes):

* only the library `HPC` is kept, the import closure of `HPC.BJ59.BJ59E` ({closure} modules);
* of these, {kept} modules are kept: the {used} that hold a declaration the final theorems use,
  and every module that a declaration in a kept module refers to;
* the other {removed} are removed;
* {syntax}
* a kept module that imported a removed one imports what the removed one imported instead.

Nothing inside a kept module is changed apart from its import lines. So the kept modules also
hold declarations the final theorems do not use: of their {decl:,} declarations, the final
theorems use {dused:,}.

{kept} modules under `HPC/`, with {lines:,} lines of Lean, and the root module `HPC.lean`.

Comments in the Lean files cite documents, modules and line numbers of the full repository. In
the {rewritten} modules whose imports were rewritten, the line numbers differ from the full
repository's.

## Building and checking

The toolchain is `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0` (`lean-toolchain`,
`lake-manifest.json`). From the root:

```
lake exe cache get                         # Mathlib's compiled files
lake build                                 # the library HPC
lake env lean Axioms.lean > axioms-ci.txt  # the axiom audit; compare with axioms.txt
```

`Axioms.lean` holds the `#print axioms` lines of the full repository's audit for theorems
declared in kept modules: {prints:,} lines, for {distinct:,} theorems (as in the full repository,
a few theorems are printed in more than one group). `axioms.txt` is its expected output. The
workflow in `.github/workflows/build.yml` builds the library on every push, fails on any
`sorry`, regenerates the audit, compares it with `axioms.txt`, and allows no axiom other than
`propext`, `Classical.choice` and `Quot.sound`.

{credits}
`scripts/make_minimal.py` was written by Claude (Anthropic).

## License

Apache License 2.0; see `LICENSE`. Quotations from published papers in the comments of the Lean
files remain under their publishers' copyright and are not covered by this license.
"""


def modname(rel):
    return rel[:-5].replace('/', '.')


def read(p):
    return open(p, encoding='utf-8').read()


def code_only(text):
    """The text with comments (nested block comments, docstrings, line comments) and string
    literals replaced by spaces, newlines kept."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth:
            if text.startswith('/-', i):
                depth, i = depth + 1, i + 2
            elif text.startswith('-/', i):
                depth, i = depth - 1, i + 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
            continue
        if text.startswith('/-', i):
            depth, i = 1, i + 2
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(' ' * text[i:j + 1].count('\n'))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def main():
    if os.path.exists(OUT):
        sys.exit('OUT exists: ' + OUT)
    # modules and imports
    path = {}
    for d, _, fs in os.walk(os.path.join(FULL, 'HPC')):
        for f in fs:
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(d, f), FULL).replace(os.sep, '/')
                path[modname(rel)] = rel
    imports = {}
    for m, rel in path.items():
        imports[m] = [mm.group(1) for line in read(os.path.join(FULL, rel)).split('\n')
                      for mm in [IMPORT.match(line)] if mm]
    closure, stack = set(), [TARGET]
    while stack:
        m = stack.pop()
        if m in closure:
            continue
        closure.add(m)
        stack += [i for i in imports[m] if i in path]
    # census
    cen = os.path.join(FULL, 'doc', 'depcensus')
    mod_of = {}
    for i, line in enumerate(open(os.path.join(cen, 'nodes.tsv'), encoding='utf-8')):
        p = line.rstrip('\n').split('\t')
        if i == 0:
            col = {k: j for j, k in enumerate(p)}
            continue
        mod_of[p[col['name']]] = RENAME.get(p[col['module']], p[col['module']])
    used = set()
    for line in open(os.path.join(cen, 'used.txt'), encoding='utf-8'):
        if line.strip():
            used.add(RENAME.get(line.rstrip('\n').split('\t')[1], line.rstrip('\n').split('\t')[1]))
    requires = collections.defaultdict(set)
    for i, line in enumerate(open(os.path.join(cen, 'edges.tsv'), encoding='utf-8')):
        if i == 0:
            continue
        s, t = line.rstrip('\n').split('\t')
        a, b = mod_of.get(s), mod_of.get(t)
        if a and b and a != b and a in closure and b in closure:
            requires[a].add(b)
    special = {m for m in closure if SPECIAL.search(code_only(read(os.path.join(FULL, path[m]))))}
    missing = sorted(m for m in closure if m not in set(mod_of.values()) and m != TARGET)
    for m in missing:
        rest = [l for l in code_only(read(os.path.join(FULL, path[m]))).split('\n')
                if l.strip() and not IMPORT.match(l)]
        if rest:
            sys.exit('%s is not in the census and holds more than imports: %r' % (m, rest[0]))
    census_lines = {}
    for i, line in enumerate(open(os.path.join(cen, 'modules.tsv'), encoding='utf-8')):
        p = line.rstrip('\n').split('\t')
        if i == 0:
            mcol = {k: j for j, k in enumerate(p)}
            continue
        census_lines[RENAME.get(p[0], p[0])] = int(p[mcol['lines']])
    n_decl, n_used = collections.Counter(), collections.Counter()
    for i, line in enumerate(open(os.path.join(cen, 'nodes.tsv'), encoding='utf-8')):
        p = line.rstrip('\n').split('\t')
        if i and p[col['counted']] == '1':
            n_decl[RENAME.get(p[col['module']], p[col['module']])] += 1
    for line in open(os.path.join(cen, 'used.txt'), encoding='utf-8'):
        if line.strip():
            q = line.rstrip('\n').split('\t')[1]
            n_used[RENAME.get(q, q)] += 1
    keep = (used & closure) | {TARGET}
    while True:
        stack, k = list(keep), set()
        while stack:
            m = stack.pop()
            if m in k:
                continue
            k.add(m)
            stack += list(requires[m])
        reach, stack = set(), list(k)
        while stack:
            m = stack.pop()
            if m in reach:
                continue
            reach.add(m)
            stack += [i for i in imports[m] if i in closure]
        new = k | (special & reach)
        if new == keep:
            break
        keep = new
    removed = closure - keep
    by_refs, stack = set(), list((used & closure) | {TARGET})
    while stack:
        m = stack.pop()
        if m not in by_refs:
            by_refs.add(m)
            stack += list(requires[m])
    special_only = keep - by_refs
    # import rewriting
    def frontier(x, seen):
        out = []
        for i in imports[x]:
            if i in path and i not in keep:
                if i not in seen:
                    seen.add(i)
                    out += frontier(i, seen)
            else:
                out.append(i)
        return out
    os.makedirs(OUT)
    rewritten = 0
    for m in sorted(keep):
        src = read(os.path.join(FULL, path[m]))
        lines, out, seen_imp = src.split('\n'), [], set()
        changed = False
        for line in lines:
            mm = IMPORT.match(line)
            if not mm:
                out.append(line)
                continue
            i = mm.group(1)
            targets = [i] if (i not in path or i in keep) else frontier(i, {i})
            changed |= targets != [i]
            for t in targets:
                if t not in seen_imp:
                    seen_imp.add(t)
                    out.append('import ' + t)
        rewritten += changed
        dst = os.path.join(OUT, path[m])
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w', encoding='utf-8', newline='').write('\n'.join(out))
    # root files
    for f in ('lean-toolchain', 'lake-manifest.json', 'LICENSE', '.gitattributes'):
        shutil.copyfile(os.path.join(FULL, f), os.path.join(OUT, f))
    hpc = read(os.path.join(FULL, 'HPC.lean'))
    if [l for l in hpc.split('\n') if l.startswith('import ')] != ['import ' + TARGET]:
        sys.exit('HPC.lean does not import exactly ' + TARGET)
    open(os.path.join(OUT, 'HPC.lean'), 'w', encoding='utf-8', newline='').write(HPC_LEAN)
    lake = read(os.path.join(FULL, 'lakefile.toml'))
    lake = lake[:lake.index('# Modules outside the classification')].rstrip('\n') + '\n'
    open(os.path.join(OUT, 'lakefile.toml'), 'w', encoding='utf-8', newline='').write(lake)
    gi = [l for l in read(os.path.join(FULL, '.gitignore')).split('\n')
          if not l.startswith(('/doc/', '!/doc/'))]
    open(os.path.join(OUT, '.gitignore'), 'w', encoding='utf-8', newline='').write('\n'.join(gi))
    wf = read(os.path.join(FULL, '.github', 'workflows', 'build.yml'))
    wf = re.sub(r'lake build HPC [A-Za-z ]+2>&1', 'lake build HPC 2>&1', wf)
    for old, new in (('name: Build the libraries', 'name: Build the library'),
                     ('name: No sorry in the libraries', 'name: No sorry in the library')):
        if wf.count(old) != 1:
            sys.exit('not once in build.yml: ' + old)
        wf = wf.replace(old, new)
    os.makedirs(os.path.join(OUT, '.github', 'workflows'))
    open(os.path.join(OUT, '.github', 'workflows', 'build.yml'), 'w', encoding='utf-8',
         newline='').write(wf)
    # Axioms.lean and axioms.txt
    ax = read(os.path.join(FULL, 'Axioms.lean')).split('\n')
    head_end = next(i for i, l in enumerate(ax) if l.startswith('-- ## '))
    # A group starts at a line "-- ## ..."; inside it, a segment is a run of comment lines with
    # the #print lines after it. A segment with #print lines is kept when one of them is; a
    # segment of comments alone is kept with its group; a group is kept when a #print line is.
    groups = []
    for l in ax[head_end:]:
        if l.startswith('-- ## '):
            groups.append([l, []])
            continue
        mm = re.match(r'#print axioms (\S+)', l)
        if mm:
            segs = groups[-1][1]
            if not segs:
                segs.append([[], []])
            segs[-1][1].append((mm.group(1), l))
        elif l.startswith('--'):
            segs = groups[-1][1]
            if not segs or segs[-1][1]:
                segs.append([[], []])
            segs[-1][0].append(l)
        elif l.strip():
            sys.exit('unexpected line in Axioms.lean: ' + l)
    kept_names, body = [], []
    for head, segs in groups:
        out = []
        for comments, prints in segs:
            kp = [(n, l) for n, l in prints if mod_of.get(n) in keep]
            if kp or not prints:
                out += comments + [l for _, l in kp]
                kept_names += [n for n, _ in kp]
        if any(l.startswith('#print') for l in out):
            body += [head] + out
    header = ['import HPC', '', '/-!', '# Axiom audit', '',
              '`#print axioms` for the audited theorems of the full repository whose modules this',
              'repository keeps, grouped by source as there. The expected output is `axioms.txt`;',
              'after `lake build`, `lake env lean Axioms.lean > axioms-ci.txt` regenerates it for',
              'comparison. Every entry must show `[propext, Classical.choice, Quot.sound]` or a',
              'subset of it.', '-/', '']
    open(os.path.join(OUT, 'Axioms.lean'), 'w', encoding='utf-8', newline='').write(
        '\n'.join(header + body) + '\n')
    entries, cur = [], None
    for l in read(os.path.join(FULL, 'axioms.txt')).split('\n'):
        mm = re.match(r"^'(.+?)' (depends on axioms|does not depend)", l)
        if mm:
            cur = [mm.group(1), [l]]
            entries.append(cur)
        elif l and cur:
            cur[1].append(l)
    by = {}
    for n, ls in entries:
        by.setdefault(n, ls)
    lost = [n for n in kept_names if n not in by]
    if lost:
        sys.exit('no axioms.txt entry for: %s' % lost[:5])
    open(os.path.join(OUT, 'axioms.txt'), 'w', encoding='utf-8', newline='').write(
        ''.join('\n'.join(by[n]) + '\n' for n in kept_names))
    os.makedirs(os.path.join(OUT, 'scripts'))
    shutil.copyfile(os.path.abspath(__file__), os.path.join(OUT, 'scripts', 'make_minimal.py'))
    nlines = sum(len(read(os.path.join(OUT, path[m])).splitlines()) for m in keep)
    full_readme = read(os.path.join(FULL, 'README.md'))
    a = full_readme.index('\n## Credits\n')
    b = full_readme.index('\n## ', a + 1)
    credits = full_readme[a + 1:b].rstrip('\n') + '\n'
    if special_only:
        syntax = ('{n} more modules are kept because they define syntax, notation, macros or '
                  'attributes for\n  kept modules, which leaves no trace in the census;'
                  ).format(n=len(special_only))
    else:
        syntax = ('a module that defines syntax, notation, macros or attributes for kept modules '
                  'is kept too,\n  since that leaves no trace in the census; here every such '
                  'module is kept already;')
    open(os.path.join(OUT, 'README.md'), 'w', encoding='utf-8', newline='').write(
        README.format(kept=len(keep), closure=len(closure), removed=len(removed),
                      lines=nlines, used=len(used & closure), by_refs=len(by_refs),
                      prints=len(kept_names), distinct=len(set(kept_names)), syntax=syntax,
                      rewritten=rewritten, credits=credits,
                      decl=sum(n_decl[m] for m in keep), dused=sum(n_used[m] for m in keep)))
    # report
    print('HPC import closure: %d modules; used: %d; kept: %d (kept for references: %d, '
          'for syntax only: %s); removed: %d'
          % (len(closure), len(used & closure), len(keep), len(by_refs), sorted(special_only),
             len(removed)))
    print('modules with syntax commands: %s' % sorted(special))
    print('kept modules whose length differs from the census: %s' % sorted(
        m for m in keep if m in census_lines
        and len(read(os.path.join(FULL, path[m])).splitlines()) != census_lines[m]))
    print('modules whose imports were rewritten: %d' % rewritten)
    print('audited theorems kept: %d of %d' % (len(kept_names),
                                               sum(1 for l in ax if l.startswith('#print'))))
    if missing:
        print('modules of the closure unknown to the census: %s' % missing)
    print('lines in kept modules: %d' % nlines)


main()
