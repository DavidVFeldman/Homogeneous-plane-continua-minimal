#!/usr/bin/env python3
"""Delete the unused declarations of the minimal repository.

    python3 scripts/prune.py SRC DST [--dry-run]

SRC is an untouched copy of the first cut (the repository before this step, with the files
of `doc/minimal/` named below); DST is the repository being pruned (the root). SRC and DST must be
different folders. The script rebuilds every file it manages in DST from SRC, so it can be run
again after the keep list changes; the files it manages are `HPC/**/*.lean`, `Axioms.lean` and
`axioms.txt`. It reads, from SRC:

* `doc/minimal/unused.tsv`: the candidates, one per line: name, module, kind, start, end (the
  lines of the declaration in SRC, its docstring and attributes included);
* `doc/minimal/modules.tsv`: per kept module, the number of its counted declarations;
* `doc/minimal/owners.tsv`: the constants that belong to a candidate and go with it (structure
  fields and other generated names, and the two `where` declarations written inside a
  candidate): name, owner, whether the census counts it, module;

and from DST:

* `doc/minimal/keep.txt`: names of candidates that are not to be deleted, one per line, each
  followed by `#` and the reason. Blank lines and lines starting with `#` are ignored.

What it does:

1. In each module, it deletes the lines of every candidate not in the keep list. A command
   modifier ending in `in` just above a deleted declaration (`open X in`, `set_option o v in`,
   `omit [I] in`, possibly over several lines) is deleted with it. Where the deletion leaves two
   blank lines in a row, one is deleted.
2. A module all of whose counted declarations are deleted (directly or with their owner), and
   which defines no syntax, notation, macro or attribute except `local` ones, is removed. A module
   that imported a removed one imports what the removed one imported instead (as far as it is
   kept or outside HPC), each module once, in order.
3. In `Axioms.lean`, the `#print axioms` lines of deleted declarations and of the constants they
   own are removed, with comment labels left without a `#print` line and groups left empty;
   `axioms.txt` loses their entries. The header's description is adjusted to the pruning.

Nothing else is changed. The report lists the counts and the removed modules.
"""
import collections
import os
import re
import shutil
import sys

ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
DRY = '--dry-run' in sys.argv
if len(ARGS) != 2:
    sys.exit(__doc__)
SRC, DST = (os.path.abspath(a) for a in ARGS)
if SRC == DST:
    sys.exit('SRC and DST must differ')
TARGET = 'HPC.BJ59.BJ59E'
IMPORT = re.compile(r'^import\s+(\S+)\s*$')
SPECIAL = re.compile(r'^\s*(?:@\[.*\]\s*)?'
                     r'(?:(?:private|protected|noncomputable|scoped(?:\[[^\]]*\])?|local)\s+)*'
                     r'(macro|macro_rules|syntax|notation|notation3|infix|infixl|infixr|prefix|'
                     r'postfix|elab|elab_rules|declare_syntax_cat|initialize|builtin_initialize|'
                     r'register_\w+|simproc|dsimproc|simproc_decl|run_cmd|run_elab|run_meta|'
                     r'deriving\s+instance|export)\b'
                     r'|^\s*attribute\s*\[(?!\s*local)', re.M)
LOCAL_SYNTAX = re.compile(r'^\s*(?:@\[.*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*local\s+'
                          r'(macro|macro_rules|syntax|notation|notation3|infix|infixl|infixr|'
                          r'prefix|postfix|elab|elab_rules)\b')
MODIFIER = re.compile(r'^(set_option|open|omit|include|variable)\b')
HEAD = re.compile(r'\s*(/--|@\[|alias\b|(?:(?:private|protected|noncomputable|unsafe|partial|'
                  r'nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|'
                  r'irreducible_def|opaque)\b)')


def read(p):
    with open(p, encoding='utf-8') as f:
        return f.read()


def write(p, s):
    if not DRY:
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8', newline='') as f:
            f.write(s)


def code_only(text):
    """The text with comments and string literals blanked out, newlines kept."""
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
            out.append('\n' * text[i:j + 1].count('\n'))
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def defines_syntax(text):
    """Whether the code defines syntax, notation, macros or attributes visible to importers."""
    return any(SPECIAL.search(l) and not LOCAL_SYNTAX.match(l)
               for l in code_only(text).split('\n'))


def modname(rel):
    return rel[:-5].replace('/', '.')


def tsv(p):
    rows = [l.split('\t') for l in read(p).split('\n') if l]
    return [dict(zip(rows[0], r)) for r in rows[1:]]


def main():
    path = {}
    for d, _, fs in os.walk(os.path.join(SRC, 'HPC')):
        for f in fs:
            if f.endswith('.lean'):
                rel = os.path.relpath(os.path.join(d, f), SRC).replace(os.sep, '/')
                path[modname(rel)] = rel
    cands = tsv(os.path.join(SRC, 'doc', 'minimal', 'unused.tsv'))
    counted = {r['module']: int(r['declarations'])
               for r in tsv(os.path.join(SRC, 'doc', 'minimal', 'modules.tsv'))}
    names = {r['name'] for r in cands}
    owners = tsv(os.path.join(SRC, 'doc', 'minimal', 'owners.tsv'))
    keep = {}
    kp = os.path.join(DST, 'doc', 'minimal', 'keep.txt')
    for i, line in enumerate(read(kp).split('\n') if os.path.exists(kp) else [], 1):
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        name, _, reason = line.partition('#')
        name = name.strip()
        if name not in names:
            sys.exit('keep.txt line %d: %r is not a candidate' % (i, name))
        if not reason.strip():
            sys.exit('keep.txt line %d: no reason given' % i)
        keep[name] = reason.strip()
    dele = [r for r in cands if r['name'] not in keep]
    by_mod = collections.defaultdict(list)
    for r in dele:
        by_mod[r['module']].append((int(r['start']), int(r['end']), r['name']))

    # 1. deletions
    new_text, ndel_lines = {}, 0
    for m, rel in path.items():
        lines = read(os.path.join(SRC, rel)).split('\n')
        gone = set()
        for s, e, name in by_mod.get(m, ()):
            if not HEAD.match(lines[s - 1]):
                sys.exit('%s:%d: %s does not start here' % (rel, s, name))
            if gone & set(range(s, e + 1)):
                sys.exit('%s: overlapping deletions at %s' % (rel, name))
            gone.update(range(s, e + 1))
            j = s - 1                                  # command modifiers ending in `in`
            while j >= 1 and re.search(r'(^|\s)in$', lines[j - 1].rstrip()):
                k = j
                while k >= 1 and not MODIFIER.match(lines[k - 1]):
                    if not lines[k - 1][:1].isspace():
                        sys.exit('%s:%d: cannot find the start of the modifier above %s'
                                 % (rel, j, name))
                    k -= 1
                if k < 1:
                    sys.exit('%s:%d: modifier without a start above %s' % (rel, j, name))
                gone.update(range(k, j + 1))
                j = k - 1
        kept_lines = []
        for i, l in enumerate(lines, 1):
            if i in gone:
                continue
            if not l.strip() and kept_lines and not kept_lines[-1].strip() and \
                    (i - 1 in gone):
                continue                               # no double blank line
            kept_lines.append(l)
        ndel_lines += len(lines) - len(kept_lines)
        new_text[m] = '\n'.join(kept_lines)

    # 2. emptied modules
    dele_names = {r['name'] for r in dele}
    gone_names = dele_names | {o['name'] for o in owners if o['owner'] in dele_names}
    ndel = collections.Counter(r['module'] for r in dele)
    for o in owners:
        if o['owner'] in dele_names and o['counted'] == '1':
            ndel[o['module']] += 1
    removed = {m for m in path if m != TARGET and m in counted and counted[m] > 0
               and ndel[m] == counted[m] and not defines_syntax(new_text[m])}
    imports = {m: [mm.group(1) for l in new_text[m].split('\n') for mm in [IMPORT.match(l)] if mm]
               for m in path}

    def frontier(x, seen):
        out = []
        for i in imports[x]:
            if i in removed:
                if i not in seen:
                    seen.add(i)
                    out += frontier(i, seen)
            else:
                out.append(i)
        return out

    rewritten = 0
    for m in path:
        if m in removed:
            continue
        out, seen_imp, changed = [], set(), False
        for l in new_text[m].split('\n'):
            mm = IMPORT.match(l)
            if not mm:
                out.append(l)
                continue
            i = mm.group(1)
            ts = frontier(i, {i}) if i in removed else [i]
            changed |= ts != [i]
            for t in ts:
                if t not in seen_imp:
                    seen_imp.add(t)
                    out.append('import ' + t)
        rewritten += changed
        new_text[m] = '\n'.join(out)
    # every kept module still reachable from the target, every import resolvable
    reach, st = set(), [TARGET]
    while st:
        x = st.pop()
        if x in reach:
            continue
        reach.add(x)
        st += [i for l in new_text[x].split('\n') for mm in [IMPORT.match(l)] if mm
               for i in [mm.group(1)] if i.startswith('HPC.')]
    missing = [x for x in reach if x not in path or x in removed]
    if missing:
        sys.exit('imports of removed or unknown modules: %s' % sorted(missing)[:5])
    orphans = sorted(set(path) - removed - reach)
    if orphans:
        sys.exit('modules no longer reachable from %s: %s' % (TARGET, orphans[:5]))

    # 3. the axiom audit
    ax = read(os.path.join(SRC, 'Axioms.lean')).split('\n')
    head_end = next(i for i, l in enumerate(ax) if l.startswith('-- ## '))
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
    for g, segs in groups:
        out = []
        for comments, prints in segs:
            kp_ = [(n, l) for n, l in prints if n not in gone_names]
            if kp_ or not prints:
                out += comments + [l for _, l in kp_]
                kept_names += [n for n, _ in kp_]
        if any(l.startswith('#print') for l in out):
            body += [g] + out
    while body and not body[-1].strip():
        body.pop()
    entries, cur = {}, None
    for l in read(os.path.join(SRC, 'axioms.txt')).split('\n'):
        mm = re.match(r"^'(.+?)' (depends on axioms|does not depend)", l)
        if mm:
            cur = mm.group(1)
            entries.setdefault(cur, []).append([l])
        elif l and cur:
            entries[cur][-1].append(l)
    used_count = collections.Counter()
    ax_out = []
    for n in kept_names:
        k = used_count[n]
        used_count[n] += 1
        ax_out += entries[n][k] if k < len(entries[n]) else entries[n][0]

    # write
    for m, rel in path.items():
        dst = os.path.join(DST, rel)
        if m in removed:
            if os.path.exists(dst) and not DRY:
                os.remove(dst)
        else:
            write(dst, new_text[m])
    header = '\n'.join(ax[:head_end])
    old_desc = 'whose modules this\nrepository keeps, grouped'
    if header.count(old_desc) != 1:
        sys.exit('Axioms.lean: unexpected header')
    if dele:
        header = header.replace(old_desc, 'that this repository\nkeeps, grouped')
    write(os.path.join(DST, 'Axioms.lean'), header + '\n' + '\n'.join(body) + '\n')
    write(os.path.join(DST, 'axioms.txt'), '\n'.join(ax_out) + '\n')
    if not DRY:                                       # empty directories left by removals
        for d, _, _ in sorted(os.walk(os.path.join(DST, 'HPC')), reverse=True):
            if not os.listdir(d):
                os.rmdir(d)
    print('candidates %d, kept by keep.txt %d, deleted %d (lines deleted %d)'
          % (len(cands), len(keep), len(dele), ndel_lines))
    print('modules: %d before, %d removed, %d after; imports rewritten in %d'
          % (len(path), len(removed), len(path) - len(removed), rewritten))
    print('Axioms.lean: %d #print lines (%d theorems); axioms.txt: %d lines'
          % (len(kept_names), len(set(kept_names)), len(ax_out)))
    print('removed modules:', ' '.join(sorted(removed)))


main()
