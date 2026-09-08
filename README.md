# Proving the correctness of a compiler — Lean 4 port

A Lean 4 translation of the Coq development accompanying Xavier Leroy's
lectures *Proving the correctness of a compiler* at the
[EUTypes 2019 summer school](https://xavierleroy.org/courses/EUTypes-2019/).

The development defines IMP (a small imperative language) and a stack machine,
compiles the former to the latter, and proves that compilation preserves
program behaviour — for terminating *and* for diverging programs. It then adds
two optimisations, constant propagation and dead code elimination, each with a
proof of semantic preservation, and closes with the theory of fixpoints that
makes the dataflow analyses precise.

Everything is proved. No `sorry` appears in the library, and the headline
theorems depend only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Repository layout

```
.                       the Lean 4 development (this is the repository root)
├── CompilerVerification/    the library: six Lean modules
├── Exercises.lean          the course exercises, as `sorry` holes
├── html/                   the sources pretty-printed as HTML
├── slides/                 slides.tex  (XeLaTeX/Beamer source)
├── slides.pdf              the built slides
├── index.html              course page, in the style of the original
├── tools/lean2html.py      the HTML generator (a coq2html analogue)
└── orig/                   the original Coq course material, for reference
```

`orig/` is an archival copy of Xavier Leroy's EUTypes 2019 course page and
its materials — the Coq sources (`orig/sources/`), the original slides, the
coqdoc HTML, and the two linked papers. Nothing in the Lean development
depends on it; it is there so the port can be read side by side with its
original. See `orig/NOTICE.md` for provenance and licensing.

## Building

Requires [`elan`](https://github.com/leanprover/elan); the toolchain
(Lean 4.33.1) is pinned in `lean-toolchain` and will be fetched automatically.

```bash
lake build
```

There are no external dependencies — not even Mathlib — so the build takes
seconds.

`lake build` also compiles `Exercises.lean`, which reports one
`declaration uses 'sorry'` warning per unsolved exercise. That is expected.
To build only the finished development:

```bash
lake build CompilerVerification
```

## Contents

| File | Contents |
| --- | --- |
| `CompilerVerification/Sequences.lean` | Reflexive transitive closure, transitive closure, and infinite sequences of transitions |
| `CompilerVerification/IMP.lean` | IMP: syntax, big-step semantics, small-step semantics, continuation semantics, and the equivalences between them |
| `CompilerVerification/Compil.lean` | The stack machine, the compiler, and its correctness proofs |
| `CompilerVerification/Constprop.lean` | Constant propagation: smart constructors, the forward analysis, the optimisation, and its correctness |
| `CompilerVerification/Deadcode.lean` | Liveness analysis (backward) and dead code elimination, with its correctness |
| `CompilerVerification/Fixpoints.lean` | Knaster–Tarski, an algorithm that computes least fixpoints, and its application to the analyses |
| `Exercises.lean` | The exercises from the original, restated for Lean |

### The main theorems

In `Compil.lean`:

```lean
theorem compileProgram_correct_terminating {s c s'} (h : cexec s c s') :
    machineTerminates (compileProgram c) s s'

theorem compileProgram_correct_diverging {c : com} {s : Store}
    (h : Infseq step (c, .stop, s)) : machineDiverges (compileProgram c) s
```

The first is proved by induction on the big-step evaluation of the source
program. The second — the real theorem — comes from a simulation diagram
(`simulation_step`) relating the continuation semantics of IMP to the machine,
with an anti-stuttering measure to rule out the machine standing still forever
while the source makes progress.

In `Constprop.lean` and `Deadcode.lean`:

```lean
theorem cpCom_correct_terminating : ∀ (c : com) {s₁ s₂ : Store} {S₁ : AStore},
    cexec s₁ c s₂ → Matches s₁ S₁ → cexec s₁ (cpCom S₁ c) s₂

theorem dce_correct_terminating {s c s'} (h : cexec s c s') :
    ∀ (L : IdentSet) (s₁ : Store), agree (live c L) s s₁ →
    ∃ s₁', cexec s₁ (dce c L) s₁' ∧ agree L s' s₁'
```

## How the port differs from the Coq original

The definitions and theorem statements follow the Coq sources. All proofs and
all explanatory text were rewritten for Lean. A few points where the two
systems pulled the development in different directions:

**Infinite sequences.** Coq defines divergence with a `CoInductive`
predicate. Lean 4 has no coinductive types, so `Sequences.Infseq` is defined
directly as the greatest fixpoint: `Infseq R a` holds when some set `X`
contains `a` and is closed under taking one more transition. The constructor,
the destructor and the coinduction principle are then ordinary lemmas, and
`Infseq.coinduction_plus` plays the role of Coq's
`infseq_coinduction_principle_2`.

**Finite maps and finite sets.** Coq's standard library supplies `FMaps` and
`FSets`; Lean's core library supplies neither, and depending on Mathlib for
them would have made the build much heavier. Abstract stores
(`Constprop.AStore`) are association lists and sets of variables
(`Deadcode.IdentSet`) are plain lists. Duplicates are harmless: every
statement is about lookup or membership, never about the representation. The
handful of facts actually needed — `find_join`, `find_update`, `equal_find`,
and the membership lemmas — are proved from scratch.

As a consequence the well-foundedness argument in `Fixpoints.lean` differs.
Coq reasons about the *cardinal* of a finite map; here the measure is the
length of the deduplicated list of keys an abstract store constrains, and the
two supporting combinatorial lemmas (`nodup_length_le`,
`subset_of_length_le`) are proved directly.

**Program counters and code positions.** `CodeAt C pc C'` is an inductive
predicate in Coq; here it is a definition (`∃ C₁ C₃, C = C₁ ++ C' ++ C₃ ∧
pc = codelen C₁`), which is far easier to take apart. Note also that Lean's
`++` is left-associative where Coq's is right-associative, so the navigation
lemmas compose in the mirror-image order.

Coq's proof scripts lean on `eauto with code` and `autorewrite with code` to
discharge program-counter arithmetic. Lean has no equivalent, so the
correctness lemmas are stated with the target program counter as a variable
constrained by an equation (`pc' = pc + codelen …`), which lets the pieces
compose and leaves `omega` to do the arithmetic. The "smart" transition
lemmas (`transition.add'`, `transition.setvar'`, …) serve the same purpose for
individual instructions.

**Fixpoints.** Coq's `Program Fixpoint` writes the iteration algorithm with
holes for the proofs. The Lean equivalent, `FixLattice.iterate`, is built with
`WellFounded.fix` and returns a subtype carrying the fixpoint together with
its specification. `Fixpoints.CexecM` corresponds to Coq's `Program Fixpoint
Cexec`: it defines the abstract interpreter and proves it monotone
simultaneously, which is forced, since the loop case cannot take a fixpoint
without knowing the body is monotone.

## Licence

The original Coq sources are copyright 2019, 2025 Xavier Leroy, distributed
under the GNU Lesser General Public License, version 2.1 or (at your option)
any later version. This Lean translation is a modified work distributed under
the same terms; see `LICENSE.md`. Each file carries a notice saying what was
changed.

The original course page, slides and Coq sources are at
<https://xavierleroy.org/courses/EUTypes-2019/>.
