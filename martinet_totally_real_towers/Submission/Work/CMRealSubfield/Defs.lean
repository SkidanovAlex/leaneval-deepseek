import Mathlib

/-!
# The real-subfield reduction of Martinet's asymptotically good towers: definitions

This module fixes the definitions used by the subproject
`Submission/Work/CMRealSubfield`: the benchmark statement of `Challenge.lean`, its
root-discriminant form, and the ladder of "weak walls" that the reduction runs through.

## The mathematics

The benchmark (`Benchmark` below) asks for *totally real* number fields of unbounded degree
with bounded root discriminant.  The point of this subproject is that the total-reality
requirement is *cheap*, provided the fields of the family are **CM** (or totally real):
for a CM field `K` with maximal real subfield `K⁺ = NumberField.maximalRealSubfield K`

* `[K : K⁺] = 2` and `K⁺` is totally real (Mathlib's `IsCMField` / `IsTotallyReal`
  instances), and
* `rootDiscr K⁺ ≤ rootDiscr K`,

so a CM field of degree `2d` and root discriminant `≤ C` yields a *totally real* field of
degree `d` and root discriminant `≤ C`.  Iterating over a bounded-root-discriminant family
of CM fields of unbounded degree therefore gives the benchmark with the *same* constant `C`.

## The walls

* `WeakWall` — the bare family: number fields of unbounded degree with
  `|discr L| ≤ C ^ [L : ℚ]` (equivalently `rootDiscr L ≤ C`).  No total reality, no Galois
  hypothesis, no ramification hypothesis.  **This alone does not suffice for the elementary
  real-subfield argument** — see the module docstring of
  `Submission.Work.CMRealSubfield.Reduction` — because a number field need *not* have a
  totally real subfield of half its degree (`ℚ(∜2, i)` has degree `8` and maximal real
  subfield `ℚ(√2)`).
* `CMWall` — the same, with CM witnesses.  This is the hypothesis the source construction
  naturally supplies (the maximal real subfield `L⁺` is then of index `2`).
* `RealOrCMWall` — witnesses that are totally real or CM (the totally real case is the
  degenerate case `L⁺ = L`).
* `HalfRealSubfieldWall` — the most general elementary form: each witness has
  `2 * [L⁺ : ℚ] ≥ [L : ℚ]`, i.e. the maximal real subfield has at least half the degree.
  It contains `CMWall`, `RealOrCMWall`, and (by `Walls.halfRealSubfieldWall_of_*`) is
  strictly stronger than `WeakWall`.
-/

open NumberField

namespace Work.CMRealSubfield

/-- The benchmark statement (`Challenge.lean`): a constant `C > 0` such that for every `N`
there is a **totally real** number field `K` of degree `≥ N` with `|discr K| ≤ C ^ [K : ℚ]`. -/
def Benchmark : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
      Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d

/-- The benchmark in root-discriminant form: a constant `C > 0` such that for every `N`
there is a totally real number field of degree `≥ N` with `rootDiscr K ≤ C`.
(Equivalent to `Benchmark`, see `Work.CMRealSubfield.benchmark_iff_rootDiscrBenchmark`.) -/
def RootDiscrBenchmark : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
      Module.finrank ℚ K = d ∧ NumberField.rootDiscr K ≤ C

/-- **The bare weak wall.**  A family of number fields of unbounded degree whose absolute
discriminants satisfy `|discr L| ≤ C ^ [L : ℚ]`, equivalently `rootDiscr L ≤ C`
(`Work.CMRealSubfield.weakWall_iff_weakRootDiscrWall`).  There is no total reality
hypothesis, no Galois hypothesis and no hypothesis on ramification. -/
def WeakWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
    N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L

/-- The bare weak wall in root-discriminant form. -/
def WeakRootDiscrWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
    N ≤ Module.finrank ℚ L ∧ NumberField.rootDiscr L ≤ C

/-- The weak wall with the *structural* hypothesis on the witnesses that makes the
real-subfield reduction work: the maximal real subfield `L⁺` has at least half the degree,
i.e. `[L : L⁺] ≤ 2`.  For a CM field this is an equality (`[L : L⁺] = 2`); for a totally
real field `L⁺ = L` and it is trivial. -/
def HalfRealSubfieldWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
    N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L ∧
      2 * Module.finrank ℚ (NumberField.maximalRealSubfield L) ≥ Module.finrank ℚ L

/-- The weak wall with **CM witnesses**.  This is the intermediate wall of the deliverable:
the fields of the family are CM, so that each witness `L` has a totally real subfield `L⁺`
of index `2` with `rootDiscr L⁺ ≤ rootDiscr L`, and the constant is preserved. -/
def CMWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L)
      (_ : NumberField.IsCMField L),
    N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L

/-- The weak wall with witnesses that are either totally real or CM. -/
def RealOrCMWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
    (NumberField.IsTotallyReal L ∨ NumberField.IsCMField L) ∧
      N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L

/-- **The exact gap.**  The input that the bare `WeakWall` does *not* supply: every witness
`L` of the family has a totally real subfield `E` of at least half the degree whose root
discriminant is no larger than that of `L`.  `CMWall` supplies this with `E = L⁺` (and
`rootDiscr L⁺ ≤ rootDiscr L`); the bare `WeakWall` does not — the maximal real subfield of
`ℚ(∜2, i)` (degree `8`) is `ℚ(√2)` (degree `2`), and the root discriminant of a subfield is
at most that of the field. -/
def HalfDegreeRealSubfieldInput : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], ∃ (E : Type) (_ : Field E) (_ : NumberField E)
      (_ : NumberField.IsTotallyReal E),
    2 * Module.finrank ℚ E ≥ Module.finrank ℚ L ∧
      NumberField.rootDiscr E ≤ NumberField.rootDiscr L

/-- The weak wall whose witnesses are **totally complex with a maximal real subfield of exactly
half the degree**.  By
`Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank` this is *the same
wall* as `CMWall` (`Work.CMRealSubfield.cmWall_iff_totallyComplexHalfWall`): it isolates the two
structural properties that the real-subfield reduction actually consumes, without mentioning the
CM class. -/
def TotallyComplexHalfWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
    (NumberField.IsTotallyComplex L ∧
      2 * Module.finrank ℚ (NumberField.maximalRealSubfield L) = Module.finrank ℚ L) ∧
      N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L

/-- The weak wall with **CM-extension witnesses**: witnesses come as a pair `F ⊆ L` with `F`
totally real, `L` totally complex and `[L : F] = 2`.  By Mathlib's
`NumberField.IsCMField.ofCMExtension` (and `CMExtension.equivMaximalRealSubfield`, which
identifies `F` with `L⁺`) this is the same wall as `CMWall`
(`Work.CMRealSubfield.cmWall_iff_cmExtensionWall`); it is the form in which the CM fields of the
source construction are usually presented. -/
def CMExtensionWall : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
      (L : Type) (_ : Field L) (_ : NumberField L) (_ : NumberField.IsTotallyComplex L)
      (_ : Algebra F L) (_ : Algebra.IsQuadraticExtension F L),
      N ≤ Module.finrank ℚ L ∧ |(NumberField.discr L : ℝ)| ≤ C ^ Module.finrank ℚ L

end Work.CMRealSubfield
