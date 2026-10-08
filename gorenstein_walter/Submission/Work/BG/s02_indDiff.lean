import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lemma13
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge

/-!
# Area BG: input I-1 to Bender–Glauberman's Coherence Theorem 2.3

`IndDiffProp C` is the statement I-1 of `NOTES_BG.md`: for a `Λ`-orbit of
`Irr(H₀)` the *differences* of equivalent irreducibles induce to virtual characters of
degree `0`, i.e. for `μ, ν ∈ Irr(H₀)` with `ν = λ_β · μ` (`λ_β ∈ Λ`):

* `(μ - ν)^G ∈ ℤ[Irr G]`, and
* `(μ - ν)^G(1) = 0`.

Both halves are formal consequences of the character library of the Feit–Thompson
closure, with no group-theoretic input beyond the definition of `Λ`:

* The first half needs *no* hypothesis on the pair `(μ, ν)` at all: `Z = ZIrr G` is the
  `ℤ`-span of `Irr G`, the two summands `μ`, `ν` are irreducible hence lie in
  `ZIrr ↥H₀`, and induction `Ind_{H₀}^{G}` maps `ℤ[Irr H₀]` into `ℤ[Irr G]`
  (`ClassFunction.induce_mem_ZIirr`).  (`LamEquiv` is genuinely used only in the second
  half; keeping it in the hypothesis costs nothing — it is the useful extra datum for
  the consumers of I-1, and it is what makes the degree vanish.)
* The second half is the degree formula `(μ - ν)^G(1) = [G : H₀] · (μ - ν)(1)`
  (`ClassFunction.induce_apply_one`) together with `ν(1) = λ_β(1)·μ(1) = μ(1)`:
  a member of `Λ` is inflated from a linear character of `H₀/U`, hence has degree `1`
  (`λ_β(1) = 1`).  So `(μ - ν)(1) = 0`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

theorem s02_indDiff {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.IndDiffProp C := by
  classical
  intro μ ν hμ hν hlam
  constructor
  · -- `μ - ν ∈ ℤ[Irr H₀]` and induction preserves `ℤ[Irr -]`.
    exact ClassFunction.induce_mem_ZIrr C.P.H0
      (Submodule.sub_mem _ (IsIrreducibleCharacter.mem_ZIrr hμ)
        (IsIrreducibleCharacter.mem_ZIrr hν))
  · -- The degree: `ν = λ_β μ` with `λ_β` of degree `1`.
    obtain ⟨β, hβ⟩ := hlam
    have h1 : Work.BG.lamCF C β (1 : ↥C.P.H0) = 1 := by
      simp [Work.BG.lamCF]
    have h0 : (μ - ν) (1 : ↥C.P.H0) = 0 := by
      rw [hβ, ClassFunction.sub_apply, ClassFunction.mul_apply, h1, one_mul, sub_self]
    rw [ClassFunction.induce_apply_one, h0, mul_zero]

end Work.BG
