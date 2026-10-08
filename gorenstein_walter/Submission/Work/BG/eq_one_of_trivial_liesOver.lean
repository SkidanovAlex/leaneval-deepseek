import Mathlib
import Submission.Work.BG.CharBridgeClifford
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedDegreeSum

namespace Work.BG

/- **A `U`-irreducible character lying over the trivial character of a normal subgroup `K ⊴ U`
is constant on `K`** (its value at every `k ∈ K` is its degree).

By Clifford's theorem (`restrictionConstituentsSingleOrbit_of_isIrreducible`) the irreducible
constituents of `Res_K χ` form a single `U`-conjugation orbit.  Since the trivial character is
conjugation-invariant (`IrreducibleCharacter.conjBy_trivial`), the orbit of the constituent
`1_K` supplied by `hover` is the singleton `{1_K}`, so `1_K` is the *only* constituent of
`Res_K χ`.  Hence `Res_K χ = c · 1_K` for the scalar `c = ⟨Res_K χ, 1_K⟩`
(orthogonality against every other irreducible, `classFunction_eq_zero_of_orthogonal`), and
evaluating at `k` and at `1` gives `χ k = c = χ 1`. -/
open OddOrder.RepresentationTheory in
theorem eq_one_of_trivial_liesOver {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (K : Subgroup U) [K.Normal] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (χ : IrreducibleCharacter U)
    (hover : IrreducibleCharacter.LiesOver K χ (trivialIrreducibleCharacter K)) :
    ∀ k : K, (χ : ClassFunction U ℂ) (k : U) = (χ : ClassFunction U ℂ) 1 := by
  classical
  -- Clifford single-orbit: the constituents of `Res_K χ` form one `U`-conjugation orbit.
  have hsingle := restrictionConstituentsSingleOrbit_of_isIrreducible (G := U) (H := K) χ
  -- The trivial character is conjugation-invariant, so every constituent is trivial.
  have hconst : ∀ θ : IrreducibleCharacter ↥K, IrreducibleCharacter.LiesOver K χ θ →
      θ = trivialIrreducibleCharacter ↥K := by
    intro θ hθ
    obtain ⟨u, hu⟩ := hsingle.exists_conj
      (θ := trivialIrreducibleCharacter ↥K) (η := θ) hover hθ
    rw [← hu, IrreducibleCharacter.conjBy_trivial]
  -- `Res_K χ` is a scalar multiple of `1_K`.
  let c : ℂ := ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction U ℂ))
    ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) : ClassFunction ↥K ℂ)
  have hzero : ∀ θ : IrreducibleCharacter ↥K, θ ≠ trivialIrreducibleCharacter ↥K →
      ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction U ℂ))
        (θ : ClassFunction ↥K ℂ) = 0 := by
    intro θ hθ
    by_contra hne
    exact hθ (hconst θ (by
      show ClassFunction.restrictionMultiplicity K (χ : ClassFunction U ℂ)
        (θ : ClassFunction ↥K ℂ) ≠ 0
      rw [ClassFunction.restrictionMultiplicity_def]
      exact hne))
  have hdiff : ClassFunction.restrict K (χ : ClassFunction U ℂ)
      - c • ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ) = 0 := by
    refine classFunction_eq_zero_of_orthogonal _ fun θ => ?_
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
      irreducibleCharacter_inner_eq_ite (trivialIrreducibleCharacter ↥K) θ]
    by_cases h : trivialIrreducibleCharacter ↥K = θ
    · rw [if_pos h, ← h, mul_one, sub_self]
    · rw [if_neg h, mul_zero, sub_zero]
      exact hzero θ (fun hh => h hh.symm)
  have hb : ClassFunction.restrict K (χ : ClassFunction U ℂ)
      = c • ((trivialIrreducibleCharacter ↥K : IrreducibleCharacter ↥K) :
          ClassFunction ↥K ℂ) := sub_eq_zero.mp hdiff
  intro k
  have h1 : ClassFunction.restrict K (χ : ClassFunction U ℂ) k = c := by
    have h := congrArg (fun φ : ClassFunction ↥K ℂ => φ k) hb
    simpa [ClassFunction.smul_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply] using h
  have h2 : ClassFunction.restrict K (χ : ClassFunction U ℂ) 1 = c := by
    have h := congrArg (fun φ : ClassFunction ↥K ℂ => φ 1) hb
    simpa [ClassFunction.smul_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply] using h
  simpa using h1.trans h2.symm

end Work.BG
