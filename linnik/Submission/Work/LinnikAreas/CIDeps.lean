import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.NumberTheory.Linnik.tentMellin_principal
import Submission.Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto
import Submission.Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
import Submission.Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt

/-!
# `CIDeps` — imports and elementary glue for the class-identity proof

This module is the common header of the proof of `Work.LinnikAreas.ClassIdentityHyp`
(`Submission/Work/LinnikAreas/ClassIdentity.lean`): it collects the analytic inputs from
`Submission/Commons` and proves the elementary translations between the Mathlib/Commons
conventions and the ones used in `Submission/Work/LinnikAreas/Setup.lean`.

Note (import constraint): the two family modules `...Linnik.logDeriv_pf_identity` and
`...Linnik.completedL_pf_identity_rect` both define `Commons.NumberTheory.Linnik.pfP`, so they
must not be imported together.  The modules imported here all belong to the
`completedL_pf_identity_rect` family.
-/

open DirichletCharacter Complex
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace Work.LinnikAreas

/-- The tent weight with `L = 11/2`, `K = 3/10`. -/
abbrev tentW (x : ℝ) : ℝ := Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10) x

/-- The trivial Dirichlet character is the indicator of the units. -/
lemma one_apply_eq_indicator {q : ℕ} (x : ZMod q) :
    (1 : DirichletCharacter ℂ q) x = if IsUnit x then 1 else 0 := by
  by_cases h : IsUnit x
  · rw [if_pos h, MulChar.one_apply h]
  · rw [if_neg h, MulChar.map_nonunit _ h]

/-- `a.Coprime q` makes `a` a unit of `ZMod q`. -/
lemma isUnit_of_coprime {q a : ℕ} (ha : a.Coprime q) : IsUnit ((a : ZMod q)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact ha

/-- The congruence `p ≡ a [MOD q]` is equality in `ZMod q`. -/
lemma modEq_iff_zmod_eq {q a p : ℕ} : p ≡ a [MOD q] ↔ (p : ZMod q) = (a : ZMod q) :=
  (ZMod.natCast_eq_natCast_iff p a q).symm

/-- The principal character at a natural number, in terms of coprimality. -/
lemma one_apply_natCast {q n : ℕ} :
    (1 : DirichletCharacter ℂ q) ((n : ℕ) : ZMod q) = if Nat.Coprime n q then 1 else 0 := by
  rw [one_apply_eq_indicator]
  by_cases h : Nat.Coprime n q
  · rw [if_pos h, if_pos]
    rw [ZMod.isUnit_iff_coprime]
    exact h
  · rw [if_neg h, if_neg]
    rw [ZMod.isUnit_iff_coprime]
    exact h

/-- `Finset.Icc 1 X = Finset.Ioc 0 X` as finsets of natural numbers. -/
lemma Icc_one_eq_Ioc_zero (X : ℕ) : Finset.Icc 1 X = Finset.Ioc 0 X := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- The conjugate of the value of a Dirichlet character at a unit is its value at the inverse. -/
lemma star_apply_eq_inv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {a : ZMod q}
    (ha : IsUnit a) : starRingEnd ℂ (χ a) = χ a⁻¹ := by
  have hnorm : ‖χ a‖ = 1 := by
    have h : χ a = χ (ha.unit : ZMod q) := by rw [ha.unit_spec]
    rw [h]
    exact DirichletCharacter.unit_norm_eq_one χ ha.unit
  have hmul : χ a * χ a⁻¹ = 1 := by
    rw [← map_mul, mul_comm, a.inv_mul_of_unit ha, map_one]
  have hne : χ a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact one_ne_zero hmul.symm
  have h2 : χ a⁻¹ = (χ a)⁻¹ := by
    have h3 := congrArg (fun z => (χ a)⁻¹ * z) hmul
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul, mul_one] at h3
    exact h3
  calc starRingEnd ℂ (χ a) = (χ a)⁻¹ := (Complex.inv_eq_conj hnorm).symm
    _ = χ a⁻¹ := h2.symm

end Work.LinnikAreas
