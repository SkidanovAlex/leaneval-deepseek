import ChallengeDeps
import ChallengeDeps

/- The statements of the challenge are elaborated in the `Challenge` module, whose import set
does not contain the `CommCStarAlgebra` instance for `ℂ`.  Since the solution module imports the
submission (and hence more of Mathlib), we restore the instance priority so that the statements
of `Solution.lean` elaborate with exactly the same instances. -/
attribute [instance 9000] NormedField.toNormedCommRing

/-!
# Elementary facts about the bilinear polynomial averages

We collect the basic properties of the averaging operator `A` of `ChallengeDeps` that are used in
the reductions: measurability, dependence on `N` only through `Nat.floor N`, the triangle
inequality bound, and the comparison of the ordinary average with the average of the absolute
values.

We also introduce the real-valued companion `Ab` of `A` (for real-valued `f, g`), which is more
convenient for the maximal and variational estimates.
-/

namespace Submission

open _root_.PointwiseErgodicTheorems
set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The bilinear average depends on `N` only through its integer part. -/
lemma A_floor (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    A T N P₁ P₂ f g x = A T ((Nat.floor N : ℕ) : ℝ≥0) P₁ P₂ f g x := by
  simp only [A, Nat.floor_natCast]

/-- Measurability of the iterates of a measurable equivalence (the powers are taken in the group
of all equivalences, as in the definition of `A`). -/
lemma measurable_zpow_apply (T : 𝓧 ≃ᵐ 𝓧) (k : ℤ) : Measurable (fun x => (T ^ k : 𝓧 ≃ 𝓧) x) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · subst hm
    have h1 : (fun x => (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) x) = (⇑T)^[m] := by
      funext x
      rw [show (T ^ (m : ℤ) : 𝓧 ≃ 𝓧) = (T : 𝓧 ≃ 𝓧) ^ m from by simp [zpow_natCast]]
      simp [Equiv.Perm.coe_pow]
    rw [h1]
    exact T.measurable.iterate m
  · subst hm
    have h1 : (fun x => (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) x) = (⇑T.symm)^[m] := by
      funext x
      rw [show (T ^ (-(m : ℤ)) : 𝓧 ≃ 𝓧) = (T.symm : 𝓧 ≃ 𝓧) ^ m from by
        rw [zpow_neg, zpow_natCast, ← inv_pow]
        rfl]
      simp [Equiv.Perm.coe_pow]
    rw [h1]
    exact T.symm.measurable.iterate m

/-- The bilinear average of measurable functions is measurable. -/
lemma measurable_A (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) {f g : 𝓧 → ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (A T N P₁ P₂ f g) := by
  unfold A
  refine measurable_const.mul (Finset.measurable_sum _ (fun n _ => ?_))
  exact (hf.comp (measurable_zpow_apply T (P₁.eval (n : ℤ)))).mul
    (hg.comp (measurable_zpow_apply T (P₂.eval (n : ℤ))))

/-- The real-valued companion of `A`, for real-valued functions `f`, `g`. -/
noncomputable def Ab (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℝ) (x : 𝓧) : ℝ :=
  (Nat.floor N : ℝ)⁻¹ * ∑ n ∈ Icc 1 (Nat.floor N),
    f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)

/-- `A` applied to (coercions of) real-valued functions is the coercion of `Ab`. -/
lemma A_ofReal (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℝ) (x : 𝓧) :
    A T N P₁ P₂ (fun y => (f y : ℂ)) (fun y => (g y : ℂ)) x
      = (Ab T N P₁ P₂ f g x : ℂ) := by
  simp only [A, Ab, Complex.ofReal_mul]
  push_cast
  rfl

/-- Unfolding of `A` for `P₁ = X`. -/
lemma A_unfold (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) :
    A T N X P f g x = (Nat.floor N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 (Nat.floor N),
      f ((T ^ (n : ℤ) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) := by
  simp only [A]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => by rw [Polynomial.eval_X])

/-- The bilinear average is additive in each variable; here in the form of the difference of the
products. -/
lemma A_sub_bilin (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f f' g g' : 𝓧 → ℂ) (x : 𝓧) :
    A T N P₁ P₂ f g x - A T N P₁ P₂ f' g' x
      = A T N P₁ P₂ (f - f') g x + A T N P₁ P₂ f' (g - g') x := by
  simp only [A, Pi.sub_apply]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => by ring)

/-- The triangle inequality bound: the average of `f, g` is dominated pointwise by the average of
their absolute values. -/
lemma norm_A_le_Ab (T : 𝓧 ≃ᵐ 𝓧) {N : ℝ≥0} (hN : 1 ≤ N) (P₁ P₂ : ℤ[X]) (f g : 𝓧 → ℂ)
    (x : 𝓧) :
    ‖A T N P₁ P₂ f g x‖ ≤ Ab T N P₁ P₂ (fun y => ‖f y‖) (fun y => ‖g y‖) x := by
  have hfloor : 1 ≤ Nat.floor N := Nat.le_floor (by exact_mod_cast hN)
  have hpos : (0 : ℝ) < (Nat.floor N : ℝ) := by exact_mod_cast hfloor
  have hnorm : ‖((((Nat.floor N : ℝ))⁻¹ : ℝ) : ℂ)‖ = ((Nat.floor N : ℝ))⁻¹ := by
    simp [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  simp only [A, Ab, norm_mul]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hpos.le)
  calc ‖∑ n ∈ Icc 1 (Nat.floor N),
        f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)‖
      ≤ ∑ n ∈ Icc 1 (Nat.floor N),
          ‖f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Icc 1 (Nat.floor N),
         ‖f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)‖ * ‖g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)‖ :=
        Finset.sum_congr rfl (fun n _ => norm_mul _ _)

end PointwiseErgodicTheorems
end Submission
