import Mathlib
import Submission.Work.Analysis.Paraproduct.TensorNorm

/-!
# Minkowski's inequality for the normalised finite `L^p` norm

`lpNormFin α p` (defined in `Submission.Work.Analysis.Paraproduct.TensorNorm`) is the normalised
`L^p` norm of a function `α → ℂ` on a finite type `α` equipped with the uniform probability
measure:
`‖f‖_p = (N⁻¹ ∑_a ‖f a‖^p)^{1/p}`, `N = card α`.

This file proves that it is subadditive for `1 ≤ p`.

The proof passes to the `ℝ≥0`-valued version `lpNormFinNN`, where `NNReal.Lp_add_le`
(Minkowski's inequality for finite sums in `ℝ≥0`) applies verbatim, and then transfers the
inequality back along the coercion `ℝ≥0 → ℝ`.
-/

namespace Work.Analysis.Paraproduct

open Finset
open scoped NNReal

noncomputable section

/-- The `ℝ≥0`-valued version of the normalised `L^p` norm: `(N⁻¹ ∑_a ‖h a‖^p)^{1/p}` with all
quantities computed in `ℝ≥0`.  Its coercion to `ℝ` is `lpNormFin`. -/
noncomputable def lpNormFinNN (α : Type*) [Fintype α] (p : ℝ) (h : α → ℂ) : ℝ≥0 :=
  ((Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖h a‖₊) ^ p) ^ (1 / p)

/-- The `ℝ≥0`-valued norm `lpNormFinNN` is the normalised `L^p` norm `lpNormFin`. -/
lemma coe_lpNormFinNN {α : Type*} [Fintype α] (p : ℝ) (h : α → ℂ) :
    ((lpNormFinNN α p h : ℝ≥0) : ℝ) = lpNormFin α p h := by
  simp only [lpNormFinNN, lpNormFin, NNReal.coe_rpow, NNReal.coe_mul, NNReal.coe_inv,
    NNReal.coe_sum, NNReal.coe_natCast, coe_nnnorm]

/-- **Minkowski's inequality** for the `ℝ≥0`-valued normalised `L^p` norm: it is subadditive
for `1 ≤ p`. -/
lemma lpNormFinNN_add_le {α : Type*} [Fintype α] {p : ℝ} (hp : 1 ≤ p) (f g : α → ℂ) :
    lpNormFinNN α p (f + g) ≤ lpNormFinNN α p f + lpNormFinNN α p g := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 ≤ 1 / p := by positivity
  -- Pointwise triangle inequality, in `ℝ≥0`.
  have hpt : ∀ a, (‖(f + g) a‖₊ : ℝ≥0) ≤ ‖f a‖₊ + ‖g a‖₊ := by
    intro a
    simpa only [Pi.add_apply] using nnnorm_add_le (f a) (g a)
  have hsum : (∑ a, (‖(f + g) a‖₊ : ℝ≥0) ^ p) ≤ ∑ a, (‖f a‖₊ + ‖g a‖₊) ^ p :=
    Finset.sum_le_sum fun a _ => NNReal.rpow_le_rpow (hpt a) hp0.le
  have hstep : (Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖(f + g) a‖₊ : ℝ≥0) ^ p
      ≤ (Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖f a‖₊ + ‖g a‖₊) ^ p :=
    mul_le_mul_of_nonneg_left hsum zero_le
  -- Minkowski's inequality for finite sums in `ℝ≥0`.
  have hM : (∑ a, (‖f a‖₊ + ‖g a‖₊) ^ p) ^ (1 / p)
      ≤ (∑ a, (‖f a‖₊ : ℝ≥0) ^ p) ^ (1 / p) + (∑ a, (‖g a‖₊ : ℝ≥0) ^ p) ^ (1 / p) := by
    simpa using NNReal.Lp_add_le Finset.univ (fun a => ‖f a‖₊) (fun a => ‖g a‖₊) hp
  calc lpNormFinNN α p (f + g)
      = ((Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖(f + g) a‖₊ : ℝ≥0) ^ p) ^ (1 / p) := rfl
    _ ≤ ((Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖f a‖₊ + ‖g a‖₊) ^ p) ^ (1 / p) :=
        NNReal.rpow_le_rpow hstep hr
    _ = (Fintype.card α : ℝ≥0)⁻¹ ^ (1 / p)
          * (∑ a, (‖f a‖₊ + ‖g a‖₊) ^ p) ^ (1 / p) := by rw [NNReal.mul_rpow]
    _ ≤ (Fintype.card α : ℝ≥0)⁻¹ ^ (1 / p)
          * ((∑ a, (‖f a‖₊ : ℝ≥0) ^ p) ^ (1 / p)
            + (∑ a, (‖g a‖₊ : ℝ≥0) ^ p) ^ (1 / p)) :=
        mul_le_mul_of_nonneg_left hM zero_le
    _ = ((Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖f a‖₊ : ℝ≥0) ^ p) ^ (1 / p)
          + ((Fintype.card α : ℝ≥0)⁻¹ * ∑ a, (‖g a‖₊ : ℝ≥0) ^ p) ^ (1 / p) := by
        rw [mul_add, ← NNReal.mul_rpow, ← NNReal.mul_rpow]
    _ = lpNormFinNN α p f + lpNormFinNN α p g := rfl

/-- **Minkowski's inequality** for the normalised `L^p` norm on a finite type: for `1 ≤ p`,
`‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p`. -/
theorem lpNormFin_add_le {α : Type*} [Fintype α] {p : ℝ} (hp : 1 ≤ p) (f g : α → ℂ) :
    lpNormFin α p (f + g) ≤ lpNormFin α p f + lpNormFin α p g := by
  have key := lpNormFinNN_add_le hp f g
  calc lpNormFin α p (f + g)
      = ((lpNormFinNN α p (f + g) : ℝ≥0) : ℝ) := (coe_lpNormFinNN p (f + g)).symm
    _ ≤ ((lpNormFinNN α p f + lpNormFinNN α p g : ℝ≥0) : ℝ) := by
        exact_mod_cast key
    _ = lpNormFin α p f + lpNormFin α p g := by
        rw [NNReal.coe_add, coe_lpNormFinNN, coe_lpNormFinNN]

end

end Work.Analysis.Paraproduct
