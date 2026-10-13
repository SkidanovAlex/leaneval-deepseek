/-
# `Work.FTS.RegPkgGal.R2.integrableOn_pth_slice`

The angular slice `θ ↦ ∂_θ g (z, θ)` of the perturbation is integrable on `Iθ = [0, π/2]`,
for `0 < α ≤ 1`, `z > 0`, whenever the *weighted* angular derivative is controlled by
`Cθ z² (sin θ cos²θ)^α`:

  `|D_θ g (z,θ)| ≤ Cθ · z² · (sin θ · cos² θ)^α`,  `D_θ = sin(2θ) ∂_θ`.

Since `sin(2θ) > 0` on `(0, π/2)`, this is the pointwise bound

  `|∂_θ g (z,θ)| ≤ Cθ z² · (sin θ cos²θ)^α / sin(2θ)`

on the *open* interval, and the two endpoints are null.  The whole content is therefore the
integrability of the explicit majorant `θ ↦ (sin θ cos²θ)^α / sin(2θ)`: near `θ = 0` the
numerator behaves like `θ^α` while `sin(2θ) ≈ 2θ`, giving `θ^{α-1}`, and near `θ = π/2`
(with `δ = π/2 - θ`) the numerator behaves like `δ^{2α}` while `sin(2θ) ≈ 2δ`, giving
`δ^{2α-1}`; both are integrable because `α > 0`.

The proof of the majorant bound is elementary:

* `sin θ cos²θ ≤ sin(2θ)` (as `cos θ ≤ 1 ≤ 2`), so `(sin θ cos²θ)^α ≤ sin(2θ)^α`;
* hence `(sin θ cos²θ)^α / sin(2θ) ≤ sin(2θ)^{α-1} ≤ sin(2θ)^{α/2-1}` because
  `sin(2θ) ≤ 1` and `α - 1 ≥ α/2 - 1`;
* finally `sin(2θ)^{-(1-α/2)} ≤ (π/4)^{1-α/2} (θ^{-(1-α/2)} + (π/2-θ)^{-(1-α/2)})` is the
  Jordan-type estimate `Work.Spaces.sin_rpow_le_majorant`, and the right-hand side is integrable
  with exponent `p = 1 - α/2 ∈ (0,1)` (`Work.Spaces.integrableOn_majorant_rpow`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_rpow_le_majorant
import Submission.Work.Spaces.integrableOn_majorant_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.FTS.RegPkgGal.R2

/-! ## Elementary facts about the angular interval -/

/-- `sin θ cos²θ ≤ sin(2θ)` for `θ ∈ (0, π/2)`: pointwise `cos²θ ≤ cos θ ≤ 2cos θ` and
`sin θ ≥ 0`. -/
lemma sin_mul_cos_sq_le_sin_two {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2*θ) := by
  have hs0 : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcs : Real.cos θ ^ 2 ≤ 2 * Real.cos θ := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1), hc0]
  rw [Real.sin_two_mul]
  calc Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * (2 * Real.cos θ) :=
        mul_le_mul_of_nonneg_left hcs hs0
    _ = 2 * Real.sin θ * Real.cos θ := by ring

/-- `sin(2θ) > 0` on the open interval `(0, π/2)`. -/
lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The explicit integrable majorant -/

/-- **The majorant estimate.**  For `0 < α ≤ 1` and `θ ∈ (0, π/2)`,

  `(sin θ cos²θ)^α / sin(2θ) ≤ (π/4)^{1-α/2} (θ^{-(1-α/2)} + (π/2-θ)^{-(1-α/2)})`. -/
lemma sin_mul_cos_sq_pow_div_le_sin_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ)
      ≤ (Real.pi/4)^(1-α/2) * (θ^(-(1-α/2)) + (Real.pi/2-θ)^(-(1-α/2))) := by
  have hs : 0 < Real.sin (2*θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have hs0 : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hA0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (sq_nonneg _)
  have hA : (Real.sin θ * Real.cos θ ^ 2)^α ≤ (Real.sin (2*θ))^α :=
    Real.rpow_le_rpow hA0 (sin_mul_cos_sq_le_sin_two hθ) (le_of_lt hα)
  have h2 : (Real.sin (2*θ))^α / Real.sin (2*θ) = (Real.sin (2*θ))^(α-1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hs]
    congr 1
  have h3 : (Real.sin (2*θ))^(α-1) ≤ (Real.sin (2*θ))^(α/2-1) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have h4 : (Real.sin (2*θ))^(α/2-1) = (Real.sin (2*θ))^(-(1-α/2)) := by
    congr 1; ring
  calc (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ)
      ≤ (Real.sin (2*θ))^α / Real.sin (2*θ) := div_le_div_of_nonneg_right hA hs.le
    _ = (Real.sin (2*θ))^(α-1) := h2
    _ ≤ (Real.sin (2*θ))^(α/2-1) := h3
    _ = (Real.sin (2*θ))^(-(1-α/2)) := h4
    _ ≤ (Real.pi/4)^(1-α/2) * (θ^(-(1-α/2)) + (Real.pi/2-θ)^(-(1-α/2))) :=
        Work.Spaces.sin_rpow_le_majorant (1-α/2) θ (by linarith) ⟨hθ.1.le, hθ.2.le⟩

/-- The function `θ ↦ (sin θ cos²θ)^α / sin(2θ)` is integrable on `Iθ` for `0 < α ≤ 1`. -/
lemma integrableOn_sin_mul_cos_sq_pow_div {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ))
      (Set.Icc (0:ℝ) (Real.pi/2)) := by
  have hIoo : MeasureTheory.volume.restrict (Set.Icc (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  set r : ℝ := 1 - α/2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  set M : ℝ → ℝ := fun θ => (Real.pi/4)^r * (θ^(-r) + (Real.pi/2-θ)^(-r)) with hMdef
  have hMaj : MeasureTheory.IntegrableOn M (Set.Icc (0:ℝ) (Real.pi/2)) := by
    have h := Work.Spaces.integrableOn_majorant_rpow r hr0 hr1
    rw [hMdef]
    exact h
  change MeasureTheory.Integrable
    (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ))
    (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) (Real.pi/2)))
  rw [hIoo]
  refine MeasureTheory.Integrable.mono'
    (f := fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ)) (g := M) ?_ ?_ ?_
  · exact hMaj.mono_set Set.Ioo_subset_Icc_self
  · -- a.e. strong measurability: continuity on the open interval
    have hcont : ContinuousOn
        (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ))
        (Set.Ioo (0:ℝ) (Real.pi/2)) := by
      have hnum : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2)^α)
          (Set.Ioo (0:ℝ) (Real.pi/2)) := by
        apply ContinuousOn.rpow_const
        · fun_prop
        · intro θ hθ
          exact Or.inl (ne_of_gt (mul_pos
            (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
            (pow_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩) 2)))
      exact hnum.div ((Real.continuous_sin.comp
        (continuous_const.mul continuous_id)).continuousOn) (fun θ hθ =>
          ne_of_gt (sin_two_pos_of_mem_Ioo hθ))
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg
      (mul_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos]))) (sq_nonneg _)) _)
      (le_of_lt (sin_two_pos_of_mem_Ioo hθ))), hMdef, hrdef]
    exact sin_mul_cos_sq_pow_div_le_sin_two hα hα1 hθ

/-! ## The pointwise bound on the slice -/

/-- On the open interval, `∂_θ g` is bounded by the weighted derivative divided by `sin(2θ)`. -/
lemma abs_pth_le_div {α Cθ z θ : ℝ} {g : ℝ → ℝ → ℝ}
    (hd : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    |Work.Spaces.pth g z θ| ≤ Cθ * z ^ 2 *
      ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) := by
  have hs : 0 < Real.sin (2*θ) := sin_two_pos_of_mem_Ioo hθ
  have h1 : |Work.Spaces.pth g z θ| = |Work.Spaces.Dth g z θ| / Real.sin (2*θ) := by
    rw [Work.Spaces.Dth, abs_mul, abs_of_pos hs]
    exact (mul_div_cancel_left₀ _ (ne_of_gt hs)).symm
  calc |Work.Spaces.pth g z θ| = |Work.Spaces.Dth g z θ| / Real.sin (2*θ) := h1
    _ ≤ (Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α) / Real.sin (2*θ) :=
        div_le_div_of_nonneg_right (hd θ ⟨hθ.1.le, hθ.2.le⟩) hs.le
    _ = Cθ * z ^ 2 * ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) := by ring

/-! ## Continuity of the slice -/

/-- The slice `θ ↦ ∂_θ g (z, θ)` is continuous on the open angular interval, by differentiating
the `C¹` function `s ↦ g z s`. -/
lemma continuousOn_pth_slice {g : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)))) :
    ContinuousOn (fun θ => Work.Spaces.pth g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  have hcomp : ContDiffOn ℝ 1 (fun s : ℝ => g z s) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    have hslice : ContDiffOn ℝ 1 (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi/2)) := by fun_prop
    have hmap : Set.MapsTo (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi/2))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := fun s hs => ⟨hz, hs⟩
    have h2 := hsm.comp hslice hmap
    simpa [Function.comp_def, Function.uncurry] using h2
  have h := hcomp.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num : (1:WithTop ℕ∞) ≤ 1)
  simpa [Work.Spaces.pth] using h

/-! ## The target -/

theorem integrableOn_pth_slice {α Cθ z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCθ : 0 ≤ Cθ)
    (hz : 0 < z) {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.pth g z s)
      (Set.Icc 0 (Real.pi / 2)) MeasureTheory.volume := by
  -- work on the open interval: the two endpoints are null
  have hIoo : MeasureTheory.volume.restrict (Set.Icc (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  set r : ℝ := 1 - α/2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hcz : 0 ≤ Cθ * z^2 := mul_nonneg hCθ (sq_nonneg z)
  -- the integrable majorant `Cθ z² · (π/4)^r (θ^{-r} + (π/2-θ)^{-r})`
  set M : ℝ → ℝ := fun θ => Cθ * z^2 * ((Real.pi/4)^r * (θ^(-r) + (Real.pi/2-θ)^(-r)))
    with hMdef
  have hMaj : MeasureTheory.IntegrableOn M (Set.Icc (0:ℝ) (Real.pi/2)) := by
    have h := (Work.Spaces.integrableOn_majorant_rpow r hr0 hr1).integrable.const_mul (Cθ * z^2)
    rw [hMdef]
    exact h
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => Work.Spaces.pth g z s) (g := M) ?_ ?_ ?_
  · -- the majorant is integrable (on the open interval, by restriction)
    rw [hIoo]
    exact hMaj.mono_set Set.Ioo_subset_Icc_self
  · -- a.e. strong measurability of the slice
    rw [hIoo]
    exact (continuousOn_pth_slice hz hsm).aestronglyMeasurable measurableSet_Ioo
  · -- the a.e. pointwise bound
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    calc |Work.Spaces.pth g z θ| ≤ Cθ * z ^ 2 *
          ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) :=
          abs_pth_le_div hd hθ
      _ ≤ M θ := by
          rw [hMdef, hrdef]
          exact mul_le_mul_of_nonneg_left
            (sin_mul_cos_sq_pow_div_le_sin_two hα hα1 hθ) hcz

end Work.FTS.RegPkgGal.R2
