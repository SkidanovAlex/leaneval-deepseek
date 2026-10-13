import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.FireFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

set_option linter.unusedVariables false

namespace Work.FTS.FireFix.Clauses.PsiWt

/-!
# Integrability of the ψ-weight singularity

The angular factor of the ψ-weight of the physical reconstruction is
`θ ↦ (sin |θ|)^{α-1} (cos θ)^{2α}`; the exponent `α - 1 ∈ (-1, 0)` makes it
non-integrable at the origin of the `θ`-line, and the radial cutoff
`z ↦ if z ≤ L then 1 else 0` makes the `z`-integral finite.  This file proves the
resulting two-dimensional integrability on `(0, ∞) × (-π/2, π/2)`.

The mathematical content is elementary: near `θ = 0` the integrand is comparable
to `|θ|^{α - 1}` (since `sin |θ| ≥ (2/π)|θ|`), which is integrable because
`α > 0`, and the cosine factor is bounded; the cutoff factor is the indicator of
the bounded interval `(0, L]`.
-/

/-- The angular factor `θ ↦ (sin |θ|)^{α-1} (cos θ)^{2α}` is integrable on the symmetric
interval `(-π/2, π/2)`: at the origin it is dominated by `(2/π)^{α-1} |θ|^{α-1}`, which is
integrable since `α - 1 > -1`, and the cosine factor is bounded by `1`. -/
theorem integrableOn_sin_abs_rpow_mul_cos_rpow_angle {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α))
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  -- the positive half, where `|y| = y`
  have hθpos : IntegrableOn (fun y : ℝ => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α))
      (Set.Ioo 0 (Real.pi / 2)) volume := by
    have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
    have hrpow : IntegrableOn (fun y : ℝ => y ^ (α - 1)) (Set.Ioo 0 (Real.pi / 2)) volume :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hpi).mpr (by linarith)
    have hM : IntegrableOn (fun y : ℝ => (2 / Real.pi) ^ (α - 1) * y ^ (α - 1))
        (Set.Ioo 0 (Real.pi / 2)) volume := Integrable.const_mul hrpow _
    refine Integrable.mono' hM ?_ ?_
    · exact (((Real.measurable_sin.comp measurable_abs).pow_const (α - 1)).mul
        (Real.measurable_cos.pow_const (2 * α))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have htp : t < Real.pi / 2 := ht.2
      rw [abs_of_pos ht0]
      have hsin_pos : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
      have h2pi : (0 : ℝ) < 2 / Real.pi := by positivity
      have hsin_ge : 2 / Real.pi * t ≤ Real.sin t := Real.mul_le_sin ht0.le htp.le
      have hrpow_le : (Real.sin t) ^ (α - 1) ≤ (2 / Real.pi * t) ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos h2pi ht0) hsin_ge (by linarith)
      rw [Real.mul_rpow h2pi.le ht0.le] at hrpow_le
      have hcos_pos : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩
      have hcos_le : (Real.cos t) ^ (2 * α) ≤ 1 :=
        Real.rpow_le_one hcos_pos.le (Real.cos_le_one t) (by linarith)
      have hsin_nn : 0 ≤ (Real.sin t) ^ (α - 1) := Real.rpow_nonneg hsin_pos.le _
      have hcos_nn : 0 ≤ (Real.cos t) ^ (2 * α) := Real.rpow_nonneg hcos_pos.le _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsin_nn hcos_nn)]
      calc (Real.sin t) ^ (α - 1) * (Real.cos t) ^ (2 * α)
          ≤ ((2 / Real.pi) ^ (α - 1) * t ^ (α - 1)) * 1 :=
            mul_le_mul hrpow_le hcos_le hcos_nn
              (le_of_lt (mul_pos (Real.rpow_pos_of_pos h2pi _) (Real.rpow_pos_of_pos ht0 _)))
        _ = (2 / Real.pi) ^ (α - 1) * t ^ (α - 1) := by ring
  set f : ℝ → ℝ := fun y => (Real.sin |y|) ^ (α - 1) * (Real.cos y) ^ (2 * α) with hf
  have hpos' : IntegrableOn f (Set.Ioo 0 (Real.pi / 2)) := hθpos
  -- the negative half, obtained from the positive one by the reflection `y ↦ -y`, using
  -- that `f` is even
  have hneg : IntegrableOn f (Set.Ioo (-(Real.pi / 2)) 0) := by
    have hset : Neg.neg '' Set.Ioo 0 (Real.pi / 2) = Set.Ioo (-(Real.pi / 2)) 0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
      · intro hx
        exact ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by simp⟩
    have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_image
      (Homeomorph.neg ℝ).measurableEmbedding (f := f) (s := Set.Ioo 0 (Real.pi / 2))
    rw [show Set.Ioo (-(Real.pi / 2)) 0 = Neg.neg '' Set.Ioo 0 (Real.pi / 2) from hset.symm]
    refine hiff.mpr ?_
    exact IntegrableOn.congr_fun hpos'
      (fun y _ => by simp [f, Function.comp_apply]) measurableSet_Ioo
  -- the origin is a null set
  have hsingle : IntegrableOn f ({0} : Set ℝ) := IntegrableOn.of_measure_zero (by simp)
  have hun : IntegrableOn f (Set.Ioo (-(Real.pi / 2)) 0 ∪ ({0} ∪ Set.Ioo 0 (Real.pi / 2))) :=
    IntegrableOn.union hneg (IntegrableOn.union hsingle hpos')
  have hset2 : Set.Ioo (-(Real.pi / 2)) 0 ∪ ({0} ∪ Set.Ioo 0 (Real.pi / 2))
      = Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro (⟨h1, h2⟩ | rfl | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      · exact ⟨by linarith, h2⟩
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h, h2⟩)
  rwa [hset2] at hun

/-- The cutoff factor `x ↦ if x ≤ L then 1 else 0` is integrable on the half line `(0, ∞)`:
it is the indicator of the bounded interval `(0, L]`. -/
theorem integrable_cutoff_Ioi (L : ℝ) :
    Integrable (fun x : ℝ => if x ≤ L then (1 : ℝ) else 0) (volume.restrict (Set.Ioi 0)) := by
  have hIoc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 L) volume := by
    apply integrableOn_const
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · simp
  have hkey : Set.Ioc (0 : ℝ) L ∩ Set.Ioi 0 = Set.Ioc 0 L := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩; exact h1
    · intro h; exact ⟨h, h.1⟩
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 L) (volume.restrict (Set.Ioi 0)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, hkey]
    exact hIoc
  have h3 : Integrable ((Set.Ioc 0 L).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume.restrict (Set.Ioi 0)) := (integrable_indicator_iff measurableSet_Ioc).2 h2
  refine Integrable.congr h3 ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : (0 : ℝ) < x := Set.mem_Ioi.mp hx
  have hiff : (x ∈ Set.Ioc (0 : ℝ) L) ↔ x ≤ L :=
    ⟨fun h => h.2, fun h => ⟨hx', h⟩⟩
  simp only [Set.indicator_apply]
  by_cases h : x ≤ L
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (hiff.mp hc)), ite_eq_right h]

theorem integrableOn_sin_rpow_mul_cos_rpow {α L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3)
    (hL : 0 ≤ L) :
    MeasureTheory.IntegrableOn (fun q : ℝ × ℝ =>
      (Real.sin |q.2|) ^ (α - 1) * (Real.cos q.2) ^ (2 * α)
        * (if q.1 ≤ L then (1 : ℝ) else 0))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hθ := integrableOn_sin_abs_rpow_mul_cos_rpow_angle hα hα1
  have hz := integrable_cutoff_Ioi L
  -- the product measure on the rectangle is the product of the restricted measures
  change Integrable _ ((Measure.prod volume volume).restrict
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
  rw [← Measure.prod_restrict]
  refine Integrable.congr (Integrable.mul_prod hz hθ) ?_
  filter_upwards with q
  exact mul_comm _ _

end Work.FTS.FireFix.Clauses.PsiWt
