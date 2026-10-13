/-
# `Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_w_sq_of`

Honesty of the radial weight `w(z) = (1+z)²/z²` on `(0,∞)`:

  `∫_0^∞ u(t)² · w(t)² dt < ∞`

from a **near** `L²`-condition on `u` (`∫_0^1 u²/t⁴ < ∞`) and a **far** `L²`-condition
(`∫_1^∞ u² < ∞`).  No pointwise decay of `u` is assumed.

**Proof.**  `w(t)² = (1+t)⁴/t⁴`.

* On `(0,1)`: `(1+t)⁴ ≤ 16`, so `u²w² = (1+t)⁴·(u²/t⁴) ≤ 16·u²/t⁴`; this is the
  `Integrable.bdd_mul` step (the bounded continuous factor `(1+t)⁴` times the integrable
  `u²/t⁴`).
* On `(1,∞)`: `1+t ≤ 2t`, so `(1+t)⁴/t⁴ ≤ 16`; the bounded factor is now
  `w(·)²` (continuous on `(1,∞)`, hence a.e. strongly measurable) times the integrable
  `u²`.
* The two halves are glued with `IntegrableOn.union` over
  `(0,1) ∪ (1,∞) = (0,∞)` up to the null sets `{0}, {1}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped Topology

theorem integrableOn_sq_mul_w_sq_of {u : ℝ → ℝ}
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) := by
  have hw : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
    intro z
    unfold Work.Spaces.w
    rw [div_pow, show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring,
      show (z ^ 2) ^ 2 = z ^ 4 by ring]
  -- **Near `0`**: `(1+z)⁴ ≤ 16` on `(0,1)`, so the weight is a bounded multiple of `1/z⁴`.
  have hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioo (0 : ℝ) 1) := by
    have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ‖(fun z : ℝ => (1 + z) ^ 4) z‖ ≤ 16 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine ae_of_all _ fun z hz => ?_
      have h0 : (0 : ℝ) ≤ 1 + z := by linarith [hz.1]
      have h2' : 1 + z ≤ 2 := by linarith [hz.2]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h2' 4
        _ = 16 := by norm_num
    have hmeas : AEStronglyMeasurable (fun z : ℝ => (1 + z) ^ 4)
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      ((continuous_const.add continuous_id).pow 4).continuousOn.aestronglyMeasurable
        measurableSet_Ioo
    have h := Integrable.bdd_mul h1 hmeas hbdd
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioo
    intro z _
    show (1 + z) ^ 4 * ((u z) ^ 2 / z ^ 4) = (u z) ^ 2 * (Work.Spaces.w z) ^ 2
    rw [hw z]; ring
  -- **Far `∞`**: `(1+z)⁴/z⁴ ≤ 16` on `(1,∞)`, so the weight is a bounded factor.
  have hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi (1 : ℝ)) := by
    have hw2 : ∀ z : ℝ, 1 < z → (Work.Spaces.w z) ^ 2 ≤ 16 := by
      intro z hz
      rw [hw z, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 4)]
      have h0 : (0 : ℝ) ≤ 1 + z := by linarith
      have hle : 1 + z ≤ 2 * z := by linarith
      calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 hle 4
        _ = 16 * z ^ 4 := by ring
    have hbdd : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖(fun z : ℝ => (Work.Spaces.w z) ^ 2) z‖ ≤ 16 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hw2 z hz
    have hcontw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi (1 : ℝ)) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ?_ ?_ ?_
      · exact ((continuous_const.add continuous_id).pow 2).continuousOn
      · exact (continuous_id.pow 2).continuousOn
      · intro z hz
        exact pow_ne_zero 2 (ne_of_gt (lt_trans one_pos hz))
    have hmeas : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi (1 : ℝ))) := (hcontw.pow 2).aestronglyMeasurable measurableSet_Ioi
    have h := Integrable.bdd_mul h2 hmeas hbdd
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro z _
    show (Work.Spaces.w z) ^ 2 * (u z) ^ 2 = (u z) ^ 2 * (Work.Spaces.w z) ^ 2
    ring
  -- **Glue** `(0,1)` and `(1,∞)` across the null set `{1}`.
  have hA : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfar.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨ha, _⟩ | h3) <;> linarith
    · intro hx
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨hx, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.PhiStar.Honesty
