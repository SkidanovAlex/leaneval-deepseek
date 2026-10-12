import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.integrableOn_sq_mul_div
import Submission.Work.BoseFixB3.CS.Pieces.integral_pos_of_support_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.avgMass_case`

Lower bound for the `ℓ`-weighted "mass" integral of the `CS` step:

for `κ := (ℓmin / 2) · ∫_{B_R} ω² · v/(v + A)`, `A := 1 / (c² ℓmin²)`, one has
`κ > 0` and `κ ≤ (ℓ/2) · ∫_{B_R} ω² · v/(v + 1/(c²ℓ²))` for every `ℓ ≥ ℓmin`.

* Positivity of `κ` (the crux): since `v ≥ 0` and `A > 0`, the pointwise zero sets of
  `ω² v` and of `ω² · v/(v+A)` agree, so their supports coincide; the set integral of a
  nonnegative integrable function is positive exactly when its support has positive
  measure, and `hJ > 0` gives that.  (`integral_pos_of_support_eq`)
* For `ℓ ≥ ℓmin > 0` the denominator `v z + 1/(c²ℓ²)` is at most `v z + A`, so the
  integrand is at least the one defining `κ`; comparison of set integrals does the rest.
-/

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Metric Filter

theorem avgMass_case (v ω : EuclideanSpace ℝ (Fin 3) → ℝ) {R ℓmin c : ℝ}
    (hR : 0 < R) (hℓmin : 0 < ℓmin) (hc : 0 < c)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.Integrable v)
    (hv_supp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0)
    (hωm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hω0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), 0 ≤ ω z)
    (hω1 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))), ω z ≤ 1)
    (hJ : 0 < ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R, (ω z) ^ 2 * v z) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ℓ : ℝ, ℓmin ≤ ℓ →
      κ ≤ (ℓ / 2) * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        (ω z) ^ 2 * (v z / (v z + 1 / (c ^ 2 * ℓ ^ 2))) := by
  -- `ω² ≤ 1` almost everywhere, from `0 ≤ ω ≤ 1`.
  have hω2le1 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      (ω z) ^ 2 ≤ 1 := by
    filter_upwards [hω0, hω1] with z h0 h1
    have h := mul_self_le_mul_self h0 h1
    simpa [pow_two] using h
  -- Integrability of `ω² v` and of `ω² v/(v+A)` on the ball.
  have hf_int : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * v z) MeasureTheory.volume := by
    refine MeasureTheory.Integrable.mono' hv1 ((hωm.pow 2).mul hv1.aestronglyMeasurable) ?_
    filter_upwards [hω2le1] with z hz
    have hvz : 0 ≤ v z := hv z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hvz)]
    have h := mul_le_mul_of_nonneg_right hz hvz
    simpa using h
  have hf_intOn : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * v z)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) MeasureTheory.volume := hf_int.integrableOn
  have hf_nn : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)] (fun z => (ω z) ^ 2 * v z) :=
    Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hv z))
  -- The reference denominator `A := 1/(c² ℓmin²)`.
  set A : ℝ := 1 / (c ^ 2 * ℓmin ^ 2) with hAdef
  have hApos : 0 < A := by
    rw [hAdef]; exact one_div_pos.mpr (mul_pos (pow_pos hc 2) (pow_pos hℓmin 2))
  -- The reference quantity `m := ∫_{B_R} ω² v/(v+A)`, the heart of `κ`.
  set m : ℝ := ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      (ω z) ^ 2 * (v z / (v z + A)) with hmdef
  have hgi : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * (v z / (v z + A)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) MeasureTheory.volume :=
    integrableOn_sq_mul_div v ω hApos hv hv1 hωm hω0 hω1
  -- The zero sets of `ω² v` and of `ω² v/(v+A)` agree pointwise.
  have hfg : ∀ z : EuclideanSpace ℝ (Fin 3),
      (ω z) ^ 2 * v z = 0 ↔ (ω z) ^ 2 * (v z / (v z + A)) = 0 := by
    intro z
    have hvz : 0 ≤ v z := hv z
    have hden : v z + A ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hvz hApos)
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · rw [mul_eq_zero]; left; exact h1
      · rw [mul_eq_zero]; right; rw [div_eq_zero_iff]; left; exact h1
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · rw [mul_eq_zero]; left; exact h1
      · rw [mul_eq_zero]; right
        rcases (div_eq_zero_iff.mp h1) with h2 | h2
        · exact h2
        · exact absurd h2 hden
  -- Positivity of `m`, the crux.
  have hm_pos : 0 < m := by
    rw [hmdef]
    exact integral_pos_of_support_eq
      (fun z => mul_nonneg (sq_nonneg _) (hv z)) hf_intOn
      (fun z => mul_nonneg (sq_nonneg _)
        (div_nonneg (hv z) (add_nonneg (hv z) (le_of_lt hApos)))) hgi hfg hJ
  refine ⟨(ℓmin / 2) * m, mul_pos (by linarith) hm_pos, ?_⟩
  intro ℓ hℓ
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hℓmin hℓ
  rw [hmdef]
  -- The denominator `B := 1/(c² ℓ²)` of the target integrand.
  set B : ℝ := 1 / (c ^ 2 * ℓ ^ 2) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]; exact one_div_pos.mpr (mul_pos (pow_pos hc 2) (pow_pos hℓpos 2))
  have hBA : B ≤ A := by
    rw [hAdef, hBdef]
    apply one_div_le_one_div_of_le (mul_pos (pow_pos hc 2) (pow_pos hℓmin 2))
    exact mul_le_mul_of_nonneg_left (by
      have h := mul_self_le_mul_self (le_of_lt hℓmin) hℓ
      simpa [pow_two] using h) (sq_nonneg c)
  have hgiB : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => (ω z) ^ 2 * (v z / (v z + B)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) MeasureTheory.volume :=
    integrableOn_sq_mul_div v ω hBpos hv hv1 hωm hω0 hω1
  -- Pointwise comparison of the integrands, hence of the set integrals.
  have hcmp : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        (ω z) ^ 2 * (v z / (v z + A)))
      ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        (ω z) ^ 2 * (v z / (v z + B)) := by
    apply MeasureTheory.setIntegral_mono hgi hgiB
    intro z
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact div_le_div_of_nonneg_left (hv z)
      (add_pos_of_nonneg_of_pos (hv z) hBpos) (by linarith [hBA])
  have hm_nn : 0 ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      (ω z) ^ 2 * (v z / (v z + A)) := le_of_lt hm_pos
  -- Multiply the comparison by `ℓ/2 ≥ ℓmin/2 ≥ 0`.
  have hfinal : (ℓmin / 2) * (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        (ω z) ^ 2 * (v z / (v z + A)))
      ≤ (ℓ / 2) * (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
        (ω z) ^ 2 * (v z / (v z + B))) := by
    calc (ℓmin / 2) * (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
            (ω z) ^ 2 * (v z / (v z + A)))
        ≤ (ℓ / 2) * (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
            (ω z) ^ 2 * (v z / (v z + A))) :=
          mul_le_mul_of_nonneg_right (by linarith) hm_nn
      _ ≤ (ℓ / 2) * (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R,
            (ω z) ^ 2 * (v z / (v z + B))) :=
          mul_le_mul_of_nonneg_left hcmp (by linarith)
  simpa [hBdef] using hfinal

end Work.BoseFixB3.CS.Pieces
