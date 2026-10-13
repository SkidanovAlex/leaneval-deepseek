import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

open MeasureTheory Set

/-- For `a > 0` the function `t ↦ t ^ e` is continuous on `(a, ∞)`. -/
private lemma continuousOn_rpow_Ioi (e a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ e) (Set.Ioi a) :=
  fun t ht =>
    (Real.continuousAt_rpow_const t e (Or.inl (ne_of_gt (lt_trans ha ht)))).continuousWithinAt

/-- For `a > 0` the function `t ↦ t ^ e` is almost everywhere strongly measurable for the
restricted measure. -/
private lemma aestronglyMeasurable_rpow_Ioi (e a : ℝ) (ha : 0 < a) :
    AEStronglyMeasurable (fun t : ℝ => t ^ e) (volume.restrict (Set.Ioi a)) :=
  ContinuousOn.aestronglyMeasurable (continuousOn_rpow_Ioi e a ha) measurableSet_Ioi

/-- For `a > 0` and any real exponent `e`, the restriction of `t ↦ t ^ e` to `(a, ∞)` is in
`L²` iff `2e < -1`; here we only need one direction, via the explicit integrability of
`t ↦ t ^ (2e)` on `(a, ∞)` and the identity `(t^e)^2 = t^(2e)` valid for `t > 0`. -/
private lemma memLp_two_rpow_Ioi (e a : ℝ) (ha : 0 < a) (h : 2 * e < -1) :
    MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi a)) := by
  refine (memLp_two_iff_integrable_sq (aestronglyMeasurable_rpow_Ioi e a ha)).mpr ?_
  have hbase : IntegrableOn (fun t : ℝ => t ^ (2 * e)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt h ha
  have hg2 : IntegrableOn (fun t : ℝ => (t ^ e) ^ 2) (Set.Ioi a) :=
    hbase.congr_fun (fun t ht => by
      show t ^ (2 * e) = (t ^ e) ^ 2
      have htpos : 0 < t := lt_trans ha ht
      rw [show (2 : ℝ) * e = e * 2 by ring]
      rw [Real.rpow_mul (x := t) htpos.le e 2, Real.rpow_two]) measurableSet_Ioi
  exact hg2

theorem srcP_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c)
      (Set.Ioi a) := by
  set e : ℝ := -(2 * (m : ℝ) / α) - 1 with he
  have h2e : 2 * e < -1 := by
    rw [he]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hx : (0 : ℝ) ≤ 2 * (m : ℝ) / α := div_nonneg (by linarith) hα.le
    nlinarith [hx]
  have hsub : Set.Ioi a ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi ha.le
  have hae : AEStronglyMeasurable c (volume.restrict (Set.Ioi a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hc2 : Integrable (fun t : ℝ => c t ^ 2) (volume.restrict (Set.Ioi a)) :=
    hc.mono_set hsub
  have hcL2 : MemLp c 2 (volume.restrict (Set.Ioi a)) :=
    (memLp_two_iff_integrable_sq hae).mpr hc2
  have hgL2 : MemLp (fun t : ℝ => t ^ e) 2 (volume.restrict (Set.Ioi a)) :=
    memLp_two_rpow_Ioi e a ha h2e
  have hprod : Integrable (fun t : ℝ => c t * t ^ e) (volume.restrict (Set.Ioi a)) :=
    hcL2.integrable_mul hgL2
  rw [he] at hprod
  show Integrable (Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c)
    (volume.restrict (Set.Ioi a))
  exact hprod

end Work.EllipticEst.ModalSolution.RGW
