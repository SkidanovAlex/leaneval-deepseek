import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseFixB1.Core.div_sq_le_inv_mul
import Submission.Work.BoseFixB1.Core.slITube_le_one
import Submission.Work.BoseFixB1.Core.slI_bulk_eq
import Submission.Work.BoseFixB1.Core.sq_setLintegral_le_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.Core

open MeasureTheory
open scoped ENNReal

/-! ## Measurability of the sliding-window tube

The set `{(u, x) : x ∈ slI ℓ h u}` is closed: it is cut out by the two continuous inequalities
`max (-ℓ/2) (h u - h/2) ≤ x` and `x ≤ min (ℓ/2) (h u + h/2)`. This is what makes Tonelli
applicable to the sliding-window double integral. -/

lemma measurableSet_slI_preimage (ℓ h x : ℝ) :
    MeasurableSet {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u} := by
  have hset : {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u}
      = {u : ℝ | max (-ℓ / 2) (h * u - h / 2) ≤ x}
          ∩ {u : ℝ | x ≤ min (ℓ / 2) (h * u + h / 2)} := by
    ext u
    simp only [Work.BoseFixB1S.slI, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hset]
  exact (isClosed_le (by fun_prop : Continuous fun u : ℝ => max (-ℓ / 2) (h * u - h / 2))
      continuous_const).measurableSet.inter
    (isClosed_le continuous_const
      (by fun_prop : Continuous fun u : ℝ => min (ℓ / 2) (h * u + h / 2))).measurableSet

lemma measurableSet_prod_slI (ℓ h : ℝ) :
    MeasurableSet {p : ℝ × ℝ | p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1} := by
  have hset : {p : ℝ × ℝ | p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1}
      = {p : ℝ × ℝ | max (-ℓ / 2) (h * p.1 - h / 2) ≤ p.2}
          ∩ {p : ℝ × ℝ | p.2 ≤ min (ℓ / 2) (h * p.1 + h / 2)} := by
    ext p
    simp only [Work.BoseFixB1S.slI, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [hset]
  exact (isClosed_le (by fun_prop : Continuous fun p : ℝ × ℝ => max (-ℓ / 2) (h * p.1 - h / 2))
      continuous_snd).measurableSet.inter
    (isClosed_le continuous_snd
      (by fun_prop : Continuous fun p : ℝ × ℝ => min (ℓ / 2) (h * p.1 + h / 2))).measurableSet

lemma aemeasurable_uncurry_indicator {ℓ h : ℝ} {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    AEMeasurable (Function.uncurry fun u x => (Work.BoseFixB1S.slI ℓ h u).indicator G x)
      ((volume : Measure ℝ).prod volume) := by
  have hA := measurableSet_prod_slI ℓ h
  have h1 : (Function.uncurry fun u x => (Work.BoseFixB1S.slI ℓ h u).indicator G x)
      = fun p : ℝ × ℝ =>
          ({p : ℝ × ℝ | p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1}).indicator
            (fun _ => (1 : ℝ≥0∞)) p * G p.2 := by
    funext p
    rw [show (Function.uncurry fun u x => (Work.BoseFixB1S.slI ℓ h u).indicator G x) p
        = (Work.BoseFixB1S.slI ℓ h p.1).indicator G p.2 from rfl]
    by_cases hp : p.2 ∈ Work.BoseFixB1S.slI ℓ h p.1
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} from hp)]
      simp
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.2 ∈ Work.BoseFixB1S.slI ℓ h q.1} from hp)]
      simp
  rw [h1]
  exact ((measurable_const.indicator hA).mul (hG.comp measurable_snd)).aemeasurable

/-- **The bulk (unclipped) part of the one-dimensional sliding-box mean-square bound.**

For `0 < h ≤ ℓ` and a.e.-measurable `F : ℝ → ℝ≥0∞`, with `B := (ℓ-h)/(2h)` and
`I(u) := Work.BoseFixB1S.slI ℓ h u = Icc (max (-ℓ/2) (h·u - h/2)) (min (ℓ/2) (h·u + h/2))`:

  `∫⁻_{u ∈ (-B, B]} ( (∫⁻_{x ∈ I(u)} F x) / |I(u)| )²  ≤  (1/h) · ∫⁻_{x ∈ [-ℓ/2,ℓ/2]} F x² dx`

(On `u ∈ (-B,B]` the window is unclipped, so `I(u) = Icc (h u - h/2, h u + h/2)` and
`|I(u)| = h`; outside that region the statement asserts nothing, and the region is disjoint from
the two other regions `(-(ℓ+h)/(2h), -(ℓ-h)/(2h)]` and `((ℓ-h)/(2h), (ℓ+h)/(2h)]`, with the
outside giving no contribution, so this is exactly the middle piece of the 1D estimate
`∫⁻_u ((∫⁻_{I(u)}F)/|I(u)|)² ≤ (9/h)∫⁻_{[-ℓ/2,ℓ/2]}F²`.)

Proof (all in `ℝ≥0∞`, no integrability hypotheses):
1. replace `F` by its measurable representative (`AEMeasurable.mk`), which leaves both sides
   unchanged;
2. interval arithmetic (`slI_bulk_eq`) gives `I(u) = Icc (h u - h/2) (h u + h/2)` on the bulk
   region, and `Real.volume_Icc` gives `volume (I(u)) = ofReal h`;
3. Cauchy–Schwarz (`sq_setLintegral_le_mul`) together with `div_sq_le_inv_mul` gives the
   pointwise bound `((∫⁻_{I(u)}F)/|I(u)|)² ≤ (ofReal h)⁻¹ ∫⁻_{I(u)} F²`;
4. Tonelli (`lintegral_lintegral_swap`) reduces the double integral to
   `∫⁻_x (∫⁻_{u ∈ (-B,B]} 1_{x ∈ I(u)}) (F x)²`, whose inner factor is `≤ 1` by the tube
   estimate (`slITube_le_one`) and vanishes for `x ∉ [-ℓ/2, ℓ/2]`, giving
   `∫⁻_{x ∈ [-ℓ/2,ℓ/2]} (F x)²`. -/
theorem bulkEst {ℓ h : ℝ} (hh : 0 < h) (hhℓ : h ≤ ℓ) {F : ℝ → ℝ≥0∞}
    (hF : AEMeasurable F (volume : Measure ℝ)) :
    ∫⁻ u in Set.Ioc (-((ℓ - h) / (2 * h))) ((ℓ - h) / (2 * h)),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
      ≤ ENNReal.ofReal (1 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2 := by
  classical
  set S : Set ℝ := Set.Ioc (-((ℓ - h) / (2 * h))) ((ℓ - h) / (2 * h)) with hS
  have hSmeas : MeasurableSet S := by rw [hS]; exact measurableSet_Ioc
  obtain ⟨F', hF'meas, hFF'⟩ : ∃ F' : ℝ → ℝ≥0∞, Measurable F' ∧ F =ᵐ[volume] F' :=
    ⟨hF.mk F, hF.measurable_mk, hF.ae_eq_mk⟩
  have hF'aem : AEMeasurable F' (volume : Measure ℝ) := hF'meas.aemeasurable
  have hLHS : (∫⁻ u in S,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
      = ∫⁻ u in S,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2 := by
    refine lintegral_congr fun u => ?_
    have : (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F x)
        = ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x :=
      lintegral_congr_ae (ae_restrict_of_ae hFF')
    rw [this]
  have hRHS : (∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F x) ^ 2)
      = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hFF'] with x hx
    rw [hx]
  have hmain : (∫⁻ u in S,
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
      ≤ ENNReal.ofReal (1 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 := by
    have hvol : ∀ u ∈ S, (volume (Work.BoseFixB1S.slI ℓ h u) : ℝ≥0∞) = ENNReal.ofReal h := by
      intro u hu
      rw [slI_bulk_eq hh hu, Real.volume_Icc]
      congr 1
      ring
    have hpoint : ∀ᵐ u ∂(volume.restrict S),
        ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2
          ≤ (ENNReal.ofReal h)⁻¹ * ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 := by
      filter_upwards [ae_restrict_mem hSmeas] with u hu
      have hvol' := hvol u hu
      have hcs := sq_setLintegral_le_mul (μ := (volume : Measure ℝ))
        (s := Work.BoseFixB1S.slI ℓ h u) (Work.BoseFixB1S.measurableSet_slI ℓ h u) hF'aem
      have hcs' : (∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) ^ 2
          ≤ ENNReal.ofReal h * ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 := by
        rw [hvol'] at hcs
        exact hcs
      have hres := div_sq_le_inv_mul (a := ENNReal.ofReal h)
        (ENNReal.ofReal_ne_zero_iff.mpr hh) (ENNReal.ofReal_ne_top) hcs'
      rw [hvol']
      exact hres
    have hstep1 : (∫⁻ u in S,
          ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
        ≤ ∫⁻ u in S, (ENNReal.ofReal h)⁻¹ * ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 :=
      lintegral_mono_ae hpoint
    have hstep2 : (∫⁻ u in S, (ENNReal.ofReal h)⁻¹ * ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2)
        = (ENNReal.ofReal h)⁻¹ * ∫⁻ u in S, ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 :=
      lintegral_const_mul' _ _
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hh))
    have hstep3 : (∫⁻ u in S, ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2)
        ≤ ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 := by
      have hGmeas : Measurable fun x : ℝ => (F' x) ^ 2 := hF'meas.pow_const 2
      have huncurry : AEMeasurable
          (Function.uncurry fun u x => (Work.BoseFixB1S.slI ℓ h u).indicator (fun y => (F' y) ^ 2) x)
          ((volume.restrict S).prod (volume : Measure ℝ)) :=
        (aemeasurable_uncurry_indicator (ℓ := ℓ) (h := h) hGmeas).mono_measure
          (Measure.prod_mono Measure.restrict_le_self le_rfl)
      have hswap := lintegral_lintegral_swap (μ := volume.restrict S) (ν := (volume : Measure ℝ))
        (f := fun u x => (Work.BoseFixB1S.slI ℓ h u).indicator (fun y => (F' y) ^ 2) x) huncurry
      have key : ∀ u : ℝ, (Work.BoseFixB1S.slI ℓ h u).indicator (fun y => (F' y) ^ 2)
          = fun x => (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x
              * (F' x) ^ 2 := by
        intro u
        funext x
        by_cases hx : x ∈ Work.BoseFixB1S.slI ℓ h u
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          simp
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp
      calc (∫⁻ u in S, ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2)
          = ∫⁻ u, ∫⁻ x, (Work.BoseFixB1S.slI ℓ h u).indicator (fun y => (F' y) ^ 2) x
              ∂volume ∂(volume.restrict S) := by
            refine lintegral_congr fun u => ?_
            exact (lintegral_indicator (Work.BoseFixB1S.measurableSet_slI ℓ h u) _).symm
        _ = ∫⁻ x, ∫⁻ u, (Work.BoseFixB1S.slI ℓ h u).indicator (fun y => (F' y) ^ 2) x
              ∂(volume.restrict S) ∂volume := hswap
        _ = ∫⁻ x, (∫⁻ u in S,
                (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x) * (F' x) ^ 2 := by
            refine lintegral_congr fun x => ?_
            have hm : AEMeasurable (fun u : ℝ =>
                (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x)
                (volume.restrict S) :=
              ((measurable_const : Measurable fun _ : ℝ => (1 : ℝ≥0∞)).indicator
                (measurableSet_slI_preimage ℓ h x)).aemeasurable
            rw [lintegral_congr (fun u => congrFun (key u) x), lintegral_mul_const'' _ hm]
        _ ≤ ∫⁻ x, (Set.Icc (-ℓ / 2) (ℓ / 2)).indicator (fun y => (F' y) ^ 2) x := by
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ Set.Icc (-ℓ / 2) (ℓ / 2)
            · rw [Set.indicator_of_mem hx]
              have hT : (∫⁻ u in S,
                    (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ 1 := by
                have hA : MeasurableSet {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u} :=
                  measurableSet_slI_preimage ℓ h x
                calc (∫⁻ u in S, (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x)
                    ≤ ∫⁻ u, (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x := by
                      simpa using lintegral_mono_set (μ := (volume : Measure ℝ))
                        (f := fun u => (Work.BoseFixB1S.slI ℓ h u).indicator
                          (fun _ => (1 : ℝ≥0∞)) x) (Set.subset_univ S)
                  _ = ∫⁻ u, ({u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u}).indicator
                        (fun _ => (1 : ℝ≥0∞)) u := by
                      refine lintegral_congr fun u => ?_
                      by_cases hu : x ∈ Work.BoseFixB1S.slI ℓ h u
                      · rw [Set.indicator_of_mem hu,
                          Set.indicator_of_mem
                            (show u ∈ {v : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h v} from hu)]
                      · rw [Set.indicator_of_notMem hu,
                          Set.indicator_of_notMem
                            (show u ∉ {v : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h v} from hu)]
                  _ = (volume : Measure ℝ) {u : ℝ | x ∈ Work.BoseFixB1S.slI ℓ h u} :=
                      lintegral_indicator_one hA
                  _ ≤ 1 := slITube_le_one hh
              exact le_trans (mul_le_mul_of_nonneg_right hT zero_le) (by simp)
            · rw [Set.indicator_of_notMem hx]
              have hT0 : (∫⁻ u in S,
                  (Work.BoseFixB1S.slI ℓ h u).indicator (fun _ => (1 : ℝ≥0∞)) x) = 0 := by
                have hzero : (fun u => (Work.BoseFixB1S.slI ℓ h u).indicator
                    (fun _ => (1 : ℝ≥0∞)) x) = fun _ => 0 := by
                  funext u
                  exact Set.indicator_of_notMem (f := fun _ => (1 : ℝ≥0∞))
                    (fun hx' => hx (Work.BoseFixB1S.slI_subset ℓ h u hx'))
                rw [hzero]
                simp
              rw [hT0]
              simp
        _ = ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 :=
            lintegral_indicator measurableSet_Icc _
    have hcoef : (ENNReal.ofReal h)⁻¹ = ENNReal.ofReal (1 / h) := by
      rw [one_div]
      exact (ENNReal.ofReal_inv_of_pos hh).symm
    calc (∫⁻ u in S,
          ((∫⁻ x in Work.BoseFixB1S.slI ℓ h u, F' x) / (volume (Work.BoseFixB1S.slI ℓ h u))) ^ 2)
        ≤ ∫⁻ u in S, (ENNReal.ofReal h)⁻¹ * ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 :=
          hstep1
      _ = (ENNReal.ofReal h)⁻¹ * ∫⁻ u in S, ∫⁻ x in Work.BoseFixB1S.slI ℓ h u, (F' x) ^ 2 :=
          hstep2
      _ ≤ (ENNReal.ofReal h)⁻¹ * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 :=
          mul_le_mul_of_nonneg_left hstep3 zero_le
      _ = ENNReal.ofReal (1 / h) * ∫⁻ x in Set.Icc (-ℓ / 2) (ℓ / 2), (F' x) ^ 2 := by
          rw [hcoef]
  rw [hLHS, hRHS]
  exact hmain

end Work.BoseFixB1.Core
