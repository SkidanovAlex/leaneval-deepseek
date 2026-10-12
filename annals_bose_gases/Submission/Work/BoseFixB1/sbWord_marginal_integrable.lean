import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BSKinetic.Decomp.bsOneBody_eq_zero_of_far
import Submission.Work.BSKinetic.Decomp.continuous_bsOneBody
import Submission.Work.BSKinetic.FarBump.Defs
import Submission.Work.BSKinetic.FarBump.oneBody_pos_of_low_freq_bound
import Submission.Work.BSKinetic.bsOneBody_eq_dirichlet
import Submission.Work.BSKinetic.cnPlus_eq_slotSum
import Submission.Work.BSKinetic.familyBigKin_eq_slotFamily
import Submission.Work.BSKinetic.familyFormUnproj_eq_kernelForm
import Submission.Work.BSKinetic.familyForm_zero_eq
import Submission.Work.BSKinetic.tBwordBInd_slotSwap_and_integrable
import Submission.Work.BSKinetic.tsupport_bsWin_subset_bsBox
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1Aux.integrable_qLHSBIntegrand_box_singleL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The kinetic word: `u`-marginal integrability for every smooth state -/

/-- **The `u`-marginal integrability of FS `eq:appTB`'s small-box kinetic word**
`Work.UBBInputs8.tBwordBInd N ℓ d ε c · Φ`, for every particle number, every smooth state and
every `ℓ > 0`, `d > 0`.

The word is supported in the bounded `u`-region where the sliding box `dlBox ℓ d u` is non-empty
and is uniformly bounded there (`Work.BSKinetic.slotWord_bounds`, after the slot reduction
`Work.BSKinetic.tBwordBInd_eq_slotSum`), so its lintegral is finite; the joint measurability
`Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1` together with Tonelli
(`Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite`) makes the slot words
jointly integrable, and Fubini (`Integrable.integral_prod_left`) integrates the configuration
variable out. -/
theorem integrable_tBwordBInd {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {N : ℕ}
    {Φ : X N → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Integrable (fun u : ℝ³ => Work.UBBInputs8.tBwordBInd N ℓ d ε c u Φ) := by
  rcases N with _ | n
  · -- `N = 0`: the word is a sum over an empty slot set.
    have h0 : (fun u : ℝ³ => Work.UBBInputs8.tBwordBInd 0 ℓ d ε c u Φ) = fun _ : ℝ³ => 0 := by
      funext u
      simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
        Work.UBBInputs8.cnPlusBoxInd, Work.UBBInputs8.tBwordKinInd,
        Work.UBBInputs8.tBdiagFormInd, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, zero_add]
    rw [h0]
    exact integrable_zero _ _ _
  · -- `N = n + 1`: slot reduction, joint integrability, Fubini.
    haveI hfin : IsFiniteMeasure (Work.BSKinetic.boxMu n ℓ) :=
      Work.BSKinetic.isFiniteMeasure_boxMu n ℓ hℓ.le
    obtain ⟨K, R, hK0, hR0, hfar, hsmall, -⟩ :=
      Work.BSKinetic.slotWord_bounds (ℓ := ℓ) (d := d) (ε := ε) (c := c) hℓ hd n Φ hΦ
    -- joint integrability of each slot word on `volume.prod (boxMu n ℓ)`
    have hin : ∀ i : Fin (n + 1), Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
        Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)))
        ((volume : Measure ℝ³).prod (Work.BSKinetic.boxMu n ℓ)) := by
      intro i
      refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
        (μ := (volume : Measure ℝ³)) (ν := Work.BSKinetic.boxMu n ℓ)
        (f := fun (u : ℝ³) (r : X n) =>
          Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
        (g := fun _ : X n => ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R))
        (Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1 hℓ hd n Φ hΦ i) ?_ ?_
      · rw [lintegral_const, Work.BSKinetic.boxMu, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (MeasureTheory.measure_closedBall_lt_top (x := (0 : ℝ³)) (r := R)).ne)
          (abox_lt_top n ℓ hℓ.le).ne
      · rw [Work.BSKinetic.boxMu, MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
        filter_upwards with r hr
        calc ∫⁻ u, ENNReal.ofReal ‖Work.BSKinetic.smallBoxWord1 ℓ d ε c u
              (Work.BSKinetic.slotState1 i Φ r)‖
            ≤ ∫⁻ u, ENNReal.ofReal K *
                (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u := by
              apply lintegral_mono; intro u
              show ENNReal.ofReal ‖Work.BSKinetic.smallBoxWord1 ℓ d ε c u
                  (Work.BSKinetic.slotState1 i Φ r)‖ ≤ ENNReal.ofReal K *
                (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ENNReal)) u
              by_cases hu : u ∈ Metric.closedBall (0 : ℝ³) R
              · rw [Set.indicator_of_mem hu, mul_one]
                exact ENNReal.ofReal_le_ofReal
                  (by rw [Real.norm_eq_abs]; exact hsmall i r hr u)
              · rw [Set.indicator_of_notMem hu, mul_zero]
                have hu' : R < ‖u‖ := by
                  have h := hu
                  rw [Metric.mem_closedBall, dist_zero_right] at h
                  exact not_le.mp h
                rw [hfar u hu' i r]
                simp
          _ = ENNReal.ofReal K * volume (Metric.closedBall (0 : ℝ³) R) := by
              rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              rw [MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
                MeasureTheory.setLIntegral_one]
    -- the slot integrals are integrable in `u`, and so is their sum
    have hsum : Integrable (fun u : ℝ³ => ∑ i : Fin (n + 1),
        ∫ r in abox n ℓ,
          Work.BSKinetic.smallBoxWord1 ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)) := by
      refine integrable_finsetSum _ (fun i _ => ?_)
      have hm := (hin i).integral_prod_left
      simpa only [Work.BSKinetic.boxMu, Function.uncurry] using hm
    -- the sum is the `(n+1)`-particle word, pointwise
    refine hsum.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact (Work.BSKinetic.tBwordBInd_eq_slotSum hℓ hd n u Φ hΦ).symm

/-! ## 2. The first conjunct of the request, as stated -/

/-- **The first conjunct of `sbWord_marginal_integrable`, proved as stated**: `sbKin` depends on
`v` only through the scalars `a v`, `sideAt μ (a v)`, `paramsAt μ (a v)` (its `M` slot is
ignored), so no hypothesis on `v` beyond the parameter data is needed. -/
theorem integrable_sbKin_marginal {v : ℝ³ → ℝ} {μ : ℝ}
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    Integrable (fun u : ℝ³ =>
      sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)) :=
  integrable_tBwordBInd (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
    (ε := (paramsAt μ (a v)).eT) (c := sbCut μ (a v)) hℓ hd Φ.contDiff

/-- `M = mValue = 48` at FS's parameters (so `1 ≤ M` holds automatically). -/
theorem one_le_paramsAt_M (μ a : ℝ) : 1 ≤ (paramsAt μ a).M := by
  have h : (paramsAt μ a).M = 48 := by simp [paramsAt, fsParams, mValue]
  omega

/-! ## 3. The second conjunct, with the missing hypothesis `MemLp v 1` added -/

/-- **The `u`-marginal integrability of the localised potential word `qLHSwordB`**, from the
box-restricted joint integrability of its `(u,x)`-integrand by Fubini.  The scale `ℓ` is a single
`ℓ > 0` (no `ℓ ≥ 1`), `d > 0` is real and `μ` is free. -/
theorem integrable_qLHSwordB_marginal_singleL {v : ℝ³ → ℝ} {h : ScatSol v} {R0 μ d : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv1 : MemLp v 1) {M : ℕ} (hM : 1 ≤ M) (hd : 0 < d)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    {n : ℕ} {Φ : X n → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun u : ℝ³ => qLHSwordB h M ℓ d μ u Φ) := by
  have hint := Work.BoseFixB1Aux.integrable_qLHSBIntegrand_box_singleL (v := v) (h := h)
    (R0 := R0) (μ := μ) (d := d) hv_supp hR0 hv1 M hM hd hℓ hR hRχ (N := n) (Φ := Φ) hΦ
  have hm := hint.integral_prod_left
  simpa only [qLHSwordB_eq_integral, Function.uncurry] using hm

/-- **The second conjunct of the request, with `hv1 : MemLp v 1` added** (the standing
integrability of FS Theorem 1.2). -/
theorem integrable_sbPot_marginal {v : ℝ³ → ℝ} (h : ScatSol v) (hv1 : MemLp v 1)
    {ε₀ μ R : ℝ} (hadm : Adm v ε₀ μ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hreg : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hregχ : R ≤ sideAt μ (a v) * chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    Integrable (fun u : ℝ³ => sbPot h μ u (Φ : X n → ℝ)) :=
  integrable_qLHSwordB_marginal_singleL (v := v) (h := h) (R0 := R) (μ := μ)
    (d := (paramsAt μ (a v)).d) hv_supp hR hv1 (one_le_paramsAt_M μ (a v))
    (adm_d_pos hadm) (adm_ell_pos hadm) hreg hregχ Φ.contDiff.continuous

/-! ## 4. The corrected request -/

/-- **The requested conjunction with the missing hypothesis `hv1 : MemLp v 1` added** (the
standing integrability of FS Theorem 1.2 / the corpus: `Submission.lean`'s `theorem_1_2`,
`Work.BoseFixB1.slidingB_holds`, `Work.BoseFixB1B.perBoxIntegrated`,
`Work.BoseFixB1.integrableOn_sbWord_interiorSet`, `Work.BoseFixB1.kineticSplit` all carry it).
This is the statement the a-priori chapter should ask for; it is proved here, so a restated
`PotentialHalf`/`KineticHalf` can consume it directly. -/
theorem sbWord_marginal_integrable_of_memLp {v : ℝ³ → ℝ} (h : ScatSol v) (hv1 : MemLp v 1)
    {ε₀ μ R : ℝ} (hadm : Adm v ε₀ μ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hreg : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hregχ : R ≤ sideAt μ (a v) * chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    Integrable (fun u : ℝ³ =>
        sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)) ∧
    Integrable (fun u : ℝ³ => sbPot h μ u (Φ : X n → ℝ)) :=
  ⟨integrable_sbKin_marginal (adm_ell_pos hadm) (adm_d_pos hadm) Φ,
    integrable_sbPot_marginal h hv1 hadm hR hv_supp hreg hregχ Φ⟩

/-- **The `u`-marginal integrability of the full small-box word `sbWord = sbKin + sbPot`, on any
set** (with `MemLp v 1`), i.e. the corrected form of the sibling
`Work.BoseFixB1.integrableOn_sbWord_interiorSet` at the interior set. -/
theorem integrableOn_sbWord_of_memLp {v : ℝ³ → ℝ} (h : ScatSol v) (hv1 : MemLp v 1)
    {ε₀ μ R : ℝ} (hadm : Adm v ε₀ μ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hreg : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hregχ : R ≤ sideAt μ (a v) * chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (s : Set ℝ³) :
    IntegrableOn (fun u : ℝ³ => sbWord h μ u (Φ : X n → ℝ)) s := by
  obtain ⟨hkin, hpot⟩ := sbWord_marginal_integrable_of_memLp h hv1 hadm hR hv_supp hreg hregχ Φ
  exact (hkin.add hpot).integrableOn

/-! ## 5. The requested statement, **repaired**: with the standing hypothesis `hv1 : MemLp v 1`
added it is a theorem (see the header's finding). -/

theorem sbWord_marginal_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1)
    {ε₀ μ R : ℝ} (hadm : Work.BoseBoxFix.Adm v ε₀ μ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hreg : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hregχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)) ∧
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)) :=
  sbWord_marginal_integrable_of_memLp h hv1 hadm hR hv_supp hreg hregχ Φ

end Work.BoseFixB1
