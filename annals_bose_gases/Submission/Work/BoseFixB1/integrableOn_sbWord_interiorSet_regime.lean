import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1.sbPot_integral_le_potWordU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrableOn_sbWord_interiorSet_regime`

The dilute-regime `u`-marginal integrability of the a-priori chapter's small-box word
`sbWord = sbKin + sbPot`, restricted to the interior set `I₋`.

## Why the statement carries an existential `ε₀`

This is the corrected form of the sibling
`Work.BoseFixB1.integrableOn_sbWord_interiorSet` (see
`Submission/Work/BoseFixB1/FINDING_sbWord_marginal_integrable_missing_hv1.md` and the header of
`Submission/Work/BoseFixB1/integrableOn_sbWord_interiorSet.lean`): the requested statement there
fixed `{ε₀ μ : ℝ}` and assumed only `Adm v ε₀ μ`, which does **not** imply the two regime
inequalities

    R ≤ ℓ(μ)·d(μ)/16        and        R ≤ ℓ(μ)·chiR0        (ℓ = sideAt μ (a v), d = (paramsAt μ (a v)).d)

that every dominating estimate of the localised potential kernel needs.  Both inputs used here
(`Work.BoseFixB1.sbPot_integral_le_potWordU` for the potential half and
`Work.BSKinetic.slotWord_bounds` for the kinetic half) carry them.  The diluteness threshold
therefore has to be existentially quantified, and it is supplied by
`Work.BoseFixB1.regime_sideAt_ge`.

## The proof

* `Work.BoseFixB1.regime_sideAt_ge` (at `a = a v > 0`, `R > 0`) produces `ε₀ > 0` such that
  `0 < μ` and `μ(a v)³ ≤ ε₀` give both regime inequalities.
* `Adm v ε₀ μ` gives exactly `0 < μ`, `μ(a v)³ ≤ ε₀`, `ParamsOK (paramsAt μ (a v)) (μ(a v)³)`,
  hence `0 < ℓ`, `0 < d` (`adm_ell_pos`, `adm_d_pos`) and `1 ≤ M = 48` (`M_eq_mValue`, `mValue`).
* the kinetic half `Integrable (fun u => sbKin … u Φ)` is the content of
  `Work.BoseFixB1.integrable_tBwordBInd`, reproduced below under a private name so that this
  file's import cone is `sorry`-free (`integrable_tBwordBInd_marginal`);
* the potential half `Integrable (fun u => sbPot h μ u Φ)` is the first conjunct of
  `Work.BoseFixB1.sbPot_integral_le_potWordU` (a `sorry`-free, Fubini-based theorem);
* `Integrable.add` sums them, `sbWord` unfolds definitionally to `sbKin + sbPot`, and
  `Integrable.integrableOn` restricts to `I₋`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `u`-marginal integrability of the small-box kinetic word

The word is supported in the bounded `u`-region where the sliding box is non-empty and is uniformly
bounded there (`Work.BSKinetic.slotWord_bounds`, after the slot reduction
`Work.BSKinetic.tBwordBInd_eq_slotSum`); joint measurability
(`Work.BSKinetic.SlotSwap.joint_measurable_smallBoxWord1`) together with Tonelli
(`Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite`) makes the slot words
jointly integrable, and Fubini (`Integrable.integral_prod_left`) integrates the configuration
variable out. -/
private theorem integrable_tBwordBInd_marginal {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {N : ℕ}
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

/-- The kinetic half at FS's parameters: `Integrable (fun u => sbKin … u Φ)`.
`sbKin` depends on `v` only through the scalars `a v`, `sideAt μ (a v)`, `paramsAt μ (a v)`
(its `M` argument is ignored), so no hypothesis on `v` beyond the parameter data is needed. -/
private theorem integrable_sbKin_marginal_regime {v : ℝ³ → ℝ} {μ : ℝ}
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) :
    Integrable (fun u : ℝ³ =>
      sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)) :=
  integrable_tBwordBInd_marginal (ℓ := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
    (ε := (paramsAt μ (a v)).eT) (c := sbCut μ (a v)) hℓ hd Φ.contDiff

/-! ## 2. The target -/

theorem integrableOn_sbWord_interiorSet_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) := by
  -- the diluteness threshold: below it the two regime inequalities hold
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm n Φ
  have hμ : 0 < μ := hAdm.1
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
  obtain ⟨hreg, hregχ⟩ := hε₀ μ hμ hdil
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [M_eq_mValue]; norm_num [mValue]
  -- the kinetic half
  have hkin := integrable_sbKin_marginal_regime (v := v) (μ := μ) hℓ hd Φ
  -- the potential half (FS `lem:LocPotential` at FS's parameters, first conjunct)
  have hpot := (sbPot_integral_le_potWordU (v := v) (h := h) (hv1 := hv1) (hvrad := hvrad)
    (R := R) (μ := μ) hR hv_supp hav hℓ hd hM hreg hregχ Φ).1
  -- the two halves sum, and `sbWord` unfolds definitionally to `sbKin + sbPot`
  have hsum : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)) :=
    (hkin.add hpot).congr (Filter.Eventually.of_forall (fun u => by
      simp only [Pi.add_apply, sbWord, sbKin, sbPot]))
  -- restrict to the interior set
  exact hsum.integrableOn

end Work.BoseFixB1
