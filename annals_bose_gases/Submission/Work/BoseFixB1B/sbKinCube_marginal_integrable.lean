import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1B.kineticHalfCube_of_oneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The `u`-marginal integrability of the cube word -/

/-- **The `u`-marginal integrability of the matched (cube-cutoff) localised word**
`Work.BoseFixB1B.cubeWord M ℓ d ε c · Φ`, for every `M ≥ 4`, every `ℓ > 0`, `d > 0`, every cut-off
`c`, every gap coefficient `ε` and every smooth box state `Φ`.

This is the cube-window twin of `Work.BoseFixB1.integrable_tBwordBInd`: the word is the sum over
the slots of the (one-particle) slot words, each of which is jointly integrable on
`volume.prod (boxMu n ℓ)` because it is bounded by `K` on the fixed compact `u`-ball given by
`cubeWord_uniform_bound` and vanishes outside it, and is jointly a.e.-strongly measurable by
`jointMeasurable_chiSmallB_slotWord`. -/
theorem cubeWord_marginal_integrable {M : ℕ} (hM : 4 ≤ M) {ℓ d ε c : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) {N : ℕ} {Φ : X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    MeasureTheory.Integrable (fun u : E3 => cubeWord M ℓ d ε c u Φ) := by
  rcases N with _ | n
  · -- `N = 0`: the word is an empty slot sum.
    have h0 : (fun u : E3 => cubeWord M ℓ d ε c u Φ) = fun _ : E3 => (0 : ℝ) := by
      funext u
      simp only [cubeWord, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
        Work.UBBInputs8.tBdiagFormInd, Work.UBBInputs8.cnPlusBoxInd, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero]
    rw [h0]
    exact integrable_zero E3 ℝ volume
  · -- `N = n + 1`: slot decomposition, joint integrability, Fubini.
    have hM1 : 1 ≤ M := by omega
    haveI hfin : IsFiniteMeasure (Work.BSKinetic.boxMu n ℓ) :=
      Work.BSKinetic.isFiniteMeasure_boxMu n ℓ hℓ.le
    obtain ⟨K, R, hK0, hR0, hfar, hsmall⟩ := cubeWord_uniform_bound hM hℓ hd n Φ hΦ
    -- joint integrability of each slot word on `volume.prod (boxMu n ℓ)`
    have hin : ∀ i : Fin (n + 1), MeasureTheory.Integrable
        (Function.uncurry (fun (u : E3) (r : X n) =>
          cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)))
        ((MeasureTheory.volume : Measure E3).prod (Work.BSKinetic.boxMu n ℓ)) := by
      intro i
      refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
        (μ := (MeasureTheory.volume : Measure E3)) (ν := Work.BSKinetic.boxMu n ℓ)
        (f := fun (u : E3) (r : X n) =>
          cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r))
        (g := fun _ : X n => ENNReal.ofReal K
          * (MeasureTheory.volume : Measure E3) (Metric.closedBall (0 : E3) R))
        (jointMeasurable_chiSmallB_slotWord hM hℓ hd n Φ hΦ i) ?_ ?_
      · rw [MeasureTheory.lintegral_const, Work.BSKinetic.boxMu, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (MeasureTheory.measure_closedBall_lt_top (x := (0 : E3)) (r := R)).ne)
          (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
      · rw [Work.BSKinetic.boxMu,
          MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        filter_upwards with r hr
        calc ∫⁻ u, ENNReal.ofReal ‖cubeWord M ℓ d ε c u
              (Work.BSKinetic.slotState1 i Φ r)‖
            ≤ ∫⁻ u, ENNReal.ofReal K
                * (Metric.closedBall (0 : E3) R).indicator (fun _ => (1 : ENNReal)) u := by
              apply lintegral_mono; intro u
              show ENNReal.ofReal ‖cubeWord M ℓ d ε c u
                  (Work.BSKinetic.slotState1 i Φ r)‖ ≤ ENNReal.ofReal K *
                (Metric.closedBall (0 : E3) R).indicator (fun _ => (1 : ENNReal)) u
              by_cases hu : u ∈ Metric.closedBall (0 : E3) R
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
          _ = ENNReal.ofReal K * (MeasureTheory.volume : Measure E3)
                (Metric.closedBall (0 : E3) R) := by
              rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              congr 1
              rw [MeasureTheory.lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
                MeasureTheory.setLIntegral_one]
    -- the slot integrals are integrable in `u`, and so is their sum
    have hsum : MeasureTheory.Integrable (fun u : E3 => ∑ i : Fin (n + 1),
        ∫ r in Submission.BoseGases.abox n ℓ,
          cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)) := by
      refine integrable_finsetSum _ (fun i _ => ?_)
      have hm := (hin i).integral_prod_left
      simpa only [Work.BSKinetic.boxMu, Function.uncurry] using hm
    -- the sum is the `(n+1)`-particle word, pointwise
    refine hsum.congr (Filter.Eventually.of_forall (fun u => ?_))
    show (∑ i : Fin (n + 1), ∫ r in Submission.BoseGases.abox n ℓ,
        cubeWord M ℓ d ε c u (Work.BSKinetic.slotState1 i Φ r)) = cubeWord M ℓ d ε c u Φ
    rw [show cubeWord M ℓ d ε c u Φ
        = Work.UBBInputs8.tBwordInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u)
            (ℓ * d) ε c Φ from rfl]
    exact (tBwordInd_eq_slotSum_three hℓ hd n u (Submission.BoseGases.chiSmallB M ℓ d u)
      (chiSmallB_contDiff3 hM hℓ hd u) (chiSmallB_hasCompactSupport' hM1 hℓ u)
      (chiSmallB_eq_zero_of_notMem_dlBox' hM1 hℓ hd u) Φ hΦ).symm

/-! ## 2. The target -/

/-- **The `u`-marginal integrability of the matched kinetic word** — the integrability conjunct of
`KineticHalfCube`, at the matched (single cube cutoff) vocabulary.  The diluteness threshold is
free (`ε₀ = 1`): only `0 < ℓ`, `0 < d` and `M ≥ 4` are used, and at FS's parameters those are
`adm_ell_pos`, `adm_d_pos` and `M = mValue = 48` for every admissible `μ`. -/
theorem sbKinCube_marginal_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1B.SbKinCubeMarginalIntegrable v := by
  refine ⟨1, one_pos, fun μ hAdm n Φ => ?_⟩
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := by
    show 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
    exact Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := by
    show 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
    exact Work.BoseFixB1.adm_d_pos hAdm
  have hM4 : 4 ≤ Work.BoseFixB1.bM v μ := by
    rw [bM_eq_mValue]; exact four_le_mValue
  refine (cubeWord_marginal_integrable (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) (Φ := (Φ : X n → ℝ))
    hM4 hℓ hd Φ.contDiff).congr ?_
  filter_upwards with u
  exact (sbKinCube_eq_cubeWord v μ u (Φ : X n → ℝ)).symm

end Work.BoseFixB1B
