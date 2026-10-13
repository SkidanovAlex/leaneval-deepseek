/-
Copyright: work module for the Elgindi finite-time singularity project.

# `residualEnergyTendstoZero` — the residual angular energy of the truncated modal series

For a source `F`, `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)` whose square is integrable
there, the residual energy of the `N`-th truncation of its angular modal expansion,

`z ↦ ∫_{Iθ} F z θ ^ 2 cos θ - ∑_{m ≤ N} (cmode m F z) ^ 2 * ∫_{Iθ} eFam m θ ^ 2 cos θ`,

is integrable in `z` and its integral over `(0,∞)` tends to `0`.

The pointwise ingredients are the angular Pythagoras identity (`eFam_pythagoras_alt`) and the
angular Parseval identity (`eFam_parseval`): for a.e. `z`,

* the residual equals `∫_{Iθ} (F z θ - ∑_{m ≤ N} cmode m F z · eFam m θ) ^ 2 cos θ ≥ 0`, and
* the truncated modal energies converge to `∫_{Iθ} F z θ ^ 2 cos θ`.

Since each truncated modal energy is nonnegative, the residual is at most the angular energy
`z ↦ ∫_{Iθ} F z θ ^ 2 cos θ`, which is integrable in `z` by Fubini (it is dominated by
`z ↦ ∫_{Iθ} F z θ ^ 2`, whose double integral is the hypothesis `hL2`).  The dominated
convergence theorem therefore applies.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.eFam_parseval
import Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras_alt
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.EllipticEst.LevelOneAsm.ParsevalZIntAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR.SourceSide

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

local notation "Iθ" => Work.Spaces.Iθ

/-- The weighted angular energy of the slice `F z ·`. -/
local notation "angE(" F ", " z ")" => (∫ θ in Iθ, F z θ ^ 2 * Real.cos θ)

/-- The energy of the first `N + 1` angular modes of the slice `F z ·`. -/
local notation "modE(" F ", " N ", " z ")" =>
  (∑ m ∈ Finset.range (N + 1),
    (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
      * (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))

/-- The `m`-th modal energy `∫_{Iθ} eFam m θ ^ 2 cos θ` is nonnegative. -/
lemma eFam_sq_cos_nonneg (m : ℕ) :
    0 ≤ ∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  show ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
    0 ≤ Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ
  rw [MeasureTheory.ae_restrict_iff' Work.EllipticEst.ModalSolution.measurableSet_Iθ]
  filter_upwards with θ hθ
  exact mul_nonneg (sq_nonneg _)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)

/-- The truncated modal energy of a slice is nonnegative. -/
lemma modalEnergy_nonneg (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) : 0 ≤ modE(F, N, z) :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (eFam_sq_cos_nonneg m))

theorem residualEnergyTendstoZero {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Set.Ioi 0,
        ((∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
          - ∑ m ∈ Finset.range (N + 1),
              (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
                * (∫ θ in Work.Spaces.Iθ,
                    Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)))
      Filter.atTop (nhds 0) := by
  classical
  -- The product of the two restricted Lebesgue measures is the plane measure restricted to `Q0`.
  have hprod : ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
    rw [← Work.FTS.EllipticEst.LevelOneAsm.volume_restrict_prod_Ioi_Iθ]
    exact Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0
  -- Integrability of the unweighted square on the product measure.
  have hF2int : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    rw [hprod]
    exact hL2
  -- A.e. strong measurability of the weighted square on the product measure.
  have hΦaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    rw [hprod]
    have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
      hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    have hcos : AEStronglyMeasurable (fun p : ℝ × ℝ => Real.cos p.2)
        ((volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0) :=
      (Real.continuous_cos.comp continuous_snd).aestronglyMeasurable
    have hsq : (((fun p : ℝ × ℝ => F p.1 p.2) * (fun p : ℝ × ℝ => F p.1 p.2))
          * (fun p : ℝ × ℝ => Real.cos p.2))
        = fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2 := by
      funext p
      simp only [Pi.mul_apply]
      ring
    rw [← hsq]
    exact (hF.mul hF).mul hcos
  -- Integrability of the weighted square on the product measure, by domination.
  have hΦint : Integrable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * Real.cos p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Iθ)) := by
    refine Integrable.mono' hF2int hΦaesm ?_
    rw [hprod]
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume)
      (s := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
      with p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hc0 : 0 ≤ Real.cos p.2 :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], hθ1⟩)
    have hc1 : Real.cos p.2 ≤ 1 := Real.cos_le_one p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (F p.1 p.2))]
    exact mul_le_of_le_one_right (sq_nonneg _) (by rwa [abs_of_nonneg hc0])
  -- The angular energy is integrable in `z` (Fubini).
  have hEnInt : Integrable (fun z => angE(F, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    hΦint.integral_prod_left
  have hEnAesm : AEStronglyMeasurable (fun z => angE(F, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    hΦaesm.integral_prod_right'
  -- A.e. strong measurability of the angular slices.
  have hSliceSM : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      AEStronglyMeasurable (fun θ => F z θ) ((volume : Measure ℝ).restrict Iθ) := by
    have hΦ : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Iθ)) := by
      rw [hprod]
      exact hsm.continuousOn.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact hΦ.prodMk_left
  -- A.e. integrability of the weighted angular slices.
  have hSliceSq : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ :=
    hΦint.prod_right_ae
  have hae : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      AEStronglyMeasurable (fun θ => F z θ) ((volume : Measure ℝ).restrict Iθ)
        ∧ IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Iθ := hSliceSM.and hSliceSq
  -- Pointwise Parseval for a.e. slice.
  have hparseval : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      Tendsto (fun N : ℕ => modE(F, N, z)) atTop (nhds (angE(F, z))) := by
    filter_upwards [hae] with z hz
    exact Work.EllipticEst.ModalSolution.eFam_parseval F z hz.1 hz.2
  -- The residual energy is nonnegative, through the pointwise Pythagoras identity.
  have hnonneg : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ N : ℕ,
      0 ≤ angE(F, z) - modE(F, N, z) := by
    filter_upwards [hae] with z hz
    intro N
    have hpyth := Work.EllipticEst.ModalSolution.eFam_pythagoras_alt F z N hz.1 hz.2
    rw [← hpyth]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    show ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      0 ≤ (F z θ - ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.cmode m F z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ
    rw [MeasureTheory.ae_restrict_iff' Work.EllipticEst.ModalSolution.measurableSet_Iθ]
    filter_upwards with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- The truncated modal energies are nonnegative.
  have hmod_nonneg : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), ∀ N : ℕ,
      0 ≤ modE(F, N, z) :=
    Filter.Eventually.of_forall (fun z N => modalEnergy_nonneg F N z)
  -- Domination of the residual by the angular energy.
  have hbound : ∀ N : ℕ, ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      ‖angE(F, z) - modE(F, N, z)‖ ≤ angE(F, z) := by
    intro N
    filter_upwards [hnonneg, hmod_nonneg] with z hn hm
    rw [Real.norm_eq_abs, abs_of_nonneg (hn N)]
    linarith [hm N]
  -- A.e. convergence of the residual energy to zero.
  have hlim : ∀ᵐ z ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      Tendsto (fun N : ℕ => angE(F, z) - modE(F, N, z)) atTop (nhds 0) := by
    filter_upwards [hparseval] with z hz
    have h := hz.const_sub (angE(F, z))
    simpa using h
  -- A.e. strong measurability of the modal coefficients.
  have haesm_cmode : ∀ m : ℕ,
      AEStronglyMeasurable (fun z => Work.FTS.PhiStar.Series.cmode m F z)
        ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
    fun m => Work.EllipticEst.ModalSolution.aesm_cmode hsm m
  have hTNaesm : ∀ N : ℕ, AEStronglyMeasurable (fun z => modE(F, N, z))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    intro N
    have h := Finset.aestronglyMeasurable_fun_sum (Finset.range (N + 1))
      (f := fun m z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2
        * (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ))
      (fun m _ => by
        have hm := ((haesm_cmode m).pow 2).mul_const
          (∫ θ in Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
        simpa only [Pi.pow_apply] using hm)
    simpa using h
  -- The dominated convergence theorem.
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))
    (bound := fun z => angE(F, z))
    (F := fun N z => angE(F, z) - modE(F, N, z))
    (f := fun _ => (0 : ℝ))
    (F_measurable := fun N => hEnAesm.sub (hTNaesm N))
    (bound_integrable := hEnInt) (h_bound := hbound) (h_lim := hlim)
  simpa using hmain

end Work.FTS.H2.ModalSolR.SourceSide
