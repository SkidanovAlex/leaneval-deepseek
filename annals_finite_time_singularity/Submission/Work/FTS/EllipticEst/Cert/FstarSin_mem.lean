/-
Copyright: work module for the Elgindi finite-time singularity project.

# `F_*(F)·sin 2θ ∈ ℋ^k` for a source `C^∞` on the *open* quadrant

This module supplies the **membership half** of the layer certificate
`Work.FTS.EllipticEst.Cert.FstarSin_layer`:

  `Work.FTS.EllipticEst.SmoothOpen F`, `F ∈ ℋ^k`  ⟹  `F_*(F)·sin 2θ ∈ ℋ^k`,

where `SmoothOpen F` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` — the class of sources
produced by the elliptic data `Work.FTS.EllipticEst.EllHyp` (the source is only known to equal
`bslOp α Ψ` on the open quadrant, cf. `Cert/SmoothOpen_bslOp.lean`).

## Route

The target `g z θ = F_*(F)(z)·sin 2θ` is of the *separated* form `R(z)·sin 2θ` with
`R = F_*`, so its `ℋ^k`-integrand is the explicit function `HkExp α k R` of
`Cert/Defs.lean` (`HkIntegrand_radial_sin`).  Writing

* `angZ θ = sin(2θ)^{2-η}` (the angular factor of a `D_z`-summand),
* `angA α i θ = (D_θ^i(sin 2θ))²·sin(2θ)^{-γ}` (that of a mixed summand),

the `θ`-integral of the integrand is a fixed linear combination of the radial iterates
`radIter R i z` with the constants `∫_θ angZ` and `∫_θ angA α i` (`integral_HkExp_L`).  Three
facts then give membership:

* each `θ`-slice is integrable on `Iθ`: the integrand is continuous in `θ` on the open interval
  and bounded there (`integrableOn_slice_of_bound_L`, with the crude bound `sliceConst`);
* the slice integral `S z = ∫_θ HkIntegrand α k g z θ` agrees, for almost every `z`, with the
  explicit measurable function `Psi α k F` in which the radial iterates of `F_*` are replaced by
  the moments `Bmom F i` (`ae_sliceIntegral_eq_Psi_L`): the identification of the two uses the
  moment tower `radIter (Bmom F 0) i = Bmom F i` (a.e., `radIter_Bmom_ae_L`, from
  `Cert/FstarSin_norm.lean`);
* `Psi` is dominated a.e. by `hkConst k · ∫_θ HkIntegrand α k F z θ`
  (`Cert/FstarSin_norm.slice_Hk_le_open`, the a.e. slice estimate), which is integrable by
  hypothesis.  Since `Psi` is a.e. strongly measurable (`aestronglyMeasurable_Psi_L`, from
  Fubini for the integral `Bmom F i = ∫_θ D_z^i F · sinθcos²θ` of a function continuous on the
  open quadrant), `S` is integrable as well.

All the auxiliary lemmas below are `private`: the only exported declaration is the membership
certificate `HkMem_Fstar_sin_open`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.FTS.EllipticEst.Cert.HkIntegrand_radial_sin
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_norm
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.FstarHkAux
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Integrability of the angular profiles `angZ` and `angA` -/

private theorem continuous_angZ_L : Continuous angZ := by
  unfold angZ
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
    (fun θ => Or.inr (by rw [Work.Spaces.eta]; norm_num))

private theorem angZ_nonneg_L {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angZ θ := by
  rw [angZ]
  exact Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _

private theorem angZ_le_one_L {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : angZ θ ≤ 1 := by
  rw [angZ]
  exact Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ) (FstarHkOpen.sin_two_le_one θ)
    (by rw [Work.Spaces.eta]; norm_num)

private theorem integrableOn_angZ_L : MeasureTheory.IntegrableOn angZ Work.Spaces.Iθ :=
  FstarHkOpen.integrableOn_Iθ_of_abs_le
    (continuous_angZ_L.continuousOn.aestronglyMeasurable
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc))
    (fun θ hθ => by rw [abs_of_nonneg (angZ_nonneg_L hθ)]; exact angZ_le_one_L hθ)

private theorem continuousOn_angA_L (α : ℝ) (i : ℕ) :
    ContinuousOn (angA α i) (Set.Ioo 0 (π / 2)) := by
  have hslice : ContDiffOn ℝ ⊤ (Work.FTS.EllipticEst.sinProf i)
      (Set.Ioo (-1) (Real.pi / 2 + 1)) := FstarHkOpen.smoothSlice_sinProf i
  have hsp : ContinuousOn (Work.FTS.EllipticEst.sinProf i) (Set.Ioo 0 (π / 2)) :=
    hslice.continuousOn.mono
      (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hsin : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo 0 (π / 2)) := by
    refine ContinuousOn.rpow_const
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn) ?_
    intro θ hθ
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])))
  unfold angA
  exact (hsp.pow 2).mul hsin

private theorem angA_nonneg_L (α : ℝ) (i : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ angA α i θ := by
  unfold angA
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)

private theorem angA_le_angK_L (α : ℝ) (i : ℕ) (h1 : 1 ≤ Work.Spaces.gam α)
    (h2 : Work.Spaces.gam α ≤ 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    angA α i θ ≤ FstarHkOpen.angK i :=
  FstarHkOpen.angK_bound i (Work.Spaces.gam α) h1 h2 hθ

private theorem integrableOn_angA_L (α : ℝ) (i : ℕ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (angA α i) Work.Spaces.Iθ := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  refine FstarHkOpen.integrableOn_Iθ_of_abs_le (C := FstarHkOpen.angK i) ?_ ?_
  · rw [show (MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iθ
        = (MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) from
      MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
    exact (continuousOn_angA_L α i).aestronglyMeasurable measurableSet_Ioo
  · intro θ hθ
    rw [abs_of_nonneg (angA_nonneg_L α i hθ)]
    exact angA_le_angK_L α i hgam1 hgam2 hθ

/-! ## The `θ`-integral of the separated integrand `HkExp` -/

private theorem integral_HkExp_L (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ)
    (hZ : MeasureTheory.IntegrableOn angZ Work.Spaces.Iθ)
    (hA : ∀ i : ℕ, MeasureTheory.IntegrableOn (angA α i) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, HkExp α k R z θ)
      = (Work.Spaces.w z) ^ 2 *
          ((∫ θ in Work.Spaces.Iθ, angZ θ)
              * (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter R j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ)) := by
  have hZc : ∀ i : ℕ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2
        * angZ θ) Work.Spaces.Iθ := fun i => hZ.const_mul _
  have hAc : ∀ i j : ℕ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => if 1 ≤ i ∧ i + j ≤ k then
        (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
        else 0) Work.Spaces.Iθ := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0)
          = fun θ : ℝ => (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * angA α i θ := by
        funext θ
        rw [if_pos hc]
      rw [hfun]
      exact (hA i).const_mul _
    · have hfun : (fun θ : ℝ => if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [if_neg hc]
      rw [hfun]
      exact integrableOn_zero
  have h1 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
      = (Work.Spaces.w z) ^ 2
          * ((∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, angZ θ)) := by
    have hstep1 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
        = ∑ i ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.radIter R i z) ^ 2
              * (Work.Spaces.w z) ^ 2 * angZ θ :=
      MeasureTheory.integral_finsetSum (Finset.range (k + 1))
        (f := fun i => fun θ => (Work.FTS.EllipticEst.radIter R i z) ^ 2
          * (Work.Spaces.w z) ^ 2 * angZ θ) (fun i _ => hZc i)
    rw [hstep1]
    have hstep2 : ∀ i ∈ Finset.range (k + 1),
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.radIter R i z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angZ θ)
          = ((Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, angZ θ) :=
      fun i _ => MeasureTheory.integral_const_mul _ _
    rw [Finset.sum_congr rfl hstep2]
    calc (∑ i ∈ Finset.range (k + 1),
            (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, angZ θ))
        = (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2
              * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angZ θ) := by
          rw [← Finset.sum_mul]
      _ = ((Work.Spaces.w z) ^ 2 * (∑ i ∈ Finset.range (k + 1),
              (Work.FTS.EllipticEst.radIter R i z) ^ 2))
            * (∫ θ in Work.Spaces.Iθ, angZ θ) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = (Work.Spaces.w z) ^ 2
            * ((∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.radIter R i z) ^ 2)
                * (∫ θ in Work.Spaces.Iθ, angZ θ)) := by
          ring
  have h2 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angA α i θ else 0))
      = (Work.Spaces.w z) ^ 2
          * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.FTS.EllipticEst.radIter R j z) ^ 2 else 0)
                * (∫ θ in Work.Spaces.Iθ, angA α i θ)) := by
    have hstep : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
              * (Work.Spaces.w z) ^ 2 * angA α i θ else 0))
        = ∑ i ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
                * (Work.Spaces.w z) ^ 2 * angA α i θ else 0) :=
      MeasureTheory.integral_finsetSum (Finset.range (k + 1))
        (f := fun i => fun θ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angA α i θ else 0))
        (fun i _ => integrable_finsetSum _ (fun j _ => hAc i j))
    rw [hstep]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hstep' : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angA α i θ else 0))
        = ∑ j ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ,
            (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
              * (Work.Spaces.w z) ^ 2 * angA α i θ else 0) :=
      MeasureTheory.integral_finsetSum (Finset.range (k + 1))
        (f := fun j => fun θ => (if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0)) (fun j _ => hAc i j)
    rw [hstep']
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hfun : (fun θ : ℝ => if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0)
          = fun θ : ℝ => (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * angA α i θ := by
        funext θ
        rw [if_pos hc]
      rw [hfun, if_pos hc, MeasureTheory.integral_const_mul]
      ring
    · have hfun : (fun θ : ℝ => if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
          else 0) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        rw [if_neg hc]
      rw [hfun, if_neg hc, MeasureTheory.integral_zero]
      ring
  unfold HkExp
  rw [MeasureTheory.integral_add
      (integrable_finsetSum (Finset.range (k + 1))
        (f := fun i => fun θ => (Work.FTS.EllipticEst.radIter R i z) ^ 2
          * (Work.Spaces.w z) ^ 2 * angZ θ) (fun i _ => hZc i))
      (integrable_finsetSum (Finset.range (k + 1))
        (f := fun i => fun θ => ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.radIter R j z) ^ 2
            * (Work.Spaces.w z) ^ 2 * angA α i θ else 0))
        (fun i _ => integrable_finsetSum _ (fun j _ => hAc i j))),
    h1, h2]
  ring

/-! ## The crude bound on a slice -/

/-- A crude bound for `HkExp α k R z` on `Iθ`: the angular factors `angZ` resp. `angA` are
replaced by their bounds `1` resp. `angK i`. -/
private def sliceConst_L (k : ℕ) (R : ℝ → ℝ) (z : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2
            * FstarHkOpen.angK i
        else 0

private theorem continuousOn_HkExp_L (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) :
    ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)) := by
  unfold HkExp
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum _ fun i _ => ?_
    exact continuousOn_const.mul continuous_angZ_L.continuousOn
  · refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      exact continuousOn_const.mul (continuousOn_angA_L α i)
    · simp only [if_neg hc]
      exact continuousOn_const

private theorem HkExp_le_sliceConst_L (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ, HkExp α k R z θ ≤ sliceConst_L k R z := by
  have hgam1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hgam2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  intro θ hθ
  have hZ1 : angZ θ ≤ 1 := angZ_le_one_L hθ
  unfold HkExp sliceConst_L
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum fun i _ => ?_
    have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ
        ≤ (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hZ1 h2
      _ = (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
  · refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]
      have h2 : 0 ≤ (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (angA_le_angK_L α i hgam1 hgam2 hθ) h2
    · simp only [if_neg hc]
      exact le_refl 0

/-! ## Integrability of a slice, from continuity and boundedness -/

private theorem integrableOn_slice_of_bound_L (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) (hz : 0 < z)
    (C : ℝ)
    (hcont : ContinuousOn (fun θ => HkExp α k R z θ) (Set.Ioo 0 (π / 2)))
    (hbnd : ∀ θ ∈ Set.Ioo 0 (π / 2), HkExp α k R z θ ≤ C) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
        (fun z θ => R z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ := by
  have hcongr : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
        = HkExp α k R z θ :=
    fun θ hθ => HkIntegrand_radial_sin α k R z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => R z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) :=
    (hcont.aestronglyMeasurable measurableSet_Ioo).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => (hcongr θ hθ).symm))
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => C) (Set.Ioo 0 (π / 2)) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hle : ∀ᵐ θ ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))),
      ‖Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ‖ ≤ C :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ),
        hcongr θ hθ]
      exact hbnd θ hθ
  refine MeasureTheory.IntegrableOn.congr_set_ae (t := Set.Ioo 0 (π / 2))
    (MeasureTheory.Integrable.mono' hconst haesm hle) ?_
  exact MeasureTheory.Ioo_ae_eq_Icc.symm

/-! ## The explicit measurable function `Psi` -/

/-- The a.e. value of the slice integral `z ↦ ∫_θ HkIntegrand α k (F_*·sin 2θ) z θ`: the
angular integrals are evaluated and the radial factors are the moments
`Bmom F i z = F_*(D_z^i F)(z)`. -/
private def Psi (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, angZ θ)
      * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ)

private theorem aestronglyMeasurable_Bmom_L (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (i : ℕ) :
    AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hsin : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter i F)
    (hF.DzIter i).continuousOn Work.Elliptic.sinCos2 hsin
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  simpa only [Work.FTS.EllipticEst.Bmom, Work.FTS.EllipticEst.PsiInt] using h

private theorem aestronglyMeasurable_w_sq_L :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hw : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Ioi 0) := by
    rw [show Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 from rfl]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
      (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have h : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := hw.pow 2
  rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
      = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioi

private theorem aesm_finset_sum_L {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun z => ∑ i ∈ s, f i z) μ :=
  (Finset.aestronglyMeasurable_sum s h).congr
    (Filter.Eventually.of_forall fun z => Finset.sum_apply z s f)

private theorem aestronglyMeasurable_Psi_L (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) :
    AEStronglyMeasurable (Psi α k F)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) := by
  have hB : ∀ i : ℕ, AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.Bmom F i z)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    fun i => aestronglyMeasurable_Bmom_L α k F hF i
  have hw := aestronglyMeasurable_w_sq_L
  unfold Psi
  refine AEStronglyMeasurable.add ?_ ?_
  · refine AEStronglyMeasurable.mul aestronglyMeasurable_const ?_
    exact aesm_finset_sum_L (Finset.range (k + 1))
      (f := fun i => fun z => (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
      (fun i _ => hw.mul ((hB i).pow 2))
  · exact aesm_finset_sum_L (Finset.range (k + 1))
      (f := fun i => fun z => ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      (fun i _ => aesm_finset_sum_L (Finset.range (k + 1))
        (f := fun j => fun z => (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ))
        (fun j _ => by
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · have hcf : (fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ))
                = fun z : ℝ => ((Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ) := by
              funext z
              rw [if_pos hc]
            rw [hcf]
            exact (hw.mul ((hB j).pow 2)).mul aestronglyMeasurable_const
          · have hcf : (fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ)) = fun _ : ℝ => (0 : ℝ) := by
              funext z
              rw [if_neg hc]
              simp
            rw [hcf]
            exact aestronglyMeasurable_const))

/-! ## The a.e. identity `radIter (B_0) j = B_j` -/

private theorem radIter_Bmom_ae_L (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    filter_upwards with z j hj
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hj
    rfl
  · filter_upwards [ae_radIter_Bmom_eq_top α k hF hmem hk,
      MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z htop hz j hj
    rcases lt_or_eq_of_le hj with h | h
    · exact radIter_Bmom_eq α k hF hmem j (by omega) z hz
    · subst h
      exact htop

/-! ## The a.e. evaluation of the slice integral -/

private theorem ae_sliceIntegral_eq_Psi_L (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      =ᵐ[(MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz] Psi α k F := by
  have hrad : ∀ᵐ z ∂((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
    rw [show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz)
        = ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioi 0)) from by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact radIter_Bmom_ae_L α k F hF hmem
  have hInt : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      = (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, angZ θ)
              * (∑ i ∈ Finset.range (k + 1),
                  (Work.FTS.EllipticEst.radIter
                    (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter
                      (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, angA α i θ)) := by
    intro z
    rw [MeasureTheory.setIntegral_congr_fun (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc) (fun θ hθ => HkIntegrand_radial_sin α k
          (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z θ hθ)]
    exact integral_HkExp_L α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
      integrableOn_angZ_L (fun i => integrableOn_angA_L α i hα hα1)
  filter_upwards [hrad] with z hzrad
  have h1 : ∀ i ∈ Finset.range (k + 1),
      Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z
        = Work.FTS.EllipticEst.Bmom F i z :=
    fun i hi => hzrad i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hS1 : (∑ i ∈ Finset.range (k + 1),
        (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) i z) ^ 2)
      = ∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.Bmom F i z) ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
  have hS2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z) ^ 2
          else 0) * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc, h1 j hj]
    · simp only [if_neg hc]
  have hA1 : (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, angZ θ)
        * (∑ i ∈ Finset.range (k + 1), (Work.FTS.EllipticEst.Bmom F i z) ^ 2))
      = (∫ θ in Work.Spaces.Iθ, angZ θ)
        * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hA2 : (Work.Spaces.w z) ^ 2 * (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ))
      = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
            * (∫ θ in Work.Spaces.Iθ, angA α i θ) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · simp only [if_pos hc]; ring
    · simp only [if_neg hc]; ring
  have hmain : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      = Psi α k F z := by
    rw [hInt z, hS1, hS2, Psi, mul_add, hA1, hA2]
  exact hmain

/-! ## The membership certificate -/

/-- **`F_*(F)·sin 2θ ∈ ℋ^k`** for a source `F` which is `C^∞` on the open quadrant and
`F ∈ ℋ^k` (`0 < α ≤ 1`). -/
theorem HkMem_Fstar_sin_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) := by
  have hfun : (fun z θ : ℝ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      = fun z θ : ℝ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ) := by
    funext z θ
    rw [Work.FTS.EllipticEst.Bmom_zero]
  rw [hfun]
  have hslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
    · subst h0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ _ => ?_) (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k _ θ).symm
    · exact integrableOn_slice_of_bound_L α k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z
        hpos (sliceConst_L k (fun z => Work.FTS.EllipticEst.Bmom F 0 z) z)
        (continuousOn_HkExp_L α k _ z)
        (fun θ hθ => HkExp_le_sliceConst_L α k _ z hα hα1 θ
          ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  refine ⟨hslice, ?_⟩
  have hae := ae_sliceIntegral_eq_Psi_L α k F hα hα1 hF hmem
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k
        (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz) :=
    (aestronglyMeasurable_Psi_L α k F hF).congr hae.symm
  refine MeasureTheory.Integrable.mono' (hmem.2.const_mul (FstarHkOpen.hkConst k)) haesm ?_
  filter_upwards [slice_Hk_le_open α k hF hα hα1 hmem] with z hz
  have hz' : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => Work.FTS.EllipticEst.Bmom F 0 z * Real.sin (2 * θ)) z θ)
      ≤ FstarHkOpen.hkConst k
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    simpa only [hfun] using hz
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
  simpa only [smul_eq_mul] using hz'

end Work.FTS.EllipticEst.Cert
