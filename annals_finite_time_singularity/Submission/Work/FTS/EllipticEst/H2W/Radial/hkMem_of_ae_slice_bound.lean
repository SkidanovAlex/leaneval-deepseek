import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Radial

set_option linter.unusedVariables false

/-- The level-`0` `HkIntegrand` unfolds into the weight `w` times the basic angular slice
integrand: for `θ ∈ Iθ`,
`HkIntegrand α 0 f z θ = w z ^ 2 * (f z θ ^ 2 * sEta θ)`.  (At `z = 0` the weight `w 0`
vanishes, and both sides are `0`.) -/
private theorem HkI_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z hθ]
  ring

/-- The `θ`-integral of the level-`0` `HkIntegrand` factors out the constant weight
`w z ^ 2`. -/
private theorem HkI_slice_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 f z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => HkI_eq α f z hθ)]
  rw [MeasureTheory.integral_const_mul]

theorem hkMem_of_ae_slice_bound {α : ℝ} {g Ψ L : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 < K)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (hbound : ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
    (hΨ : Work.Spaces.HkMem α 0 Ψ) (hL : Work.Spaces.HkMem α 0 L) :
    Work.Spaces.HkMem α 0 g := by
  -- ## the two conjuncts of `HkMem α 0 g`
  refine ⟨?_, ?_⟩
  · -- ### `θ`-slice integrability of the integrand, from the hypothesis on `g`
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hz0
    · -- `z = 0`: the weight `w 0` vanishes, so the integrand is identically `0`
      subst h0
      refine IntegrableOn.congr_fun (integrableOn_zero (μ := volume) (s := Work.Spaces.Iθ))
        (fun θ hθ => ?_) measurableSet_Icc
      rw [HkI_eq α g 0 hθ]
      simp [Work.Spaces.w]
    · -- `z > 0`: multiply the hypothesis of `hslice` by the constant `w z ^ 2`
      refine IntegrableOn.congr_fun ((hslice z hz0).const_mul ((Work.Spaces.w z) ^ 2))
        (fun θ hθ => ?_) measurableSet_Icc
      exact (HkI_eq α g z hθ).symm
  · -- ### integrability of the `z`-integral of the angular slices
    -- The slice integrals are a.e. strongly measurable, being the partial integrals of the
    -- jointly a.e. strongly measurable `HkIntegrand` (continuous on the open quadrant).
    have hAmeas : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
        (volume.restrict Work.Spaces.Iz) :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
    -- the integrable majorant `K · (slice integral of Ψ + slice integral of L)`
    have hBC : IntegrableOn (fun z => K *
        ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Ψ z θ)
          + (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 L z θ))) Work.Spaces.Iz :=
      (hΨ.2.add hL.2).const_mul K
    refine Integrable.mono' hBC hAmeas ?_
    -- it suffices to dominate a.e. on the open half-line
    have hIzm : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi 0) :=
      Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [hIzm]
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g z θ))]
    -- factor out `w z ^ 2` from all three slice integrals
    rw [HkI_slice_eq α g z, HkI_slice_eq α Ψ z, HkI_slice_eq α L z]
    have h1 : (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (Work.Spaces.w z) ^ 2
          * (K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) :=
      mul_le_mul_of_nonneg_left (hbound z hz) (sq_nonneg _)
    calc (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (Work.Spaces.w z) ^ 2
            * (K * ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) := h1
      _ = K * ((Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (L z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring

end Work.FTS.EllipticEst.H2W.Radial
