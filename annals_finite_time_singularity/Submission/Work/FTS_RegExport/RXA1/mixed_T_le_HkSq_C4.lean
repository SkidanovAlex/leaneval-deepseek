import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_RegExport.C4.HkSqSwap_C4
import Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary pointwise identities

The energy of a mixed slot is the angular partial integral of the corresponding `ℋ⁴`-summand:
on `Iθ` the angular weight `w_θ = sin(2θ)^{-γ/2}` squares to `sin(2θ)^{-γ}`, so

`(D_z^bD_θ^a f · Wt)² = sin(2θ)^{-γ} · ((D_z^bD_θ^a f)² · w²)`.

This is the identity `mixed_Wt_sq_eq_fts` of the smooth (`SmoothOpen`) development, re-proved
here for a bare curried function so that the `C⁴` statement does not have to import the
`StrongEps/SupPort` cone. -/

theorem sin_two_nonneg_Iθ_RXA1 {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- `w_θ(θ)² = sin(2θ)^{-γ}` on `Iθ`. -/
theorem wTheta_sq_eq_RXA1 {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.wTheta α θ) ^ 2 = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_mul (sin_two_nonneg_Iθ_RXA1 hθ) (-(Work.Spaces.gam α / 2)) 2]
    congr 1
    ring
  rw [Work.Spaces.wTheta]
  exact hsq

/-- The pointwise form of the identity, at a fixed radial variable. -/
theorem Wt_sq_eq_RXA1 {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (z A : ℝ) :
    (A * Work.Spaces.Wt α z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (A ^ 2 * (Work.Spaces.w z) ^ 2) := by
  have hwt := wTheta_sq_eq_RXA1 (α := α) hθ
  rw [Work.Spaces.Wt]
  calc (A * (Work.Spaces.w z * Work.Spaces.wTheta α θ)) ^ 2
      = A ^ 2 * (Work.Spaces.w z) ^ 2 * (Work.Spaces.wTheta α θ) ^ 2 := by ring
    _ = A ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [hwt]
    _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (A ^ 2 * (Work.Spaces.w z) ^ 2) := by
        ring

theorem mixed_T_le_HkSq_C4 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) :
    MeasureTheory.IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iθ
    ∧ (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hi : 1 ≤ a + 1 := by omega
  have hij : (a + 1) + (b + 1) ≤ 4 := by omega
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (α := α) hF hmem
  -- The radial partial integral of the weighted mixed slot.
  -- ## The pointwise identity `Φ θ = sin(2θ)^{-γ} ∫ (mixed)²w²`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ z in Work.Spaces.Iz,
              (Work.Spaces.mixed (b + 1) (a + 1) f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro θ hθ
    rw [show (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((Work.Spaces.mixed (b + 1) (a + 1) f z θ) ^ 2 * (Work.Spaces.w z) ^ 2) from
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun z => Wt_sq_eq_RXA1 hθ z _)]
    rw [MeasureTheory.integral_const_mul]
  -- ## A.e. strong measurability of the radial partial integral
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed (b + 1) (a + 1) f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hF hij).mul
      (Work.FTS.StrongEps.continuousOn_Wt_Q0_fin α)).pow 2
  have haesm1 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed (b + 1) (a + 1) f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (by
      simpa only [Work.FTS.EllipticEst.Q0] using hcont)
  have haesm2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed (b + 1) (a + 1) f p.2 p.1 * Work.Spaces.Wt α p.2 p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
    haesm1.prod_swap
  have hΦsm : AEStronglyMeasurable (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
      (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    haesm2.integral_prod_right'
  -- ## Pointwise domination by the `ℋ⁴`-integrand, a.e. in the angle
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f z θ := by
    filter_upwards [hGslice] with θ hθ
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => sq_nonneg _) hθ
      (Filter.Eventually.of_forall fun z =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ (a + 1) (b + 1) hi hij)
  -- ## Integrability of the radial partial integral
  have hΦint : Integrable (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
      (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hGint.mono' hΦsm ?_
    filter_upwards [hbound] with θ hθ
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun z => sq_nonneg _)]
    exact hθ
  -- ## Transfer to the stated function
  have hTae : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => ∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2) :=
    MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun θ hθ => (hpt θ hθ).symm)
  refine ⟨hΦint.congr hTae.symm, ?_⟩
  calc (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) (a + 1) f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.mixed (b + 1) (a + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
        MeasureTheory.integral_congr_ae hTae
    _ ≤ ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f z θ :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ =>
            MeasureTheory.integral_nonneg fun z => sq_nonneg _)
          hGint hbound
    _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS_RegExport.RXA1
