import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **Cross-slot Cauchy–Schwarz.**  If the `w²sin(2θ)^{-q}`-weighted squares of two functions
`X`, `Y` are pointwise dominated by the `ℋ^p`- resp. `ℋ^n`-integrands of a common `f`, then the
corresponding weighted *cross* pairing of `X` and `Y` is bounded by `|f|_{ℋ^p}·|f|_{ℋ^n}`.

The proof is the two-level Cauchy–Schwarz argument: on each angular slice the pointwise AM–GM
estimate `ρ·|X|·|Y| ≤ √(ρX²)·√(ρY²)` turns the pairing into a product of the two square roots,
which Cauchy–Schwarz integrates into `√(∫_θ HkIntegrand α p)·√(∫_θ HkIntegrand α n)`; a second
Cauchy–Schwarz in `z` gives `√(HkSq α p f)·√(HkSq α n f) = HkNorm α p f · HkNorm α n f`. -/
theorem slotCrossLe {α : ℝ} {f X Y : ℝ → ℝ → ℝ} {q : ℝ} {p n : ℕ}
    (hα : 0 < α) (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hp : Work.Spaces.HkMem α p f) (hn : Work.Spaces.HkMem α n f)
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hdomX : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) →
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α p f z θ)
    (hdomY : ∀ z θ, θ ∈ Set.Ioo 0 (π / 2) →
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (Y z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α n f z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q) * (X z θ * Y z θ)|
      ≤ Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
  let W : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
  let A : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α p f z θ
  let B : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.HkIntegrand α n f z θ
  change |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|
      ≤ Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hAnn : ∀ z θ, 0 ≤ A z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α p f z θ
  have hBnn : ∀ z θ, 0 ≤ B z θ := fun z θ => Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- the weight is nonnegative on the closed angular interval
  have hWnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ W z θ := by
    intro z θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact mul_nonneg (sq_nonneg (Work.Spaces.w z)) (Real.rpow_nonneg hsin _)
  -- ## the angular slice estimate
  have hsliceAll : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := by
    intro z hz
    have hstep1 : |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, |W z θ * (X z θ * Y z θ)| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
          (fun θ : ℝ => W z θ * (X z θ * Y z θ)))
    have hcongr : (∫ θ in Work.Spaces.Iθ, |W z θ * (X z θ * Y z θ)|)
        = ∫ θ in Work.Spaces.Iθ, W z θ * |X z θ| * |Y z θ| := by
      refine integral_congr_ae (ae_restrict_of_forall_mem hIθm (fun θ hθ => ?_))
      simp only [abs_mul, abs_of_nonneg (hWnn z θ hθ)]
      ring
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        W z θ * |X z θ| * |Y z θ| ≤ Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
      Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h1 h2 => by
        refine leaf_prod_sqrt_le (hWnn z θ ⟨le_of_lt h1, le_of_lt h2⟩) ?_ ?_
        · exact hdomX z θ ⟨h1, h2⟩
        · exact hdomY z θ ⟨h1, h2⟩)
    have hAslice : IntegrableOn (fun θ => A z θ) Work.Spaces.Iθ := hp.1 z hz
    have hBslice : IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ := hn.1 z hz
    have h4_meas : AEStronglyMeasurable (fun θ => Real.sqrt (A z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAslice.aestronglyMeasurable
    have h6_meas : AEStronglyMeasurable (fun θ => Real.sqrt (B z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBslice.aestronglyMeasurable
    have h4_sq : Integrable (fun θ => Real.sqrt (A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hAslice.congr (Filter.Eventually.of_forall (fun θ => (Real.sq_sqrt (hAnn z θ)).symm))
    have h6_sq : Integrable (fun θ => Real.sqrt (B z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hBslice.congr (Filter.Eventually.of_forall (fun θ => (Real.sq_sqrt (hBnn z θ)).symm))
    have h4_lp : MemLp (fun θ => Real.sqrt (A z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq h4_meas).mpr h4_sq
    have h6_lp : MemLp (fun θ => Real.sqrt (B z θ)) 2 (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq h6_meas).mpr h6_sq
    have hprod : Integrable (fun θ => Real.sqrt (A z θ) * Real.sqrt (B z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (h4_lp.mul h6_lp)
    have hstep3 : (∫ θ in Work.Spaces.Iθ, W z θ * |X z θ| * |Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) :=
      MeasureTheory.integral_mono_of_nonneg
        (ae_restrict_of_forall_mem hIθm (fun θ hθ => mul_nonneg
          (mul_nonneg (hWnn z θ hθ) (abs_nonneg _)) (abs_nonneg _)))
        hprod hpt
    have hstep4 : (∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ))
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
      cs_sqrt_le_fts hAslice hBslice (fun θ => hAnn z θ) (fun θ => hBnn z θ)
    calc |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|
        ≤ ∫ θ in Work.Spaces.Iθ, |W z θ * (X z θ * Y z θ)| := hstep1
      _ = ∫ θ in Work.Spaces.Iθ, W z θ * |X z θ| * |Y z θ| := hcongr
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (A z θ) * Real.sqrt (B z θ) := hstep3
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := hstep4
  -- ## the radial Cauchy–Schwarz
  have hAint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, A z θ) Work.Spaces.Iz := hp.2
  have hBint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz := hn.2
  have hAnnI : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, A z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => hAnn z θ))
  have hBnnI : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, B z θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae
      (ae_restrict_of_forall_mem hIθm (fun θ _ => hBnn z θ))
  have houter_int : IntegrableOn (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBint.aestronglyMeasurable
    have h1sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hAint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hAnnI z)).symm))
    have h2sq : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hBint.congr (Filter.Eventually.of_forall (fun z => (Real.sq_sqrt (hBnnI z)).symm))
    have h1lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have hstep1o : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        W z θ * (X z θ * Y z θ)|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iz)
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)))
  have hstep2o : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) houter_int
      (ae_restrict_of_forall_mem hIzm hsliceAll)
  have hCS : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) :=
    cs_sqrt_le_fts hAint hBint hAnnI hBnnI
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, W z θ * (X z θ * Y z θ)| := hstep1o
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, B z θ) := hstep2o
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, A z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, B z θ) := hCS
    _ = Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq]
        first
          | rfl
          | simp only [A, B]

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
