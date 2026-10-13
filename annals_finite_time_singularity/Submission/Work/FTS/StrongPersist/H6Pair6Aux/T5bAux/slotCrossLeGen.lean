import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.IPGen.slotPairing_abs_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.slotCrossLe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **General cross-slot Cauchy–Schwarz with a constant.**  Let `W` be any nonnegative weight
on the quadrant, and suppose that (on the open quadrant) the `W`-weighted squares of two
functions `X`, `Y` are pointwise dominated by the `ℋ^p`- resp. `ℋ^n`-integrands of a common
`f`.  If `P` is pointwise dominated by `C · W · |X| · |Y|`, then

  `|∫∫ P| ≤ C · |f|_{ℋ^p} · |f|_{ℋ^n}`.

This is the two-level Cauchy–Schwarz argument (`slotCrossLe` / `cs_slotInt_abs_le`): at each
radial slice the pointwise AM–GM estimate `W|X||Y| ≤ √(W X²)·√(W Y²)` turns `|P|` into a
multiple of the product of the two square roots, and Cauchy–Schwarz integrates the product of
the square roots first in `θ` and then in `z`. -/
theorem slotCrossLeGen {α : ℝ} {f X Y W P : ℝ → ℝ → ℝ} {p n : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hp : Work.Spaces.HkMem α p f) (hn : Work.Spaces.HkMem α n f)
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hWc : ContinuousOn (Function.uncurry W) Work.FTS.EllipticEst.Q0)
    (hWnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ W z θ)
    (hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      W z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α p f z θ)
    (hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      W z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ)
    (hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |P z θ| ≤ C * (W z θ * |X z θ| * |Y z θ|)) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ C * Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hAnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α p f z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α p f z θ
  have hBnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α n f z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- ## the angular slice estimate
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, P z θ|
        ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := by
    intro z hz
    have hAslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α p f z θ)
        Work.Spaces.Iθ := hp.1 z hz
    have hBslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n f z θ)
        Work.Spaces.Iθ := hn.1 z hz
    have hAmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAslice.aestronglyMeasurable
    have hBmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBslice.aestronglyMeasurable
    have hAsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hAslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hAnn z θ)).symm))
    have hBsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hBslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hBnn z θ)).symm))
    have hAlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hAmeas).mpr hAsq
    have hBlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hBmeas).mpr hBsq
    have hprodθ : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (hAlp.mul hBlp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |P z θ| ≤ C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := by
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      have hgm : W z θ * |X z θ| * |Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le (hWnn z hz θ hθ)
          (hdomX z hz θ hθ) (hdomY z hz θ hθ)
      exact le_trans (hP z hz θ hθ) (mul_le_mul_of_nonneg_left hgm hC)
    have hmain : (∫ θ in Work.Spaces.Iθ, |P z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
        (hprodθ.const_mul C) hpt
    calc |∫ θ in Work.Spaces.Iθ, P z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |P z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, C * (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := hmain
      _ = C * ∫ θ in Work.Spaces.Iθ, (Real.sqrt (Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) := integral_const_mul C _
      _ ≤ C * (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hAslice hBslice
              (fun θ => hAnn z θ) (fun θ => hBnn z θ)) hC
  -- ## the radial Cauchy–Schwarz
  have hFint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α p f z θ) Work.Spaces.Iz := hp.2
  have hGint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n f z θ) Work.Spaces.Iz := hn.2
  have hFnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ :=
    fun z => integral_nonneg fun θ => hAnn z θ
  have hGnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ :=
    fun z => integral_nonneg fun θ => hBnn z θ
  have houter : IntegrableOn (fun z =>
      Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
      Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have h1sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have h2sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have h1lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α p f z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have hstep1o : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ| :=
    abs_integral_le_integral_abs
  have hstep2o : (∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ|)
      ≤ ∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
      (houter.const_mul C) (ae_restrict_of_forall_mem hIzm hslice)
  have hstep3o : (∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)))
      = C * ∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) :=
    integral_const_mul C _
  have hCS : (∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hFint hGint hFnn hGnn
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, P z θ|
      ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, P z θ| := hstep1o
    _ ≤ ∫ z in Work.Spaces.Iz, C * (Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := hstep2o
    _ = C * ∫ z in Work.Spaces.Iz, (Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) := hstep3o
    _ ≤ C * (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α p f z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n f z θ)) := mul_le_mul_of_nonneg_left hCS hC
    _ = C * Work.Spaces.HkNorm α p f * Work.Spaces.HkNorm α n f := by
        simp only [Work.Spaces.HkNorm, Work.Spaces.HkSq]
        ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
