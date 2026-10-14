import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseHard
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.Spaces.HkSq_terms
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.slot_cs6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux

set_option autoImplicit false

/-! ## The two-function weighted Cauchy–Schwarz bound -/

/-- **Weighted Cauchy–Schwarz for a doubly weighted pairing.**

Let `ρ ≥ 0` on `Iz × Iθ`, and suppose that (on the open quadrant, which is conull in `Iθ`)
the `ρ`-weighted squares of `X` resp. `Y` are dominated by the `ℋ^n`-integrand of `u`
resp. `f`.  Then

  `|∫_z ∫_θ ρ · X · Y| ≤ |u|_{ℋ^n} · |f|_{ℋ^n}`.

Route: on each angular slice the pointwise inequality
`ρ|X||Y| = √(ρX²)·√(ρY²) ≤ √(HkIntegrand u)·√(HkIntegrand f)` and Cauchy–Schwarz in `L²(Iθ)`
bound `|∫_θ ρXY|` by the product of the two slice energies; Cauchy–Schwarz in `L²(Iz)`
(against the honest radial marginals supplied by `HkMem`) gives `√(HkSq α n u)·√(HkSq α n f)`.
No measurability, smoothness or integrability of the pairing itself is assumed: the totalised
(junk) values only make the left-hand side smaller. -/
theorem pairing_cs_le {α : ℝ} {n : ℕ} {ρ X Y u f : ℝ → ℝ → ℝ}
    (hu : Work.Spaces.HkMem α n u) (hf : Work.Spaces.HkMem α n f)
    (hρnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hdomU : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n u z θ)
    (hdomF : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ Work.Spaces.HkNorm α n u * Work.Spaces.HkNorm α n f := by
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hAnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α n u z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α n u z θ
  have hBnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α n f z θ := fun z θ =>
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  -- ## the angular slice estimate
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) := by
    intro z hz
    have hAslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n u z θ)
        Work.Spaces.Iθ := hu.1 z hz
    have hBslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α n f z θ)
        Work.Spaces.Iθ := hf.1 z hz
    have hAmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n u z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hAslice.aestronglyMeasurable
    have hBmeas : AEStronglyMeasurable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hBslice.aestronglyMeasurable
    have hAsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n u z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hAslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hAnn z θ)).symm))
    have hBsq : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      hBslice.congr (Eventually.of_forall (fun θ => (Real.sq_sqrt (hBnn z θ)).symm))
    have hAlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hAmeas).mpr hAsq
    have hBlp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iθ) :=
      (memLp_two_iff_integrable_sq hBmeas).mpr hBsq
    have hprodθ : Integrable
        (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
          * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iθ) :=
      memLp_one_iff_integrable.mp (hAlp.mul hBlp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |ρ z θ * X z θ * Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) := by
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      have hρ0 : 0 ≤ ρ z θ := hρnn z hz θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hgm : ρ z θ * |X z θ| * |Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
        Work.FTS.StrongPersist.H6Pair6Aux.leaf_prod_sqrt_le hρ0
          (hdomU z hz θ hθ) (hdomF z hz θ hθ)
      calc |ρ z θ * X z θ * Y z θ| = ρ z θ * |X z θ| * |Y z θ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) := hgm
    have hmono : (∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
      integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hprodθ hpt
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α n u z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) := hmono
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) :=
          Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hAslice hBslice
            (fun θ => hAnn z θ) (fun θ => hBnn z θ)
  -- ## the radial Cauchy–Schwarz
  have hFint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n u z θ) Work.Spaces.Iz := hu.2
  have hGint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n f z θ) Work.Spaces.Iz := hf.2
  have hFnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ :=
    fun z => MeasureTheory.integral_nonneg fun θ => hAnn z θ
  have hGnn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ :=
    fun z => MeasureTheory.integral_nonneg fun θ => hBnn z θ
  have houter : IntegrableOn (fun z =>
      Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
      Work.Spaces.Iz := by
    have h1meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have h2meas : AEStronglyMeasurable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
        (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have h1sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have h2sq : Integrable
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have h1lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n u z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h1meas).mpr h1sq
    have h2lp : MemLp
        (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ)) 2
        (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq h2meas).mpr h2sq
    exact memLp_one_iff_integrable.mp (h1lp.mul h2lp)
  have hstep1o : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| :=
    MeasureTheory.abs_integral_le_integral_abs
  have hstep2o : (∫ z in Work.Spaces.Iz,
        |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|)
      ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n u z θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) houter
      (ae_restrict_of_forall_mem hIzm hslice)
  have hCS : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α n u z θ)
      * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ))
      ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n u z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α n f z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.cs_sqrt_le_fts hFint hGint hFnn hGnn
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| := hstep1o
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n u z θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ) := hstep2o
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n u z θ)
        * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α n f z θ) := hCS
    _ = Work.Spaces.HkNorm α n u * Work.Spaces.HkNorm α n f := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkSq, Work.Spaces.HkSq]

/-! ## The requested per-slot bound -/

theorem slot_cs6 {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 6)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    {u f : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (mu : Work.Spaces.HkMem α 6 u) (mf : Work.Spaces.HkMem α 6 f) :
    |Work.FTS.TransportS.slotPairing ρ a b u f|
      ≤ Work.Spaces.HkNorm α 6 u * Work.Spaces.HkNorm α 6 f := by
  rw [Work.FTS.TransportS.slotPairing]
  refine pairing_cs_le mu mf (fun z _ θ hθ =>
    Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg_Iθ hρ z θ hθ) ?_ ?_
  · intro z _ θ hθ
    exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ
      (f := u) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab
  · intro z _ θ hθ
    exact Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all hα hρ
      (f := f) (b' := b) (n := 6) (z := z) (θ := θ) hθ hab

end Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaEnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! The remaining one-dimensional estimate after the angular integration by parts:
`|(q-1)·∫_z (L₁₂f·w²)·∫_θ cos(2θ)σ^{-q}h²| ≤ C₄|f|_{ℋ⁴}·|f|²_{ℋ⁶}`. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

theorem end_bound_fts {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {q C₄ : ℝ} (hα : 0 < α)
    (hmem6 : Work.Spaces.HkMem α 6 f) (hab : a + b ≤ 6)
    (hqabs : |q - 1| ≤ 1)
    (hC : ∀ z ∈ Work.Spaces.Iz, |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a
      (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
    (hout : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) :
    |(q - 1) * (∫ z in Work.Spaces.Iz,
        (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f := by
  -- nonnegativity of the `σ^{-q}`-weighted square, a.e. in `θ`
  have hsnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  -- `C₄·|f|_{ℋ⁴} ≥ 0` follows from `hC` (at `z = 1`); no separate sign hypothesis is needed
  have hX0 : 0 ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
    le_trans (abs_nonneg (Work.Construction.L12 f 1))
      (hC 1 (Set.mem_Ici.mpr (by norm_num)))
  -- the `θ`-majorant of the inner integral
  have hinner_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2|
        ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    filter_upwards [hslice] with z hz
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) hz ?_
    filter_upwards [hsnn] with θ hθ
    have hσ : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hθ _
    have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) := abs_of_nonneg hσ
    have h3 : |(Work.Spaces.mixed b a f z θ) ^ 2|
        = (Work.Spaces.mixed b a f z θ) ^ 2 := abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, abs_mul, h2, h3]
    calc (|Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
        ≤ (1 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcos hσ) (sq_nonneg _)
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by ring
  -- the pointwise bound by the `L₁₂`-majorant
  have hmaj_le : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        ≤ C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
    filter_upwards [hinner_le, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzin hz
    have hDnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [hsnn] with θ hθ
      exact mul_nonneg (Real.rpow_nonneg hθ _) (sq_nonneg _)
    have hW2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    calc |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2)|
        = |Work.Construction.L12 f z| * (Work.Spaces.w z) ^ 2
          * |∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hW2]
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
          refine mul_le_mul (mul_le_mul (hC z hz) le_rfl (sq_nonneg _) hX0) hzin
            (abs_nonneg _) (mul_nonneg hX0 hW2)
      _ = C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
  -- the majorant is integrable
  have hmaj : MeasureTheory.IntegrableOn (fun z => C₄ * Work.Spaces.HkNorm α 4 f
      * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) Work.Spaces.Iz :=
    hout.const_mul _
  -- the final chain
  have htarget : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
          * (Work.Spaces.mixed b a f z θ) ^ 2
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hleafslab := Work.FTS.StrongPersist.H6Pair6Aux.leaf_slot_le6 hα hmem6 a b
    (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) hab hleaf
  calc |(q - 1) * (∫ z in Work.Spaces.Iz,
        (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2))|
      = |q - 1| * |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := by rw [abs_mul]
    _ ≤ 1 * |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| :=
        mul_le_mul_of_nonneg_right hqabs (abs_nonneg _)
    _ = |∫ z in Work.Spaces.Iz,
          (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := one_mul _
    _ ≤ ∫ z in Work.Spaces.Iz,
        |(Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
              * (Work.Spaces.mixed b a f z θ) ^ 2)| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, C₄ * Work.Spaces.HkNorm α 4 f * ((Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => abs_nonneg _) hmaj hmaj_le
    _ = C₄ * Work.Spaces.HkNorm α 4 f * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = C₄ * Work.Spaces.HkNorm α 4 f * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by rw [htarget]
    _ ≤ C₄ * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 6 f :=
        mul_le_mul_of_nonneg_left hleafslab hX0

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12ShiftThetaIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! The three `IntegrableOn (Iz ×ˢ Iθ)` hypotheses of
`Work.FTS.StrongPersist.H6Aux.wip_Dth_ibp` for the `k = 0` slot of the `L₁₂·D_θ` expansion,
together with the product/outer/slice integrability of the bare leaf-weighted slot. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option maxHeartbeats 1600000

theorem ibp_integrable_fts {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem6 : Work.Spaces.HkMem α 6 f)
    (hmem7 : Work.Spaces.HkMem α 7 f) (h0 : Work.Construction.L12 f 0 = 0)
    {a b : ℕ} (hab : a + b ≤ 6) {q : ℝ}
    (hqle : q ≤ Work.Spaces.gam α) (hq0 : a = 0 → q ≤ Work.Spaces.eta) :
    MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2
          * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
          * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q)))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
    ∧ MeasureTheory.Integrable
        (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    ∧ MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz
    ∧ (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ) := by
  obtain ⟨C₄, hC₄pos, hC₄⟩ := L12Sup4
  set P : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hP
  -- a.e. positivity of `z`
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    have hEq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- `|L₁₂ f|` is bounded by the `ℋ⁴`-norm
  have hC : ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 f z| ≤ C₄ * Work.Spaces.HkNorm α 4 f := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · rw [← h, h0, abs_zero]
      exact mul_nonneg (le_of_lt hC₄pos) (Work.Spaces.HkNorm_nonneg α 4 f)
    · have hh := hC₄ α f hα hα1 hO hmem6 h0 0 (by norm_num) z h
      simpa using hh
  have hK0 : 0 ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
    le_trans (abs_nonneg (Work.Construction.L12 f 1))
      (hC 1 (Set.mem_Ici.mpr (by norm_num)))
  have hQ0 : ∀ᵐ p ∂P, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [hP]; exact ae_prod_mem_Q0
  have hsin_pos : ∀ᵐ p ∂P, 0 < Real.sin (2 * p.2) :=
    hQ0.mono fun p hp => by
      obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin_nn : ∀ᵐ p ∂P, 0 ≤ Real.sin (2 * p.2) :=
    hsin_pos.mono fun _ h => le_of_lt h
  -- the leaf-slot domination, a.e.
  have hleaf6 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b a f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact leafdom_rpow hα hab hqle hq0 (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hleaf7 : ∀ᵐ p ∂P, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
      * (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0] with p hp
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact leafdom_rpow hα (k := 7) (by omega) hqle (fun hc => absurd hc (by omega))
      (Set.mem_Ici.mpr (le_of_lt hz)) ⟨h1, h2⟩
  have hcomm : ∀ᵐ p ∂P, Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
      = Work.Spaces.mixed b (a + 1) f p.1 p.2 := by
    rw [hP]; exact dth_mixed_ae_eq hO a b
  -- integrability of the two level-`6`/`7` integrands
  have hI6 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 6 f p.1 p.2) P := by
    rw [hP]; exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem6).1
  have hI7 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 7 f p.1 p.2) P := by
    rw [hP]; exact (Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen hO hmem7).1
  have hmono67 : ∀ᵐ p ∂P,
      Work.Spaces.HkIntegrand α 6 f p.1 p.2 ≤ Work.Spaces.HkIntegrand α 7 f p.1 p.2 :=
    Filter.Eventually.of_forall fun p => Work.Spaces.HkIntegrand_mono α 6 f p.1 p.2
  -- continuity inputs
  have hL12c : ContinuousOn
      (fun z => Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    (continuousOn_L12 hO hmem6).mul continuousOn_w_sq
  have hhc : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).continuousOn
  have hsqc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ ^ 2))
      Work.FTS.EllipticEst.Q0 := continuousOn_uncurry_sq hhc
  have hdhc : ContinuousOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 := (hO.mixed b a).Dth.continuousOn
  have hphc : ContinuousOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
        * Work.Spaces.mixed b a f z θ)) Work.FTS.EllipticEst.Q0 := by
    have h := continuousOn_uncurry_mul hdhc hhc
    simpa using h
  -- the singular weight is nonnegative a.e. in `θ` (for the slice integrals)
  have hsin_nn_θ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ Real.sin (2 * θ) :=
    (Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ).mono fun θ hθ =>
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
  -- integrands
  have hm0 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (h1.mul h2).mul h3
  have hm1 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2 * Work.Spaces.mixed b a f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      exact continuousOn_uncurry_mul hdhc hhc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (h1.mul h2).mul h3
  have hm2 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    have h2 : ContinuousOn
        (fun p : ℝ × ℝ => Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      hL12c.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2))
        Work.FTS.EllipticEst.Q0 := by fun_prop
    have h4 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact ((h1.mul h2).mul h3).mul h4
  -- the a.e. domination for each of the three integrands
  have hbd0 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.mixed b a f p.1 p.2 ^ 2|
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2 := abs_of_nonneg hsq
    have e2 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have e3 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, e1, e2, e3]
    rw [hkey]
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLn hW) hsq) hσq
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hK0
  have hbd1 : ∀ᵐ p ∂P, ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf7, hleaf6, hcomm, hsin_nn, hmono67]
      with p hp hle7 hle6 hcm hσ0 hm67
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2| =
        |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2| := abs_mul _ _
    have e2 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have e3 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have hkey : ‖Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)‖
        = |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, e2, e3]
    rw [hkey]
    have hD : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
        = |Work.Spaces.mixed b (a + 1) f p.1 p.2| := by rw [hcm]
    have ham : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
        ≤ ((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2 := by
      rw [hD]
      nlinarith [sq_nonneg (|Work.Spaces.mixed b (a + 1) f p.1 p.2|
        - |Work.Spaces.mixed b a f p.1 p.2|),
        sq_abs (Work.Spaces.mixed b (a + 1) f p.1 p.2),
        sq_abs (Work.Spaces.mixed b a f p.1 p.2)]
    have hs1 : |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ (((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul ham (mul_le_mul_of_nonneg_right hLn hW) (by positivity) (by positivity)
    calc |Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2|
          * |Work.Spaces.mixed b a f p.1 p.2|
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * (Real.sin (2 * p.2)) ^ (-q)
        ≤ ((((Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
            + Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2)
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2))
          * (Real.sin (2 * p.2)) ^ (-q) := mul_le_mul_of_nonneg_right hs1 hσq
      _ = (C₄ * Work.Spaces.HkNorm α 4 f)
          * (((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b (a + 1) f p.1 p.2 ^ 2) / 2
            + ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
              * Work.Spaces.mixed b a f p.1 p.2 ^ 2) / 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2
            + (Work.Spaces.HkIntegrand α 7 f p.1 p.2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK0
          exact add_le_add (div_le_div_of_nonneg_right hle7 (by norm_num))
            (div_le_div_of_nonneg_right (hle6.trans hm67) (by norm_num))
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 7 f p.1 p.2 := by ring
  have hbd2 : ∀ᵐ p ∂P, ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
        * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
        * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
      ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hQ0, hleaf6, hsin_nn] with p hp hle hσ0
    obtain ⟨hz, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    have hW : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hsq : 0 ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2 := sq_nonneg _
    have hLn : |Work.Construction.L12 f p.1| ≤ C₄ * Work.Spaces.HkNorm α 4 f :=
      hC p.1 (Set.mem_Ici.mpr (le_of_lt hz))
    have e1 : |Work.Spaces.mixed b a f p.1 p.2 ^ 2|
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2 := abs_of_nonneg hsq
    have e2 : |(Work.Spaces.w p.1) ^ 2| = (Work.Spaces.w p.1) ^ 2 := abs_of_nonneg hW
    have e3 : |(Real.sin (2 * p.2)) ^ (-q)| = (Real.sin (2 * p.2)) ^ (-q) := abs_of_nonneg hσq
    have hkey : ‖Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (Work.Construction.L12 f p.1 * (Work.Spaces.w p.1) ^ 2)
          * Real.cos (2 * p.2) * (Real.sin (2 * p.2)) ^ (-q)‖
        = Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, e1, e2, e3]
    rw [hkey]
    have hs1 : Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
        ≤ Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLn hW) hsq
    calc Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * (|Work.Construction.L12 f p.1| * (Work.Spaces.w p.1) ^ 2)
          * |Real.cos (2 * p.2)| * (Real.sin (2 * p.2)) ^ (-q)
        ≤ (Work.Spaces.mixed b a f p.1 p.2 ^ 2
          * ((C₄ * Work.Spaces.HkNorm α 4 f) * (Work.Spaces.w p.1) ^ 2))
          * 1 * (Real.sin (2 * p.2)) ^ (-q) :=
          mul_le_mul (mul_le_mul hs1 (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = (C₄ * Work.Spaces.HkNorm α 4 f) * ((Work.Spaces.w p.1) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q) * Work.Spaces.mixed b a f p.1 p.2 ^ 2) := by ring
      _ ≤ (C₄ * Work.Spaces.HkNorm α 4 f) * Work.Spaces.HkIntegrand α 6 f p.1 p.2 :=
          mul_le_mul_of_nonneg_left hle hK0
  -- the fourth conjunct: the bare leaf-weighted slot
  have hm3 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P := by
    rw [hP]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      continuousOn_w_sq.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-q))
        Work.FTS.EllipticEst.Q0 :=
      (continuousOn_sin_two_rpow_neg q).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 := hsqc
    exact (h1.mul h2).mul h3
  have hbd3 : ∀ᵐ p ∂P, ‖(Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hleaf6, hsin_nn] with p hle hσ0
    have hσq : 0 ≤ (Real.sin (2 * p.2)) ^ (-q) := Real.rpow_nonneg hσ0 (-q)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hσq)
      (sq_nonneg _))]
    exact hle
  -- the first three conjuncts
  have hProd : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm0 hbd0
  have hProd1 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ * Work.Spaces.mixed b a f z θ
        * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI7.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm1 hbd1
  have hProd2 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Spaces.mixed b a f z θ ^ 2 * (Work.Construction.L12 f z * (Work.Spaces.w z) ^ 2)
        * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q))) P :=
    MeasureTheory.Integrable.mono' (hI6.const_mul (C₄ * Work.Spaces.HkNorm α 4 f)) hm2 hbd2
  -- the fourth conjunct: the bare leaf-weighted slot
  have hbd3 : ∀ᵐ p ∂P, ‖(Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 6 f p.1 p.2 := by
    filter_upwards [hleaf6, hsin_nn] with p hle hσ0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg hσ0 _)) (sq_nonneg _))]
    exact hle
  have hm3 : AEStronglyMeasurable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P := by
    rw [hP]
    refine (aesm_uncurry_mul (continuousOn_w_sq) (continuousOn_sin_two_rpow_neg q) hsqc).congr ?_
    filter_upwards with p
    show (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * Work.Spaces.mixed b a f p.1 p.2 ^ 2
      = (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-q)
        * Work.Spaces.mixed b a f p.1 p.2 ^ 2
    rfl
  have hProd3 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed b a f z θ) ^ 2)) P :=
    MeasureTheory.Integrable.mono' hI6 hm3 hbd3
  -- conjuncts 5 and 6 from conjunct 4
  have hOut : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
      * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iz := by
    have hsplit := (MeasureTheory.integrable_prod_iff hm3).mp hProd3
    have hfun : (fun z : ℝ => ∫ θ, ‖Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) (z, θ)‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
      funext z
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hsin_nn_θ] with θ hθ
      show ‖(Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2‖
        = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg hθ _)) (sq_nonneg _))]
      ring
    rw [hfun] at hsplit
    exact hsplit.2
  have hSlice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [hProd3.prod_right_ae, hzpos] with z hz hzp
    have hcoe : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have h1 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
      rw [h1]
      exact pow_ne_zero 2 (div_ne_zero (by positivity) (pow_ne_zero 2 (ne_of_gt hzp)))
    refine (hz.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr (Filter.Eventually.of_forall ?_)
    intro θ
    have hinv : ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2 = 1 := inv_mul_cancel₀ hcoe
    calc ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2)
        = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2) * ((Real.sin (2 * θ)) ^ (-q)
          * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
      _ = (Real.sin (2 * θ)) ^ (-q) * (Work.Spaces.mixed b a f z θ) ^ 2 := by
          rw [hinv, one_mul]
  have hconv : ∀ F : ℝ × ℝ → ℝ, MeasureTheory.Integrable F P →
      MeasureTheory.IntegrableOn F (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro F hF
    rw [MeasureTheory.IntegrableOn,
      show (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) from
        (MeasureTheory.Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ).symm]
    exact hF
  exact ⟨hconv _ hProd, hconv _ hProd1, hconv _ hProd2, hProd3, hOut, hSlice⟩



end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Weights: continuity, vanishing at `z = 0`, and the two arithmetic reductions -/

theorem contOn_leafW {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with h | h | ⟨-, h⟩
  · subst h
    exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta)).congr
      (fun p _ => rfl)
  · subst h
    exact Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.congr (fun p _ => rfl)
  · subst h
    exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0
        (Work.Spaces.gam α))).congr (fun p _ => rfl)

/-- Every leaf weight vanishes at `z = 0` (its `w²`-factor does). -/
theorem leaf_zero_left {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) : ρ 0 θ = 0 := by
  rcases hleaf with h | h | ⟨-, h⟩
  · rw [h]; simp [Work.FTS.TransportS.leafEta, Work.Spaces.w]
  · rw [h]; simp [Work.FTS.TransportS.leafOne, Work.Spaces.w]
  · rw [h]; simp [Work.FTS.TransportS.leafGam, Work.Spaces.w]

/-- The piece vanishes at `z = 0`. -/
theorem piece_at_zero {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k i : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) :
    Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (0, θ) = 0 := by
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece, leaf_zero_left hleaf θ, zero_mul]

/-- The weight `w²·sin(2θ)^{-(γ-1)}` is continuous on the open quadrant. -/
theorem contOn_Wgam (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α - 1)))
      Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α - 1))

theorem arith_four {X Cc C4 N4 N6 B : ℝ} (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hN4 : 0 ≤ N4) (hN6 : 0 ≤ N6) (hB : 1 ≤ B)
    (hres : X ≤ (Cc * (C4 * N4)) * N6 * N6) :
    X ≤ B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by
  refine hres.trans ?_
  have hA : 0 ≤ Cc * (C4 * N4) := mul_nonneg hCc (mul_nonneg hC4 hN4)
  have hD : 0 ≤ N4 * N6 + N6 * N6 := by nlinarith
  have h1 : (Cc * (C4 * N4)) * N6 * N6 ≤ (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6) := by
    have h2 : N6 * N6 ≤ N4 * N6 + N6 * N6 := by nlinarith
    calc (Cc * (C4 * N4)) * N6 * N6 = (Cc * (C4 * N4)) * (N6 * N6) := by ring
      _ ≤ (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6) := mul_le_mul_of_nonneg_left h2 hA
  have h3 : (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)
      ≤ B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by
    have h4 := mul_le_mul_of_nonneg_right hB (mul_nonneg hA hD)
    calc (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)
        = 1 * ((Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)) := by ring
      _ ≤ B * ((Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)) := h4
      _ = B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by ring
  exact h1.trans h3

/-- The arithmetic of the `k ≥ 5` branch: from the level-four Cauchy–Schwarz bound
`|∫∫| ≤ (Cc·C₆|f|₆)·|f|₄·|f|₆` conclude the statement's bound. -/
theorem arith_six {X Cc C6 N4 N6 B : ℝ} (hCc : 0 ≤ Cc) (hC6 : 0 ≤ C6)
    (hN4 : 0 ≤ N4) (hN6 : 0 ≤ N6) (hB : 1 ≤ B)
    (hres : X ≤ Cc * (C6 * N6) * N4 * N6) :
    X ≤ B * Cc * (C6 * N6 * (N4 * N6)) := by
  refine hres.trans ?_
  have hA : 0 ≤ Cc * (C6 * N6) := mul_nonneg hCc (mul_nonneg hC6 hN6)
  have hD : 0 ≤ N4 * N6 := mul_nonneg hN4 hN6
  have h4 := mul_le_mul_of_nonneg_right hB (mul_nonneg hA hD)
  calc Cc * (C6 * N6) * N4 * N6
      = 1 * ((Cc * (C6 * N6)) * (N4 * N6)) := by ring
    _ ≤ B * ((Cc * (C6 * N6)) * (N4 * N6)) := h4
    _ = B * Cc * (C6 * N6 * (N4 * N6)) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Finite-order smoothness of the radial iterates `(z∂_z)^k` -/

/-- If `r` is `C^K` on `(0,∞)` then its `k`-th `D_z`-iterate (`D_z = z∂_z`) is `C^{K-k}`
there, for `k ≤ K`: each application of `D_z` costs one derivative. -/
theorem contDiffOn_Zop_iterate {r : ℝ → ℝ} {K : ℕ}
    (h : ContDiffOn ℝ K r (Set.Ioi 0)) :
    ∀ k : ℕ, k ≤ K →
      ContDiffOn ℝ ((K - k : ℕ) : WithTop ℕ∞) ((Work.Spaces.Zop^[k]) r) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
      intro hk
      have hk' : k ≤ K := le_trans (Nat.le_succ k) hk
      have ih' := ih hk'
      rw [Function.iterate_succ_apply']
      show ContDiffOn ℝ ((K - (k + 1) : ℕ) : WithTop ℕ∞)
        (fun z => z * deriv ((Work.Spaces.Zop^[k]) r) z) (Set.Ioi 0)
      have hder : ContDiffOn ℝ ((K - (k + 1) : ℕ) : WithTop ℕ∞)
          (deriv ((Work.Spaces.Zop^[k]) r)) (Set.Ioi 0) :=
        ih'.deriv_of_isOpen isOpen_Ioi (by
          exact_mod_cast (show K - (k + 1) + 1 ≤ K - k by omega))
      exact contDiffOn_id.mul hder

/-- `L₁₂(f)` is `C⁷` on `(0,∞)` in the class of the row. -/
theorem contDiffOn_L12_seven {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 7 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
  (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα hα1 hso hm7 (by norm_num)).congr
    (fun z _ => (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm)

/-- The `D_z`-iterates of `L₁₂(f)` are continuous on `(0,∞)`. -/
theorem continuousOn_DzdIter_L12 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm7 : Work.Spaces.HkMem α 7 f)
    {k : ℕ} (hk : k ≤ 6) :
    ContinuousOn (fun z => Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z)
      (Set.Ioi 0) := by
  have hZ := contDiffOn_Zop_iterate (K := 7) (h := contDiffOn_L12_seven hα hα1 hso hm7) k
    (by omega)
  have hcont := hZ.continuousOn
  rwa [Work.FTS.StrongPersist.H6Pair6Aux.Zop_iter_eq_DzdIter] at hcont

/-! ## The leaf weights are continuous on the open quadrant -/

/-- The uncurried leaf weight of the slot `a` is continuous on the open quadrant. -/
theorem continuousOn_leaf_Q0 {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with rfl | rfl | ⟨_, rfl⟩
  · have h := (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta))
    exact h.congr (fun p _ => by simp only [Pi.mul_apply, Work.FTS.TransportS.leafEta])
  · simpa only [Work.FTS.TransportS.leafOne,
      Work.FTS.StrongPersist.H6Pair6Aux.leafOne_eq] using
      Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
  · have h := (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α)))
    exact h.congr (fun p _ => by simp only [Pi.mul_apply, Work.FTS.TransportS.leafGam])

/-! ## The AM–GM slot steps -/

/-- If the squares of `A`, `B` are dominated by `P` resp. `Q`, then `|A||B| ≤ P + Q`. -/
theorem abs_mul_le_add_of_sq_le {P Q A B : ℝ} (hA : A ^ 2 ≤ P) (hB : B ^ 2 ≤ Q) :
    |A| * |B| ≤ P + Q := by
  have h1 : |A| * |B| ≤ (1 / 2) * A ^ 2 + (1 / 2) * B ^ 2 := by
    have h := Work.FTS.StrongPersist.H6Pair6Aux.abs_mul_le_half A B
    rwa [abs_mul] at h
  have hP : 0 ≤ P := le_trans (sq_nonneg A) hA
  have hQ : 0 ≤ Q := le_trans (sq_nonneg B) hB
  linarith

/-- **The `η`-slot AM–GM step.**  If `|ρ|` is dominated by the square of the `D_z`-slot weight
`w/sin(2θ)^{η/2}` and the corresponding weighted squares of `X`, `Y` are slots of the levels
`7` resp. `6`, then `|ρ||X||Y|` is bounded by the sum of the two integrands. -/
theorem abs_mul_abs_mul_le_zslot {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
    (hX : (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    |ρ z θ| * |X| * |Y| ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    div_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc |ρ z θ| * |X| * |Y|
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 * |X| * |Y| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _)) (abs_nonneg _)
    _ = |X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
          * |Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hW]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- **The `γ`-slot AM–GM step.**  The same as `abs_mul_abs_mul_le_zslot` with the mixed slot
weight `Wt α = w·sin(2θ)^{-γ/2}` on both `X` and `Y`. -/
theorem abs_mul_abs_mul_le_gam {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2)
    (hX : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    |ρ z θ| * |X| * |Y| ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc |ρ z θ| * |X| * |Y| ≤ (Work.Spaces.Wt α z θ) ^ 2 * |X| * |Y| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _)) (abs_nonneg _)
    _ = |X * Work.Spaces.Wt α z θ| * |Y * Work.Spaces.Wt α z θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hW]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- **The `γ`-slot AM–GM step with a `sin(2θ)` factor.**  This is the form needed when the
angular coefficient contributes a factor `sin(2θ)`: the extra `sin(2θ)` (at most `1`) is spent
on `X`, whose weighted square is therefore allowed to carry it. -/
theorem sin_mul_abs_mul_abs_mul_le_gam {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {X Y z θ : ℝ}
    (hsn : 0 ≤ Real.sin (2 * θ))
    (hρ : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2)
    (hX : (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ)
    (hY : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ) :
    Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|
      ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ := by
  have hW : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_nonneg (by rw [Work.Spaces.w]; positivity) (Real.rpow_nonneg hsn _)
  calc Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|
      = Real.sin (2 * θ) * (|ρ z θ| * |X| * |Y|) := by ring
    _ ≤ Real.sin (2 * θ) * ((Work.Spaces.Wt α z θ) ^ 2 * |X| * |Y|) := by
        refine mul_le_mul_of_nonneg_left ?_ hsn
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ (abs_nonneg _))
          (abs_nonneg _)
    _ = |X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)| * |Y * Work.Spaces.Wt α z θ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hW, abs_of_nonneg hsn]
        ring
    _ ≤ Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ :=
        abs_mul_le_add_of_sq_le hX hY

/-- `(X·Wt α·sin 2θ)² ≤ w²·sin(2θ)^{-(γ-1)}·X²`: the `sin(2θ)`-factor (at most `1`) turns the
`γ`-slot weight `sin(2θ)^{-γ}` into a weight that is *dominated* by the `(γ-1)`-weight of
`domGm1`. -/
theorem sq_mul_Wt_mul_sin_le (α z θ X : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ)
    (hs : 0 < Real.sin (2 * θ)) (hs1 : Real.sin (2 * θ) ≤ 1) :
    (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) * X ^ 2 := by
  have hrw2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
    rw [show (Real.sin (2 * θ)) ^ 2 = (Real.sin (2 * θ)) ^ ((2 : ℝ)) by
      simpa using (Real.rpow_natCast (Real.sin (2 * θ)) 2).symm, ← Real.rpow_add hs]
    congr 1
    ring
  have hpow : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
    linarith
  calc (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
      = X ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
    _ = X ^ 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          * (Real.sin (2 * θ)) ^ 2 := by rw [Work.Spaces.bt_Wt_sq α z θ hα hθ]
    _ = X ^ 2 * (Work.Spaces.w z) ^ 2
          * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Real.sin (2 * θ)) ^ 2) := by ring
    _ = X ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [hrw2]
    _ ≤ X ^ 2 * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) * X ^ 2 := by
        ring

/-! ## The pointwise bound on the open quadrant -/

/-- **The pointwise bound of a Leibniz summand** on the open quadrant.  Each of the five
factors of `t5bPiece` is bounded separately, and the two `f`-slots are paired by AM–GM. -/
theorem t5bPiece_abs_le_quad {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {M Cc : ℝ} {k i : ℕ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hab : a + b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hMnn : 0 ≤ M) (hCc : 0 ≤ Cc)
    (hA : ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hCcg : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter j (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    (hk : k ≤ b) (hi : i ≤ a) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |t5bPiece f ρ a b k i (z, θ)| ≤
        ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
  intro z θ hz hθ0 hθ1
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongPersist.H6Pair6Aux.sin_two_pos hθIoo
  have hsn : 0 ≤ Real.sin (2 * θ) := le_of_lt hs
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hA' : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| ≤ M := hA z hz
  have hρnn : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hcoef : (1 : ℝ) ≤ (b.choose k : ℝ) * (a.choose i : ℝ) := by
    have h1 : (1 : ℝ) ≤ (b.choose k : ℝ) := by
      have h := Nat.choose_pos hk
      exact_mod_cast (by omega : 1 ≤ b.choose k)
    have h2 : (1 : ℝ) ≤ (a.choose i : ℝ) := by
      have h := Nat.choose_pos hi
      exact_mod_cast (by omega : 1 ≤ a.choose i)
    nlinarith
  set X : ℝ := Work.Spaces.mixed (b - k + 1) (a - i) f z θ with hXdef
  set Y : ℝ := Work.Spaces.mixed b a f z θ with hYdef
  have hcore : |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
      * |X| * |Y|
      ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · -- ## Case `a = 0` (hence `i = 0`): the pure `D_z`-slots
      have hi0 : i = 0 := by omega
      have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| ≤ Cc := by
        rw [hi0]
        simpa using hCcbd θ hθI
      have hρle : |ρ z θ| ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        rw [abs_of_nonneg hρnn]
        have h := Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_any (z := z) hα hleaf hθIoo
        rw [ha0] at h
        rw [wdivSq z θ hsn, ← Work.FTS.TransportS.slotW_zero_eq α hθIoo]
        exact h
      have hX2 : (X * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
        rw [hXdef, ha0, hi0, Nat.sub_zero, Work.Spaces.mixed_zero_right]
        exact Work.Spaces.sq_le_HkIntegrand_z α 7 f z θ (b - k + 1) (by omega)
      have hY2 : (Y * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [hYdef, ha0, Work.Spaces.mixed_zero_right]
        exact Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ b (by omega)
      have hXY := abs_mul_abs_mul_le_zslot (α := α) (f := f) hsn hρle hX2 hY2
      calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
          = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
              * (|ρ z θ| * |X| * |Y|) := by ring
        _ ≤ (M * Cc) * (|ρ z θ| * |X| * |Y|) :=
            mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
              (by positivity) (mul_nonneg hMnn hCc)
        _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
    · -- ## Case `a ≥ 1`: the mixed `γ`-slots
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have hρle : |ρ z θ| ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
        rw [abs_of_nonneg hρnn]
        have h1 : (Work.Spaces.Wt α z θ) ^ 2 = Work.FTS.TransportS.slotW α a z θ :=
          (Work.Spaces.bt_Wt_sq α z θ hα hθI).trans
            (Work.FTS.TransportS.slotW_of_pos_eq α ha1 hθIoo).symm
        exact (Work.FTS.StrongPersist.H6Pair6Aux.leaf_le_slotW_any (z := z) hα hleaf hθIoo).trans
          (le_of_eq h1.symm)
      have hY2 : (Y * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        rw [hYdef]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ a b ha1 (by omega)
      by_cases hi0 : i = 0
      · -- ## Case `a ≥ 1`, `i = 0`
        have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| ≤ Cc := by
          rw [hi0]
          simpa using hCcbd θ hθI
        have hX2 : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
          rw [hXdef, hi0, Nat.sub_zero]
          exact Work.Spaces.sq_le_HkIntegrand_mixed α 7 f z θ a (b - k + 1) ha1 (by omega)
        have hXY := abs_mul_abs_mul_le_gam (α := α) (f := f) hsn hρle hX2 hY2
        calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
            = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
                * (|ρ z θ| * |X| * |Y|) := by ring
          _ ≤ (M * Cc) * (|ρ z θ| * |X| * |Y|) :=
              mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
                (by positivity) (mul_nonneg hMnn hCc)
          _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
      · -- ## Case `a ≥ 1`, `i ≥ 1`: the coefficient contributes a `sin(2θ)`
        have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
        have hB : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
            ≤ Cc * Real.sin (2 * θ) := hCcg i hi1 (by omega) z θ hθI
        have hX2 : (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
            ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
          by_cases hai : a - i = 0
          · have hx : X = Work.Spaces.DzIter (b - k + 1) f z θ := by
              rw [hXdef, hai, Work.Spaces.mixed_zero_right]
            rw [hx]
            refine (sq_mul_Wt_mul_sin_le α z θ (Work.Spaces.DzIter (b - k + 1) f z θ) hα hθI hs
              hs1).trans ?_
            exact Work.FTS.StrongPersist.H6Pair6Aux.domGm1 (α := α) hα hα1 (f := f) (a' := 0)
              (b' := b - k + 1) (n := 7) hθIoo (by omega)
          · have hai1 : 1 ≤ a - i := Nat.one_le_iff_ne_zero.mpr hai
            have hX' : (X * Work.Spaces.Wt α z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 7 f z θ := by
              rw [hXdef]
              exact Work.Spaces.sq_le_HkIntegrand_mixed α 7 f z θ (a - i) (b - k + 1) hai1
                (by omega)
            calc (X * Work.Spaces.Wt α z θ * Real.sin (2 * θ)) ^ 2
                = (X * Work.Spaces.Wt α z θ) ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
              _ ≤ (X * Work.Spaces.Wt α z θ) ^ 2 * 1 :=
                  mul_le_mul_of_nonneg_left (by nlinarith [hsn, hs1]) (sq_nonneg _)
              _ = (X * Work.Spaces.Wt α z θ) ^ 2 := by ring
              _ ≤ Work.Spaces.HkIntegrand α 7 f z θ := hX'
        have hXY := sin_mul_abs_mul_abs_mul_le_gam (α := α) (f := f) hsn hρle hX2 hY2
        calc |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
              * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| * |X| * |Y|
            = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
                * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|)
                * (|ρ z θ| * |X| * |Y|) := by ring
          _ ≤ (M * (Cc * Real.sin (2 * θ))) * (|ρ z θ| * |X| * |Y|) :=
              mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) hMnn) le_rfl
                (by positivity) (mul_nonneg hMnn (mul_nonneg hCc hsn))
          _ = M * Cc * (Real.sin (2 * θ) * |ρ z θ| * |X| * |Y|) := by ring
          _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left hXY (mul_nonneg hMnn hCc)
  have habs : |t5bPiece f ρ a b k i (z, θ)|
      = |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        * |X| * |Y| := by
    simp only [t5bPiece, abs_mul, ← hXdef, ← hYdef]
  calc |t5bPiece f ρ a b k i (z, θ)|
      = |ρ z θ| * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        * |X| * |Y| := habs
    _ ≤ M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := hcore
    _ = 1 * (M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by
        ring
    _ ≤ ((b.choose k : ℝ) * (a.choose i : ℝ))
          * (M * Cc * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (mul_nonneg hMnn hCc)
            (add_nonneg (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)
              (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)))
    _ = ((b.choose k : ℝ) * (a.choose i : ℝ)) * (M * Cc)
          * (Work.Spaces.HkIntegrand α 7 f z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
end
