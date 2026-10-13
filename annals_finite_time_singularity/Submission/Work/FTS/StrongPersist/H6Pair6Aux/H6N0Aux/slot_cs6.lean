/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6N0Aux/slot_cs6` — the Cauchy–Schwarz slot bound at level six

For every leaf weight `ρ` of a slot `(a,b)` of the level-six pairing, and any two `ℋ⁶`-data
`u`, `f`,

  `|slotPairing ρ a b u f| = |∫_z ∫_θ ρ · D_z^bD_θ^a u · D_z^bD_θ^a f|`
      `≤ |u|_{ℋ⁶} · |f|_{ℋ⁶}`,

with the **sharp** constant `1`.

This is the two-function, two-level Cauchy–Schwarz estimate.  The level-six sibling
`H6Pair6Aux.SlotPairingHkSq` only gives the *additive* form
`≤ (|u|²_{ℋ⁶} + |f|²_{ℋ⁶})/2` (pointwise AM–GM); the product form needs genuine
Cauchy–Schwarz, which is what is proved here: at each radial slice `√ρ·X` and `√ρ·Y` are
`L²` (their squares are dominated by the two slices of `HkIntegrand α 6`), the slice
Cauchy–Schwarz `cs_sqrt_le_fts` bounds the angular pairing by the product of the two slice
norms, and a second `cs_sqrt_le_fts` in `z` turns that into `√(HkSq α 6 u)·√(HkSq α 6 f)`.

The engine is stated at an arbitrary level `n` (`pairing_cs_le`), since the proof never uses
`n = 6`; the target instantiates it with the leaf-slot domination `domLeaf_all` of
`H6Pair6Aux/T5bPrep`.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.IPGen.slotPairing_abs_le
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

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
