/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Dispatch.RadAux` — the slice tools of the truncated `w²`-energy inequality

This is a *self-contained copy* of the slice-level toolkit of
`Submission/Work/FTS/EllipticEst/Prop/aeCutEnergyV2.lean` (lines 1–503 there): the a.e.
strong measurability and slicewise integrability of the angular fibres of a datum
`H2W.Ae.AeData α u G`, together with the elementary facts about the weights `w`, `σ = sEta`
and the interval `Iθ`.  The copy exists because the original module now imports the
work-in-progress `Prop.cutEnergyProof`, while the statements below are stable; the namespace
is renamed so that no clash arises when both are imported.

The only name *not* copied is `Prop.sliceLintegralConv`, which lives in its own module
`Prop/sliceLintegralConv.lean` and is imported directly by the consumers.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon
import Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.AngAWeak.CutEnergy.aeCutAfiniteA
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `aeCutEnergyV2` — the truncated `w²`-weighted energy inequality

Elgindi, Annals **194** (2021), Step 1 of `prop:H2`: for a datum `AeData α u G` of the
almost-everywhere class of the level-`0` elliptic estimate and an admissible cut-off `φ`
(`C²`, compactly supported, `0 ≤ φ ≤ 1`, vanishing on a neighbourhood of `z = 0`),

`α²∫⁻ (φw²z²)(∫⁻ (∂_zu)²) + ∫⁻ (φw²)(∫⁻ (∂_θu)²)
  ≤ K ∫⁻ (φw²)(∫⁻ u²) + ½∫⁻ (φw²)(∫⁻ G²σ) + err`,

with `K = 13/2 + 3α² + (3/2)α(5+α)` and the explicit truncation error `err`.

## The route

1. the *radial identity* `Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon` (proved, sorry-free) is
   the two radial integrations by parts already performed *inside* the `z`-integral;
2. the equation `bslOp α u = G` on the open quadrant turns its left-hand side into
   `∫_z φw² ∫_θ G u`;
3. the angular slice self-form `Work.FTS.EllipticEst.Honest.LzeroSelfFormHon` bounds
   `∫_θ (∂_θu)²` by `∫_θ Lzero u · u + 6∫_θ u²` for a.e. `z`;
4. AM–GM bounds `∫_z φw² ∫_θ G u ≤ ½∫_z φw² ∫_θ G² + ½∫_z φw² ∫_θ u²`;
5. the weight algebra `(z²w²)'' ≤ 6w²`, `-(zw²)' ≤ 3w²` bounds the two brackets;
6. `∫⁻`/`ofReal` conversions convert the resulting real inequality into the goal.

All the analysis is done at the level of *Bochner* integrals over the compact support of `φ`;
the two elementary facts used throughout are `w z ≥ 1` for `z > 0` and
`sin(2θ)^{-η} ≥ 1` for `θ ∈ (0,π/2)`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch.RadAux

set_option autoImplicit false

/-! ## Elementary facts about the angular weight -/

/-- Almost every `θ ∈ Iθ` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have h : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- `σ θ = sin(2θ)^{-η} ≥ 1` on the open interval. -/
theorem one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h : (1 : ℝ) ^ (-Work.Spaces.eta) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
    Real.rpow_le_rpow_of_nonpos hs hs1 (by have := Work.Spaces.eta_pos; linarith)
  simpa [Work.FTS.EllipticEst.sEta] using h

/-- `σ θ ≥ 0` on `Iθ`. -/
theorem sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> linarith [hθ.1, hθ.2, Real.pi_pos]

/-- `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

/-- `w z ≥ 0` for `z > 0`. -/
theorem w_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ Work.Spaces.w z := le_trans zero_le_one (one_le_w hz)

/-- `w z ^ 2 ≥ 1` for `z > 0`. -/
theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  nlinarith [one_le_w hz]

/-! ## The angular slices of a datum -/

/-- `P z = ∫_θ (u z θ)²`. -/
def sliceP (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2

/-- `A z = ∫_θ (∂_z u z θ)²`. -/
def sliceA (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2

/-- `B z = ∫_θ (∂_θ u z θ)²`. -/
def sliceB (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2

/-- `Q z = ∫_θ Lzero u z θ · u z θ`. -/
def sliceQ (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ

/-- `GU z = ∫_θ G z θ · u z θ`. -/
def sliceGU (u G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, G z θ * u z θ

/-- `C z = ∫_θ bslOp α u z θ · u z θ` (a.e. equal to `sliceGU`). -/
def sliceC (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ

/-- `Fg z = ∫_θ (G z θ)² σ θ`. -/
def sliceFg (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- `Cg z = ∫_θ (bslOp α u z θ)² σ θ` (a.e. equal to `sliceFg`). -/
def sliceCg (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Elliptic.bslOp α u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ

/-- The cut-off weight `W z = φ z · w z ^ 2`. -/
def cutW (φ : ℝ → ℝ) (z : ℝ) : ℝ := φ z * (Work.Spaces.w z) ^ 2

/-- `W z · z²`. -/
def cutWz2 (φ : ℝ → ℝ) (z : ℝ) : ℝ := cutW φ z * z ^ 2

/-- `W z · z`. -/
def cutWz1 (φ : ℝ → ℝ) (z : ℝ) : ℝ := cutW φ z * z

/-! ## Almost-everywhere strong measurability of the slices -/

/-- A slice integral of a jointly continuous function is a.e.-strongly measurable. -/
theorem aesm_sliceIntegral {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, F (z, θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd F hF).integral_prod_right'

/-- The uncurried `Lzero u · u` is continuous on the open quadrant. -/
theorem continuousOn_Lzero_mul {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Real.tan θ * u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hu
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero u) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hu 2))
        h1.pth)
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 hu)
  exact h2.continuousOn.mul hu.continuousOn

/-! ## Measurability and integrability of the slices -/

/-- The restrictions of `volume` to `Iθ` and to the open interval agree. -/
theorem hθ_eq : (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) : Measure ℝ)
    = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc

/-- Continuity on the open interval gives a.e.-strong measurability on `Iθ`. -/
theorem aesm_slice_of_cont_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (hf.aestronglyMeasurable measurableSet_Ioo).mono_measure (le_of_eq hθ_eq.symm)

/-- The `θ`-slice at `z > 0` of a function smooth on the open quadrant is a.e.-strongly
measurable. -/
theorem aesm_slice_of_smoothOpen {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => F z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  aesm_slice_of_cont_Ioo ((hF.curry_θ hz).continuousOn)

/-- `bslOp α u` is smooth on the open quadrant when `u` is. -/
theorem smoothOpen_bslOp {α : ℝ} {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
  Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hu

/-- `HkMem α 0 f` gives the *unweighted* slicewise square-integrability of `f` at every `z > 0`. -/
theorem integrableOn_sq_of_hkMem {α z : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) (hz : 0 < z)
    (haesm : AEStronglyMeasurable (fun θ => f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  refine (hm.1 z hzI).mono' (haesm.pow 2) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have h1 := Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z
    (θ := θ) (Set.Ioo_subset_Icc_self hθ)
  have hw := one_le_w_sq hz
  have hs := one_le_sEta hθ
  have hf2 : 0 ≤ (f z θ) ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg hf2, h1]
  calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 * 1 := by ring
    _ ≤ (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw hf2) hs (by norm_num) (by positivity)

/-- `∫_θ (u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceP {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {z : ℝ} (hz : 0 < z) : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_hkMem (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h) hz
    (aesm_slice_of_smoothOpen (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) hz)

/-- `∫_θ (z ∂_z u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceGrad {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_hkMem (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h) hz
    (aesm_slice_of_smoothOpen
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pz (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)))
      hz)

/-- `∫_θ (∂_z u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceA {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {z : ℝ} (hz : 0 < z) : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2)
      Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2)⁻¹ * (z * Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ :=
    (integrableOn_sliceGrad h hz).const_mul _
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 (ne_of_gt hz))]
  ring

/-- `∫_θ (z² ∂_z²u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceRad2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2)
      Work.Spaces.Iθ :=
  integrableOn_sq_of_hkMem h.memRad2 hz
    (aesm_slice_of_smoothOpen
      (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
        Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
        (Work.FTS.EllipticEst.SmoothOpen.pzIter (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth) 2))
      hz)

/-- `∫_θ (∂_z²u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceZ2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => ((z ^ 2) ^ 2)⁻¹ * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
    (integrableOn_sliceRad2 h hz).const_mul _
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz)))]
  ring

/-- `∫_θ (∂_θ²u z θ)²` is honest at every `z > 0`. -/
theorem integrableOn_sliceAng2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2) Work.Spaces.Iθ :=
  integrableOn_sq_of_hkMem h.memAng2 hz
    (aesm_slice_of_smoothOpen
      (Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth
        (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))) hz)

/-- `G z ·` is a.e.-strongly measurable for `z > 0` (it agrees a.e. with `bslOp α u z ·`). -/
theorem aesm_slice_G {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun θ => G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hbsl : AEStronglyMeasurable (fun θ => Work.Elliptic.bslOp α u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    aesm_slice_of_smoothOpen
      (smoothOpen_bslOp (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth)) hz
  refine hbsl.congr ?_
  rw [← hθ_eq]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  exact h.eq z hz θ hθ.1 hθ.2

/-- `θ ↦ sin(2θ)^{-η}` is continuous on the open interval. -/
theorem continuousOn_sEta :
    ContinuousOn Work.FTS.EllipticEst.sEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hfun : Work.FTS.EllipticEst.sEta
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := rfl
  rw [hfun]
  refine ContinuousOn.rpow_const ?_ (fun θ hθ => Or.inl ?_)
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))

/-- `∫_θ (G z θ)² σ θ` is honest at every `z > 0`. -/
theorem integrableOn_sliceFg {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  refine (h.memG.1 z hzI).mono'
    ((aesm_slice_G h hz).pow 2 |>.mul (aesm_slice_of_cont_Ioo continuousOn_sEta)) ?_
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have h1 := Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α G z
      (θ := θ) (Set.Ioo_subset_Icc_self hθ)
    have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
    have hG2 : 0 ≤ (G z θ) ^ 2 := sq_nonneg _
    have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg (Set.Ioo_subset_Icc_self hθ)
    rw [Real.norm_of_nonneg (mul_nonneg hG2 hs), h1]
    calc (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (G z θ) ^ 2 * 1 * Work.FTS.EllipticEst.sEta θ := by ring
      _ ≤ (G z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hG2) hs

/-- `θ ↦ (∂_θu z θ)²` has the constant bound `C²` on the open interval. -/
theorem integrableOn_sliceB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  refine MeasureTheory.IntegrableOn.of_bound (μ := MeasureTheory.volume)
    (measure_Icc_lt_top (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2)) ?_ (C ^ 2) ?_
  · exact (aesm_slice_of_smoothOpen
      (Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
      hz).pow 2
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hb := (hC θ hθ).2
    have hpth : Work.Spaces.pth u z θ = deriv (fun θ' : ℝ => u z θ') θ := rfl
    rw [Real.norm_of_nonneg (sq_nonneg _), hpth]
    calc deriv (fun θ' : ℝ => u z θ') θ ^ 2 = |deriv (fun θ' : ℝ => u z θ') θ| ^ 2 :=
          (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2

/-! ## Measurability of the weight and the `σ`-dominated slices -/

/-- `z ↦ w z ^ 2` is measurable. -/
theorem measurable_w_sq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact (Measurable.div ((measurable_const.add measurable_id).pow_const 2)
    (measurable_id.pow_const 2)).pow_const 2

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_of_mem_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
  intro z hz
  simp only [Set.mem_setOf_eq, not_imp, Set.mem_Ici, Set.mem_singleton_iff] at hz
  exact le_antisymm (le_of_not_gt hz.2) hz.1

/-- `HkMem α 0 f` gives the `σ`-weighted slicewise square-integrability of `f` at every `z > 0`. -/
theorem integrableOn_slice_sigma_of_hkMem {α z : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) (hz : 0 < z)
    (haesm : AEStronglyMeasurable (fun θ => f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  refine (hm.1 z hzI).mono'
    ((haesm.pow 2).mul (aesm_slice_of_cont_Ioo continuousOn_sEta)) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have h1 := Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z
    (θ := θ) (Set.Ioo_subset_Icc_self hθ)
  have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
  have hf2 : 0 ≤ (f z θ) ^ 2 := sq_nonneg _
  have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg (Set.Ioo_subset_Icc_self hθ)
  rw [Real.norm_of_nonneg (mul_nonneg hf2 hs), h1]
  calc (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (f z θ) ^ 2 * 1 * Work.FTS.EllipticEst.sEta θ := by ring
    _ ≤ (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hf2) hs

/-- `HkMem α 0 f` gives the `z`-integrability of `z ↦ w z² ∫_θ (f z θ)² σ θ`. -/
theorem integrableOn_w2_slice_sigma_of_hkMem {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz := by
  refine hm.2.congr_fun (fun z _ => ?_) measurableSet_Ici
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
    (Filter.Eventually.of_forall (fun θ hθ => ?_))
  rw [Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α f z hθ]
  ring

/-- `sliceP u` is dominated by the `σ`-weighted slice integral. -/
theorem sliceP_le_slice_sigma {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    sliceP u z ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine MeasureTheory.integral_mono_ae (integrableOn_sliceP h hz)
    (integrableOn_slice_sigma_of_hkMem (Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h) hz
      (aesm_slice_of_smoothOpen hSO hz)) ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hs : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta hθ
  nlinarith [sq_nonneg (u z θ)]

/-- `z ↦ sliceP u z` is a.e.-strongly measurable. -/
theorem aesm_sliceP {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable (fun z : ℝ => sliceP u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hSO.continuousOn).comp (by fun_prop) (fun p hp => hp)).pow 2
  exact aesm_sliceIntegral hcont

/-- `z ↦ ∫_θ (z ∂_zu z θ)²` is a.e.-strongly measurable. -/
theorem aesm_sliceGrad {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_fst.mul (hSO.pz).continuousOn)).pow 2
  exact aesm_sliceIntegral hcont

/-- `z ↦ ∫_θ (z² ∂_z²u z θ)²` is a.e.-strongly measurable. -/
theorem aesm_sliceRad2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_fst.pow 2).mul (hSO.pzIter 2).continuousOn).pow 2
  exact aesm_sliceIntegral hcont

/-- `z ↦ ∫_θ (∂_θu z θ)²` is a.e.-strongly measurable. -/
theorem aesm_sliceB {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable (fun z : ℝ => sliceB u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hSO.pth).continuousOn.pow 2
  exact aesm_sliceIntegral hcont

/-- `z ↦ sliceQ u z` is a.e.-strongly measurable. -/
theorem aesm_sliceQ {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable (fun z : ℝ => sliceQ u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
  aesm_sliceIntegral (continuousOn_Lzero_mul (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))

/-- `z ↦ sliceFg G z` is a.e.-strongly measurable. -/
theorem aesm_sliceFg {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable (fun z : ℝ => sliceFg G z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont1 : ContinuousOn
      (fun p : ℝ × ℝ => (Work.Elliptic.bslOp α u p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((smoothOpen_bslOp hSO).continuousOn).pow 2).mul
      (continuousOn_sEta.comp continuousOn_snd (fun p hp => hp.2))
  have haesm1 : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Elliptic.bslOp α u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := aesm_sliceIntegral hcont1
  refine haesm1.congr ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  refine MeasureTheory.integral_congr_ae ?_
  rw [← hθ_eq]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  simp only [h.eq z hz θ hθ.1 hθ.2]

/-- `z ↦ w z² · sliceP u z` is integrable. -/
theorem integrableOn_w2_sliceP {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceP u z)
      Work.Spaces.Iz := by
  have hm := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hbig : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz :=
    integrableOn_w2_slice_sigma_of_hkMem hm
  refine hbig.mono' (measurable_w_sq.aestronglyMeasurable.mul (aesm_sliceP h)) ?_
  filter_upwards [ae_pos_of_mem_Iz] with z hz
  have hP0 : 0 ≤ sliceP u z := MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  have hle := sliceP_le_slice_sigma h hz
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hP0)]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- `z ↦ w z² · sliceFg G z` is integrable. -/
theorem integrableOn_w2_sliceFg {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * sliceFg G z)
      Work.Spaces.Iz :=
  integrableOn_w2_slice_sigma_of_hkMem h.memG

/-- `z ↦ w z² · ∫_θ (z²∂_z²u z θ)²σ θ` is integrable. -/
theorem integrableOn_w2_sliceRad2 {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
  integrableOn_w2_slice_sigma_of_hkMem h.memRad2

/-- `z ↦ w z² · ∫_θ (z ∂_zu z θ)²σ θ` is integrable. -/
theorem integrableOn_w2_sliceGrad {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
  integrableOn_w2_slice_sigma_of_hkMem (Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h)

end Work.FTS.EllipticEst.Dispatch.RadAux
