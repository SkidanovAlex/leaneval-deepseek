import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.RadAux =====
section

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




/-- `Q z = ∫_θ Lzero u z θ · u z θ`. -/
def sliceQ (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ


/-- `C z = ∫_θ bslOp α u z θ · u z θ` (a.e. equal to `sliceGU`). -/
def sliceC (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ



/-- The cut-off weight `W z = φ z · w z ^ 2`. -/
def cutW (φ : ℝ → ℝ) (z : ℝ) : ℝ := φ z * (Work.Spaces.w z) ^ 2



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














end Work.FTS.EllipticEst.Dispatch.RadAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- The radial weight of the truncated identity: `om W z = W z · w z ²`. -/
def om (W : ℝ → ℝ) : ℝ → ℝ := fun z => W z * (Work.Spaces.w z) ^ 2

/-- `om W z · z²`, the weight of `∂_zzu`. -/
def om2 (W : ℝ → ℝ) : ℝ → ℝ := fun z => om W z * z ^ 2

/-- `om W z · z`, the weight of `∂_zu`. -/
def om1 (W : ℝ → ℝ) : ℝ → ℝ := fun z => om W z * z

@[simp] theorem om_apply (W : ℝ → ℝ) (z : ℝ) : om W z = W z * (Work.Spaces.w z) ^ 2 := rfl
@[simp] theorem om2_apply (W : ℝ → ℝ) (z : ℝ) : om2 W z = om W z * z ^ 2 := rfl
@[simp] theorem om1_apply (W : ℝ → ℝ) (z : ℝ) : om1 W z = om W z * z := rfl

/-- The product measure `dz dθ` over `Iz × Iθ`. -/
abbrev msig : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Iz).prod (MeasureTheory.volume.restrict Iθ)

/-! ## The `z`-slice functionals of the `σ`-weighted analysis -/

/-- `sigR u z = ∫_θ σ θ · u(z,θ)²`. -/
def sigR (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, sg θ * (u z θ) ^ 2


/-- `sigG G z = ∫_θ σ θ · G(z,θ)²`. -/
def sigG (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ := ∫ θ in Iθ, sg θ * (G z θ) ^ 2




/-! ## Nonnegativity of the `ℋ⁰` slots -/

theorem sEta_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  rw [Work.FTS.EllipticEst.sEta]
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _



theorem sigG_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ sigG G z := by
  rw [sigG]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun θ hθ => mul_nonneg (sEta_nonneg_of_mem hθ) (sq_nonneg _))


/-- Linearity of the Bochner integral in the `c₁f₁ + f₂ - c₃f₃ + c₄f₄` shape. -/
theorem integral_lin4 {μ : MeasureTheory.Measure ℝ} {f1 f2 f3 f4 : ℝ → ℝ} {c1 c3 c4 : ℝ}
    (h1 : MeasureTheory.Integrable f1 μ) (h2 : MeasureTheory.Integrable f2 μ)
    (h3 : MeasureTheory.Integrable f3 μ) (h4 : MeasureTheory.Integrable f4 μ) :
    (∫ x, (c1 * f1 x + f2 x - c3 * f3 x + c4 * f4 x) ∂μ)
      = c1 * (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) - c3 * (∫ x, f3 x ∂μ)
        + c4 * (∫ x, f4 x ∂μ) := by
  have hAB : MeasureTheory.Integrable (fun x => c1 * f1 x + f2 x) μ :=
    (h1.const_mul c1).add h2
  have hC : MeasureTheory.Integrable (fun x => c3 * f3 x) μ := h3.const_mul c3
  have hD : MeasureTheory.Integrable (fun x => c4 * f4 x) μ := h4.const_mul c4
  have hABC : MeasureTheory.Integrable (fun x => c1 * f1 x + f2 x - c3 * f3 x) μ :=
    hAB.sub hC
  rw [MeasureTheory.integral_add hABC hD, MeasureTheory.integral_sub hAB hC,
    MeasureTheory.integral_add (h1.const_mul c1) h2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-! ## The `σ`-weighted truncated radial energy identity -/

/-- **The `σ`-weighted truncated radial identity.**  This is the identity
`aeTruncIdent_core` of the colleague's module with the angular integration weighted by
`σ = sin(2θ)^{-η}` instead of being unweighted: it is `Honest.zIBP_compact` applied to each
`θ`-slice and then Fubini'd against `σ`.

The five joint-integrability inputs are kept as hypotheses; they are discharged from the
`ℋ⁰`-membership of `u`, `G`, `z ∂_zu` and `z²∂_zzu` in the consumer. -/
theorem sigTruncIdentD (α : ℝ) (u G : ℝ → ℝ → ℝ) (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    (hWcpt : HasCompactSupport W) (hW0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z, z ≤ δ → W z = 0)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α u z θ = G z θ)
    (hJ1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))) msig)
    (hJ2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (om W p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) msig)
    (hJ3 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (deriv (om2 W)) p.1 * (u p.1 p.2) ^ 2)) msig)
    (hJ4 : MeasureTheory.Integrable (fun p : ℝ × ℝ => sg p.2 *
      (deriv (om1 W) p.1 * (u p.1 p.2) ^ 2)) msig)
    (hJ5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig)
    (hsl : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z => u z θ) (Set.Ioi 0)) :
    (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Iz, om2 W z * (∫ θ in Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Iz, deriv (deriv (om2 W)) z *
            (∫ θ in Iθ, sg θ * (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ z in Iz, deriv (om1 W) z *
            (∫ θ in Iθ, sg θ * (u z θ) ^ 2)) := by
  obtain ⟨δ, hδ0, hδW⟩ := hW0
  obtain ⟨R, hR0, hRW⟩ := Work.FTS.EllipticEst.AngAWeak.exists_bound_W W hWcpt
  have hδR : min δ R ≤ R := min_le_right _ _
  have hδmin0 : 0 < min δ R := lt_min hδ0 hR0
  have hδminW : ∀ z, z ≤ min δ R → W z = 0 := fun z hz =>
    hδW z (le_trans hz (min_le_left _ _))
  -- ## Step 1: replace `G` by `bslOp α u` on the left-hand side
  have hbsl : (∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (G z θ * u z θ)))
      = ∫ z in Iz, om W z *
          (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    by_cases hzδ : z ≤ min δ R
    · have h0 : om W z = 0 := by rw [om, hδminW z hzδ]; ring
      rw [h0, zero_mul, zero_mul]
    · have hz0 : 0 < z := lt_trans hδmin0 (lt_of_not_ge hzδ)
      congr 1
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
      show sg θ * (G z θ * u z θ) = sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)
      rw [heq z hz0 θ hθ.1 hθ.2]
  -- ## Step 2: Fubini on the left-hand side
  have hfub1 : (∫ z in Iz, om W z *
        (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Iθ, sg θ *
          (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
    have h1 : (∫ z in Iz, om W z *
          (∫ θ in Iθ, sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
        = ∫ z in Iz, ∫ θ in Iθ,
            om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
      rw [MeasureTheory.integral_const_mul]
    rw [h1, MeasureTheory.integral_integral_swap
      (f := fun z θ => om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ1]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    rw [show (fun z => om W z * (sg θ * (Work.Elliptic.bslOp α u z θ * u z θ)))
        = fun z => sg θ * (om W z * (Work.Elliptic.bslOp α u z θ * u z θ)) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  -- ## Step 3: the per-`θ` identity, a.e. in `θ`
  have hJ5' : MeasureTheory.Integrable (fun p : ℝ × ℝ => om W p.1 *
      (sg p.2 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig := hJ5
  have hslice_lz : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), MeasureTheory.IntegrableOn
      (fun z => om W z * (Work.Elliptic.Lzero u z θ * u z θ)) Iz := by
    filter_upwards [hJ5.prod_left_ae, Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ]
      with θ hJ hθ
    have hne : sg θ ≠ 0 := by
      have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta_of_mem_Ioo hθ
      linarith
    have h3 := hJ.const_mul ((sg θ)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
    show (sg θ)⁻¹ * (om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
      = om W z * (Work.Elliptic.Lzero u z θ * u z θ)
    rw [show (sg θ)⁻¹ * (om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)))
        = ((sg θ)⁻¹ * sg θ) * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)) from by ring,
      inv_mul_cancel₀ hne, one_mul]
  have hper : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
      (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ))
        = α ^ 2 * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2)
          + (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ))
          - (α ^ 2 / 2) * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2)
          + (α * (5 + α) / 2) * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2) := by
    filter_upwards [hslice_lz, Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hlz hθ
    exact Work.FTS.EllipticEst.AngAWeak.sliceIBP α u W hW2 hδmin0 hδR hθ hδminW hRW
      (hsl θ hθ) hlz
  -- ## Step 4: integrate in `θ` and use linearity
  have hJ2'' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      sg p.2 * (om2 W p.1 * (Work.Spaces.pz u p.1 p.2) ^ 2)) msig :=
    hJ2.congr (Filter.Eventually.of_forall fun p => by
      simp only [om2_apply, om_apply]; ring)
  have hI2 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ2''.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hJ5'' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      sg p.2 * (om W p.1 * (Work.Elliptic.Lzero u p.1 p.2 * u p.1 p.2))) msig :=
    hJ5.congr (Filter.Eventually.of_forall fun p => by ring)
  have hI5 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ5''.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hI3 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ3.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hI4 : MeasureTheory.Integrable
      (fun θ => sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Iθ) := by
    refine hJ4.integral_prod_right.congr ?_
    filter_upwards with θ
    rw [MeasureTheory.integral_const_mul]
  have hcomb : (∫ θ in Iθ, sg θ *
        (∫ z in Iz, om W z * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Iθ,
          (α ^ 2 * (sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
            + (sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
            - (α ^ 2 / 2) * (sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
            + (α * (5 + α) / 2) * (sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hper] with θ hθ
    rw [hθ]
    ring
  have hlin : (∫ θ in Iθ,
          (α ^ 2 * (sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
            + (sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
            - (α ^ 2 / 2) * (sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
            + (α * (5 + α) / 2) * (sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))))
      = α ^ 2 * (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ θ in Iθ, sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        - (α ^ 2 / 2) * (∫ θ in Iθ, sg θ *
            (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ θ in Iθ, sg θ *
            (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2)) :=
    integral_lin4 hI2 hI5 hI3 hI4
  -- ## Step 5: Fubini back for the four terms
  have f1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Iz, om2 W z * (∫ θ in Iθ, sg θ * (Work.Spaces.pz u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ2'']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (om2 W z * (Work.Spaces.pz u z θ) ^ 2))
        = fun θ => om2 W z * (sg θ * (Work.Spaces.pz u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f2 : (∫ θ in Iθ, sg θ *
        (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      = ∫ z in Iz, om W z * (∫ θ in Iθ, sg θ * (Work.Elliptic.Lzero u z θ * u z θ)) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ5'']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (om W z * (Work.Elliptic.Lzero u z θ * u z θ)))
        = fun θ => om W z * (sg θ * (Work.Elliptic.Lzero u z θ * u z θ)) from by
      funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f3 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      = ∫ z in Iz, deriv (deriv (om2 W)) z * (∫ θ in Iθ, sg θ * (u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ3]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (deriv (deriv (om2 W)) z * (u z θ) ^ 2))
        = fun θ => deriv (deriv (om2 W)) z * (sg θ * (u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  have f4 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
      = ∫ z in Iz, deriv (om1 W) z * (∫ θ in Iθ, sg θ * (u z θ) ^ 2) := by
    have h1 : (∫ θ in Iθ, sg θ * (∫ z in Iz, deriv (om1 W) z * (u z θ) ^ 2))
        = ∫ θ in Iθ, ∫ z in Iz, sg θ * (deriv (om1 W) z * (u z θ) ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
      rw [← MeasureTheory.integral_const_mul]
    rw [h1, ← MeasureTheory.integral_integral_swap (f := fun z θ =>
      sg θ * (deriv (om1 W) z * (u z θ) ^ 2))
      (μ := MeasureTheory.volume.restrict Iz)
      (ν := MeasureTheory.volume.restrict Iθ) hJ4]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
    rw [show (fun θ => sg θ * (deriv (om1 W) z * (u z θ) ^ 2))
        = fun θ => deriv (om1 W) z * (sg θ * (u z θ) ^ 2) from by funext θ; ring,
      MeasureTheory.integral_const_mul]
  rw [hbsl, hfub1, hcomb, hlin, f1, f2, f3, f4]

end Work.FTS.EllipticEst.Dispatch
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-integrated radial integration by parts of the truncated energy identity

This module proves `Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta`: for a datum `u` which is
`C^∞` on the open quadrant `(0,∞) × (0,π/2)` and honestly in `ℋ⁰` (i.e. `HkMem α 0` of `u`,
`z ∂_z u` and `z²∂_z²u`), and a compactly supported `C²` radial weight `ω` (supported in `[a,b]`,
`0 < a < b`) which is bounded by the square of the radial weight `w`,

`∫_0^∞ ω(z) ∫_θ σ(θ)(α²z²∂_z²u + α(5+α)z∂_zu)·u
  = -α²∫_0^∞ ω(z)∫_θ σ(θ)(z∂_zu)²
    + (α²/2)∫_0^∞ (z²ω)''(z)∫_θ σ(θ)u²
    - (α(5+α)/2)∫_0^∞ (zω)'(z)∫_θ σ(θ)u²`,  `σ = sin(2θ)^{-η}`.

Route: the per-`θ` radial identity `Honest.zIBP_compact`, applied to the `z`-slices
`z ↦ u z θ` for a.e. `θ ∈ Iθ`, followed by an exchange of the two integrals (Fubini, whose
integrability hypothesis comes from the three `ℋ⁰`-memberships and `|ω| ≤ w²`).
-/

noncomputable section

namespace Work.FTS.EllipticEst.Dispatch

open MeasureTheory Set Filter
open scoped Topology Real

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The Fubini/Tonelli swap of the `z`- and `θ`-integrations -/

/-- **Fubini for the iterated integrals over `(0,∞) × Iθ`.**  If `(z,θ) ↦ K z · G z θ` is
integrable against the product measure `nuFts = dz|_{(0,∞)} × dθ|_{Iθ}`, then the `z`-outer
iterated integral is the `θ`-outer iterated integral.  This is `integral_integral_swap`
together with the pointwise `K z * ∫ = ∫ K z *` (`integral_const_mul`). -/
theorem tRibp_swapRadial {K : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => K p.1 * G p.1 p.2) nuFts) :
    (∫ z in Set.Ioi (0 : ℝ), K z * (∫ θ in Work.Spaces.Iθ, G z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ), K z * G z θ := by
  have h1 : (∫ z in Set.Ioi (0 : ℝ), K z * (∫ θ in Work.Spaces.Iθ, G z θ))
      = ∫ z, ∫ θ, K z * G z θ
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact (MeasureTheory.integral_const_mul (K z) (fun θ => G z θ)).symm
  rw [h1]
  exact MeasureTheory.integral_integral_swap hint

/-! ## The pointwise-in-`θ` radial identity -/

/-- **The radial integration by parts on a single angular slice.**  For a.e. `θ ∈ Iθ` the
`θ`-weight `σ(θ) = sEta θ` is a constant for the `z`-integral, so `Honest.zIBP_compact` applied
to the slice `z ↦ u z θ` gives the identity with the weight. -/
theorem tRibp_sliceIbpSeta {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z *
            (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  have hsl : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) := by
    have h2 := hsm 2
    have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi 0)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun z hz => ⟨hz, hθ⟩
    exact h2.comp (by fun_prop) hmap
  have hkey := Work.FTS.EllipticEst.Honest.zIBP_compact α ω (fun z : ℝ => u z θ)
    ha hab hωsupp hωd hsl
  have key : ∀ (F : ℝ → ℝ), (∫ z in Set.Ioi (0 : ℝ), ω z *
        (Work.FTS.EllipticEst.sEta θ * F z))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), ω z * F z) := by
    intro F
    rw [show (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ * F z))
        = ∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.sEta θ * (ω z * F z) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have key2 : ∀ (G : ℝ → ℝ), (∫ z in Set.Ioi (0 : ℝ),
        G z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), G z * (u z θ) ^ 2) := by
    intro G
    rw [show (∫ z in Set.Ioi (0 : ℝ), G z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        = ∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.sEta θ * (G z * (u z θ) ^ 2) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
    rw [MeasureTheory.integral_const_mul]
  have hL : (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), ω z *
          (α ^ 2 * z ^ 2 * deriv (deriv (fun z : ℝ => u z θ)) z
            + (α * (5 + α) * z) * deriv (fun z : ℝ => u z θ) z) * u z θ) := by
    rw [key (fun z => (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    simp only [Work.Spaces.pz, Work.Spaces.pzIter, Work.Spaces.pzIter_succ,
      Work.Spaces.pzIter_zero]
    ring
  rw [hL, hkey, key (fun z => (z * Work.Spaces.pz u z θ) ^ 2),
    key2 (fun z => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z),
    key2 (fun z => deriv (fun y : ℝ => y * ω y) z)]
  simp only [Work.Spaces.pz]
  ring

/-! ## Vanishing off the support `[a,b]` and bounds for the weight coefficients -/

/-- `ω = 0` in a neighbourhood of every point outside `[a,b]`. -/
private lemma tRibp_omega_eventually_zero {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → ω =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  rcases hz' with hlt | hgt
  · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
    exact hω0 w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
  · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
    exact hω0 w (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)

private lemma tRibp_deriv_one_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => y * ω y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [tRibp_omega_eventually_zero hω0 z hz] with y hy
    rw [hy]; ring
  rw [hev.deriv_eq]; simp

private lemma tRibp_deriv_two_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (fun y : ℝ => y ^ 2 * ω y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [tRibp_omega_eventually_zero hω0 z hz] with y hy
    rw [hy]; ring
  rw [hev.deriv_eq]; simp

private lemma tRibp_deriv_two_two_off {ω : ℝ → ℝ} {a b : ℝ}
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∀ z : ℝ, z ∉ Set.Icc a b → deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z = 0 := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  have hev : deriv (fun y : ℝ => y ^ 2 * ω y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
      exact tRibp_deriv_two_off hω0 w
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hw)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with w hw
      exact tRibp_deriv_two_off hω0 w
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hw)
  rw [hev.deriv_eq]; simp

/-- The two weight coefficients `(z²ω)''` and `(zω)'` are globally bounded.  Both vanish off
`[a,b]` (since `ω` does, near every point outside it) and are continuous on the compact `[a,b]`
(as `ω` is `C²` on `(0,∞) ⊇ [a,b]`). -/
theorem tRibp_exists_bound_derivs {ω : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hω0 : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z : ℝ, |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ M)
      ∧ (∀ z : ℝ, |deriv (fun y : ℝ => y * ω y) z| ≤ M) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hW2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2' : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hZ2 : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hc2 : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Icc a b) :=
    (hW2'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hc1 : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Icc a b) :=
    (hZ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  refine ⟨max (max M2 M1) 0, le_max_right _ _, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ Set.Icc a b
    · have h := hM2 z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [tRibp_deriv_two_two_off hω0 z hz, abs_zero]
      exact le_max_right _ _
  · intro z
    by_cases hz : z ∈ Set.Icc a b
    · have h := hM1 z hz
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [tRibp_deriv_one_off hω0 z hz, abs_zero]
      exact le_max_right _ _


/-- `σ(θ) = sEta θ = sin(2θ)^{-η}` is continuous on the open quadrant. -/
theorem tRibp_continuousOn_sEta :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hpow : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun p hp =>
      Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos]))))
  exact hpow

/-- The elementary AM–GM bound `|A|·|B| ≤ (A² + B²)/2`. -/
private lemma tRibp_abs_mul_le_half (A B : ℝ) : |A| * |B| ≤ (A ^ 2 + B ^ 2) / 2 := by
  nlinarith [sq_nonneg (|A| - |B|), abs_mul_abs_self A, abs_mul_abs_self B]

/-! ## Joint integrability of the four integrands -/

/-- **Joint integrability of the pairing integrands.**  The `ℋ⁰`-integrand of a function `g` is
`w(z)² g² σ(θ)`, and `σ ≥ 0`, `w ≥ 0`; with `|ω z| ≤ w(z)²` and `2|A||B| ≤ A² + B²` this
dominates the two `ω`-weighted pairings by sums of `ℋ⁰`-integrands of `z²∂_z²u`, `z∂_zu` and
`u`, all of which are integrable on `nuFts` by `HkMem α 0` (`integrable_HkIntegrand_of_smoothOpen`
plus the a.e. form `HkIntegrand_zero_D`). -/
theorem tRibp_integrablePair {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0)
    (hωbdd : ∀ z : ℝ, |ω z| ≤ (Work.Spaces.w z) ^ 2) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
        ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts
    ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hIu := integrable_HkIntegrand_of_smoothOpen huS hu
  have hIg := integrable_HkIntegrand_of_smoothOpen huS.Dz hgrad
  have hIr := integrable_HkIntegrand_of_smoothOpen
    (Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq huS) hrad2
  have hωcont : ContinuousOn (fun p : ℝ × ℝ => ω p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hPz2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (huS.pzIter 2).continuousOn
  have hPz1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.pz.continuousOn
  have hPsi : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.continuousOn
  -- the second conjunct
  have h2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 *
      (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts := by
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)) nuFts :=
      aesm_prod_of_continuousOn_Q0 (hωcont.mul (tRibp_continuousOn_sEta.mul
        (((continuous_fst.continuousOn).mul hPz1).pow 2)))
    refine hIg.mono' haesm ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hnn : 0 ≤ Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc |ω p.1| * (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
        ≤ (Work.Spaces.w p.1) ^ 2 *
            (Work.FTS.EllipticEst.sEta p.2 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2) :=
          mul_le_mul_of_nonneg_right (hωbdd p.1) hnn
      _ = Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2 := by
          rw [HkIntegrand_zero_D α _ hθ]; ring
  -- the first conjunct
  have h1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
        ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts := by
    have haesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => ω p.1 *
        (Work.FTS.EllipticEst.sEta p.2 *
          ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
            + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))) nuFts :=
      aesm_prod_of_continuousOn_Q0 (hωcont.mul (tRibp_continuousOn_sEta.mul
        ((((continuousOn_const.mul ((continuous_fst.continuousOn).pow 2)).mul hPz2).add
          ((continuousOn_const.mul continuous_fst.continuousOn).mul hPz1)).mul hPsi)))
    set K : ℝ := max 1 (max (α ^ 4 / 2) ((α * (5 + α)) ^ 2 / 2)) with hKdef
    have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one (le_max_left _ _)
    have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
    have hK2 : α ^ 4 / 2 ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK3 : (α * (5 + α)) ^ 2 / 2 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
    have hsum : MeasureTheory.Integrable (fun p : ℝ × ℝ => K *
        (Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2
          + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) p.1 p.2
          + Work.Spaces.HkIntegrand α 0 u p.1 p.2)) nuFts :=
      ((hIr.add hIg).add hIu).const_mul K
    refine hsum.mono' haesm ?_
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hw2 : (0 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    obtain ⟨z, θ⟩ := p
    have hcore : |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|
        ≤ (α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
          + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
          + (u z θ) ^ 2 := by
      have h1' := tRibp_abs_mul_le_half (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) (u z θ)
      have h2' := tRibp_abs_mul_le_half ((α * (5 + α) * z) * Work.Spaces.pz u z θ) (u z θ)
      rw [abs_mul]
      calc |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ| * |u z θ|
          ≤ (|α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz u z θ|) * |u z θ| :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
        _ = |α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ| * |u z θ|
              + |(α * (5 + α) * z) * Work.Spaces.pz u z θ| * |u z θ| := by ring
        _ ≤ ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2 + (u z θ) ^ 2) / 2
              + (((α * (5 + α) * z) * Work.Spaces.pz u z θ) ^ 2 + (u z θ) ^ 2) / 2 :=
            add_le_add h1' h2'
        _ = (α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
              + (u z θ) ^ 2 := by ring
    have hstep : |ω z| * (Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
            + (u z θ) ^ 2)) := by
      have h0 : 0 ≤ Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ| :=
        mul_nonneg hsEta (abs_nonneg _)
      calc |ω z| * (Work.FTS.EllipticEst.sEta θ *
            |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
          ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
              |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
                + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|) :=
            mul_le_mul_of_nonneg_right (hωbdd z) h0
        _ ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
              ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
                + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
                + (u z θ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore hsEta) hw2
    have hkey : (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
            + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
            + (u z θ) ^ 2))
        = (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ := by
      rw [HkIntegrand_zero_D α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) hθ,
        HkIntegrand_zero_D α (fun z θ => z * Work.Spaces.pz u z θ) hθ,
        HkIntegrand_zero_D α u hθ]
      ring
    have hnn3 : 0 ≤ Work.Spaces.HkIntegrand α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnn2 : 0 ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnn1 : 0 ≤ Work.Spaces.HkIntegrand α 0 u z θ :=
      Work.Spaces.HkIntegrand_nonneg _ _ _ z θ
    have hnnEta : 0 ≤ Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    have hnnAbs : 0 ≤ Work.FTS.EllipticEst.sEta θ *
        |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
          + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ| :=
      mul_nonneg hsEta (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hsEta]
    calc |ω z| * (Work.FTS.EllipticEst.sEta θ *
          |(α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ|)
        ≤ (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.sEta θ *
            ((α ^ 4 / 2) * (z ^ 2 * Work.Spaces.pzIter 2 u z θ) ^ 2
              + ((α * (5 + α)) ^ 2 / 2) * (z * Work.Spaces.pz u z θ) ^ 2
              + (u z θ) ^ 2)) := hstep
      _ = (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
              (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ := hkey
      _ ≤ K * (Work.Spaces.HkIntegrand α 0
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ
          + Work.Spaces.HkIntegrand α 0 u z θ) := by
          calc (α ^ 4 / 2) * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
              + ((α * (5 + α)) ^ 2 / 2) * Work.Spaces.HkIntegrand α 0
                  (fun z θ => z * Work.Spaces.pz u z θ) z θ
              + Work.Spaces.HkIntegrand α 0 u z θ
              ≤ K * Work.Spaces.HkIntegrand α 0
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + K * Work.Spaces.HkIntegrand α 0
                    (fun z θ => z * Work.Spaces.pz u z θ) z θ
                + K * Work.Spaces.HkIntegrand α 0 u z θ := by
                refine add_le_add (add_le_add ?_ ?_) ?_
                · exact mul_le_mul_of_nonneg_right hK2 hnn3
                · exact mul_le_mul_of_nonneg_right hK3 hnn2
                · simpa using mul_le_mul_of_nonneg_right hK1 hnn1
            _ = K * (Work.Spaces.HkIntegrand α 0
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz u z θ) z θ
                + Work.Spaces.HkIntegrand α 0 u z θ) := by ring
  exact ⟨h1, h2⟩

/-- **Joint integrability of the weight-coefficient integrands.**  With `M` a global bound for
`(z²ω)''` and `(zω)'` (they vanish off the compact `[a,b]` and are continuous there), the two
integrands `(z²ω)''(z)·σ(θ)u²` and `(zω)'(z)·σ(θ)u²` are dominated by `M` times
`HkIntegrand α 0 u` (using `w ≥ 1` on `(0,∞)` and `σ ≥ 0`). -/
theorem tRibp_integrableCoeff {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    (hωsupp : ∀ z : ℝ, z ∉ Set.Icc a b → ω z = 0) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) p.1 *
          (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)) nuFts
    ∧ MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (fun y : ℝ => y * ω y) p.1 *
          (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)) nuFts := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hIu := integrable_HkIntegrand_of_smoothOpen huS hu
  obtain ⟨M, hM0, hM2, hM1⟩ := tRibp_exists_bound_derivs (ω := ω) ha hωd hωsupp
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hW2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hW2' : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
    hW2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hZ2 : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have hc2 : ContinuousOn (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Ioi 0) :=
    hW2'.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hc1 : ContinuousOn (deriv (fun y : ℝ => y * ω y)) (Set.Ioi 0) :=
    hZ2.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hPsi : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := huS.continuousOn
  have hdom : ∀ᵐ p ∂nuFts, ∀ (c : ℝ → ℝ), (∀ z, |c z| ≤ M) →
      ‖c p.1 * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)‖
        ≤ M * Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
    filter_upwards [ae_mem_Ioi_nu, ae_mem_Ioo_nu] with p hp1 hp2
    intro c hc
    have hθ : p.2 ∈ Work.Spaces.Iθ := ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
    have hsEta : 0 ≤ Work.FTS.EllipticEst.sEta p.2 := sEta_nonneg_Iθ_D hθ
    have hnn : 0 ≤ Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2 :=
      mul_nonneg hsEta (sq_nonneg _)
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w p.1 := one_le_w_D hp1
    have hw2 : (1 : ℝ) ≤ (Work.Spaces.w p.1) ^ 2 := one_le_pow₀ hw1
    have hsq : Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2
        ≤ Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
      calc Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2
          = 1 * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2) := (one_mul _).symm
        _ ≤ (Work.Spaces.w p.1) ^ 2 *
              (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2) :=
            mul_le_mul_of_nonneg_right hw2 hnn
        _ = Work.Spaces.HkIntegrand α 0 u p.1 p.2 := by
            rw [HkIntegrand_zero_D α u hθ]; ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact le_trans (mul_le_mul_of_nonneg_right (hc p.1) hnn)
      (mul_le_mul_of_nonneg_left hsq hM0)
  refine ⟨?_, ?_⟩
  · refine integrable_of_le_const_mul_HkIntegrand hM0
      (aesm_prod_of_continuousOn_Q0 ((hc2.comp continuous_fst.continuousOn
        (fun p hp => hp.1)).mul (tRibp_continuousOn_sEta.mul (hPsi.pow 2)))) hIu ?_
    filter_upwards [hdom] with p hp
    exact hp _ hM2
  · refine integrable_of_le_const_mul_HkIntegrand hM0
      (aesm_prod_of_continuousOn_Q0 ((hc1.comp continuous_fst.continuousOn
        (fun p hp => hp.1)).mul (tRibp_continuousOn_sEta.mul (hPsi.pow 2)))) hIu ?_
    filter_upwards [hdom] with p hp
    exact hp _ hM1

/-! ## The target theorem -/

theorem truncRadialIbpTheta {α : ℝ} {u : ℝ → ℝ → ℝ} (ω : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0)) (hωsupp : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωbdd : ∀ z, |ω z| ≤ (Work.Spaces.w z) ^ 2) :
    (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
        ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ + (α * (5 + α) * z) * Work.Spaces.pz u z θ)
          * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  -- ## the four joint-integrability facts
  obtain ⟨hIntL, hIntY⟩ := tRibp_integrablePair (α := α) (u := u) ω ha hab hsm hgrad hrad2 hu
    hωd hωsupp hωbdd
  obtain ⟨hIntA, hIntB⟩ := tRibp_integrableCoeff (α := α) (u := u) ω ha hab hsm hu hωd hωsupp
  -- ## the slicewise identity holds for a.e. `θ`
  have hθae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    have hset : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[MeasureTheory.volume] Work.Spaces.Iθ :=
      MeasureTheory.Ioo_ae_eq_Icc
    rw [← MeasureTheory.Measure.restrict_congr_set hset]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (∫ z in Set.Ioi (0 : ℝ), ω z * (Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
        = -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z *
              (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
                (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
              deriv (fun y : ℝ => y * ω y) z *
                (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    hθae.mono (fun θ hθ => tRibp_sliceIbpSeta (α := α) (u := u) ω ha hab hsm hωd hωsupp hθ)
  -- ## exchange the two integrations
  rw [tRibp_swapRadial hIntL, tRibp_swapRadial hIntY, tRibp_swapRadial hIntA,
    tRibp_swapRadial hIntB]
  -- ## apply the slicewise identity under the `θ`-integral
  rw [MeasureTheory.integral_congr_ae hae]
  -- ## split the linear combination
  have hF1 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntY.integral_prod_right
  have hF2 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntA.integral_prod_right
  have hF3 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z in Set.Ioi (0 : ℝ),
      deriv (fun y : ℝ => y * ω y) z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hIntB.integral_prod_right
  have hA1c : MeasureTheory.Integrable (fun θ : ℝ => -α ^ 2 *
      (∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF1.const_mul (-α ^ 2)
  have hA2c : MeasureTheory.Integrable (fun θ : ℝ => α ^ 2 / 2 *
      (∫ z in Set.Ioi (0 : ℝ), deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF2.const_mul (α ^ 2 / 2)
  have hA3c : MeasureTheory.Integrable (fun θ : ℝ => α * (5 + α) / 2 *
      (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z *
        (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hF3.const_mul (α * (5 + α) / 2)
  have e1 : (∫ θ in Work.Spaces.Iθ, -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
      = -α ^ 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (-α ^ 2) _
  have e2 : (∫ θ in Work.Spaces.Iθ, α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      = α ^ 2 / 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (α ^ 2 / 2) _
  have e3 : (∫ θ in Work.Spaces.Iθ, α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
        deriv (fun y : ℝ => y * ω y) z * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
      = α * (5 + α) / 2 * (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
        deriv (fun y : ℝ => y * ω y) z *
          (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) :=
    MeasureTheory.integral_const_mul (α * (5 + α) / 2) _
  have e4 : (∫ θ in Work.Spaces.Iθ, (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
          ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
      = (∫ θ in Work.Spaces.Iθ, -α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
          ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫ θ in Work.Spaces.Iθ, α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))) :=
    MeasureTheory.integral_add hA1c hA2c
  have e5 : (∫ θ in Work.Spaces.Iθ, ((-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
            ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)))
        - α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
      = (∫ θ in Work.Spaces.Iθ, (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ),
            ω z * (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
          + α ^ 2 / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))))
        - (∫ θ in Work.Spaces.Iθ, α * (5 + α) / 2 * (∫ z in Set.Ioi (0 : ℝ),
            deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))) :=
    MeasureTheory.integral_sub (hA1c.add hA2c) hA3c
  rw [e5, e4, e1, e2, e3]

end Work.FTS.EllipticEst.Dispatch
end
end
