/-
Copyright: work module for the Elgindi finite-time singularity project.

# Basic lemmas for the truncated `w²`-energy inequality in the a.e. class

This module collects the elementary ingredients of the proof of
`Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp` (the truncated `w²`-weighted energy
inequality of Elgindi, Annals **194** (2021), Step 1 of `prop:H2`, in the almost-everywhere class
`AeData`):

* `aesm_massProfile` — a.e. strong measurability of the angular mass profile `z ↦ ∫_θ u(z,θ)²`;
* `slice_sq_integrable` — the fibre-`θ` square integrability of `u`, `∂_zu`, `∂_z²u`, `G`;
* `ae_slice_ineq` — the *a.e.-in-`z`* angular self-form inequality
  `∫_θ (∂_θu)² ≤ ∫_θ (Lzero u)·u + 6∫_θ u²`, and the nonnegativity of the right-hand side;
* `truncW2_le`, `truncW1_le` — the two pointwise weight bounds for the truncation error,
  `(φw²z²)'' ≤ 2|φ'||(z²w²)'| + |φ''|z²w² + 6φw²` and `-(φw²z)' ≤ |φ'|(zw²) + 3φw²`;
* `ae_slice_amgm` — the a.e.-in-`z` angular AM–GM `∫_θ G·u ≤ ½∫_θ G² + ½∫_θ u²`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyTruncIneq2
import Submission.Work.FTS.EllipticEst.Honest.LzeroSelfFormHon
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.sliceFacts
import Submission.Work.FTS.EllipticEst.Prop.CutEnergyAux.lintegralConv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.CutEnergyAux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "sg" => Work.FTS.EllipticEst.sEta

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
  intro z hz
  simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Ici] at hz
  exact le_antisymm (le_of_not_gt hz.2) hz.1

/-- Almost every `θ ∈ Iθ` lies in the open interval. -/
theorem ae_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'

/-- `Iθ` and the open interval carry the same measure (the endpoints are null). -/
theorem restrict_Iθ_eq_Ioo :
    MeasureTheory.volume.restrict Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
      (b := Real.pi / 2))).symm

/-- A.e. strong measurability of the angular mass profile `z ↦ ∫_θ u(z,θ)²`. -/
theorem aesm_massProfile {u : ℝ → ℝ → ℝ}
    (hs : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun z => ∫ θ in Iθ, (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hs 0).continuousOn).pow 2
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- A.e. strong measurability of the profile `z ↦ ∫_θ f(z,θ)` for a function `f` continuous on
the open quadrant. -/
theorem aesm_profile_of_cont {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable (fun z => ∫ θ in Iθ, f z θ) (MeasureTheory.volume.restrict Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd _ hf).integral_prod_right'

/-- On `Iθ` the level-`0` integrand is `w(z)²·g(z,θ)²·σ(θ)`. -/
theorem hkIntegrand_zero_eq' (α : ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ = (Work.Spaces.w z) ^ 2 * (g z θ ^ 2 * sg θ) := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.sq_profile_eq g z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
  simp only [Work.FTS.EllipticEst.sEta]
  ring

/-- `bslOp α u = G` holds a.e. on the angular interval, for `z > 0`. -/
theorem ae_bslOp_eq_G (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    (fun θ => Work.Elliptic.bslOp α u z θ * u z θ) =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => G z θ * u z θ) := by
  rw [restrict_Iθ_eq_Ioo]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [h.eq z hz θ hθ.1 hθ.2]

/-- The `θ`-squares of `u`, `∂_zu`, `∂_z²u` and `G` are integrable on the angular interval, for
every `z > 0`. -/
theorem slice_sq_integrable (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2) Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 u z θ) ^ 2) Iθ
    ∧ MeasureTheory.IntegrableOn (fun θ => (G z θ) ^ 2) Iθ := by
  obtain ⟨-, -, -, -, -, hu2, hpz2, hpzI2, hG2, -, -⟩ :=
    sliceFacts α u G h z (Set.mem_Ioi.mpr hz)
  exact ⟨hu2, hpz2, hpzI2, hG2⟩

/-- The angular self-form: for a.e. `z > 0` the slice of `u` satisfies
`∫_θ (∂_θu)² ≤ ∫_θ (Lzero u)·u + 6∫_θ u²`, the right-hand side being nonnegative. -/
theorem ae_slice_ineq (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2
          ≤ (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2))
      ∧ 0 ≤ (∫ θ in Iθ, Work.Elliptic.Lzero u z θ * u z θ) + 6 * (∫ θ in Iθ, (u z θ) ^ 2) := by
  have hIoi : MeasureTheory.volume.restrict Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  rw [hIoi]
  filter_upwards [hC, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hCz hz
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := fun n => by
    have h1 : ContDiffOn ℝ n (Function.uncurry u)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.smooth n
    have h2 : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiff_prodMk_right (𝕜 := ℝ) z).contDiffOn
    have h3 := h1.comp h2 (fun θ hθ => ⟨hz, hθ⟩)
    show ContDiffOn ℝ n (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2))
    exact h3
  have hsig : MeasureTheory.IntegrableOn
      (fun θ => deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ ^ 2 * sg θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma h.memAng2 hz
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      using h0
  have hid := Work.FTS.EllipticEst.H2W.AeProof.AeSliceSelfForm u z hsm hCz
    (h.dirZero z) (h.dirPi z) hsig
  have hsec : 0 ≤ ∫ θ in Iθ, (u z θ / Real.cos θ) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hB : 0 ≤ ∫ θ in Iθ, (deriv (fun θ' => u z θ') θ) ^ 2 :=
    integral_nonneg fun θ => sq_nonneg _
  have hpth : (∫ θ in Iθ, (Work.Spaces.pth u z θ) ^ 2)
      = ∫ θ in Iθ, (deriv (fun θ' => u z θ') θ) ^ 2 := by
    simp only [Work.Spaces.pth]
  rw [hpth, hid]
  constructor <;> linarith

/-- The first-order product rule for the truncated radial weight `φ·w²·z`. -/
theorem truncW1_deriv (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) {z : ℝ} (hz : 0 < z) :
    deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x) z
      = deriv φ z * (z * (Work.Spaces.w z) ^ 2)
        + φ z * deriv (fun x : ℝ => x * (Work.Spaces.w x) ^ 2) z :=
  Work.FTS.EllipticEst.Honest.TruncCutDerivOne φ hφsm z hz

/-- The second-order product rule for the truncated radial weight `φ·w²·z²`. -/
theorem truncW2_deriv (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) {z : ℝ} (hz : 0 < z) :
    deriv (deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)) z
      = deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        + 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        + φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z :=
  Work.FTS.EllipticEst.Honest.TruncCutDerivTwo φ hφsm z hz

/-- The pointwise bound for the second-order truncation weight:
`(φw²z²)'' ≤ 2|φ'||(z²w²)'| + |φ''|z²w² + 6φw²` for `z > 0`. -/
theorem truncW2_le (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    {z : ℝ} (hz : 0 < z) :
    deriv (deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x ^ 2)) z
      ≤ 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z|
        + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        + 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
  obtain ⟨-, -, -, -, -, hW2le, -, -, -, -, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  have hW2 := hW2le z hz
  have hderiv := truncW2_deriv φ hφsm hz
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hw2z : 0 ≤ z ^ 2 * (Work.Spaces.w z) ^ 2 := mul_nonneg (sq_nonneg _) hw2
  have hb1 : deriv (deriv φ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hw2z
  have hb2 : 2 * deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
      ≤ 2 * |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
    have h0 : deriv φ z * deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z
        ≤ |deriv φ z| * |deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2) z| := by
      rw [← abs_mul]; exact le_abs_self _
    linarith [h0]
  have hb3 : φ z * deriv (deriv (fun x : ℝ => x ^ 2 * (Work.Spaces.w x) ^ 2)) z
      ≤ 6 * (φ z * (Work.Spaces.w z) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hW2 (hφ0 z)
    linarith [hh]
  rw [hderiv]
  linarith

/-- The pointwise bound for the first-order truncation weight:
`-(φw²z)' ≤ |φ'|(zw²) + 3φw²` for `z > 0`. -/
theorem truncW1_le (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hφ0 : ∀ z : ℝ, 0 ≤ φ z)
    {z : ℝ} (hz : 0 < z) :
    -(deriv (fun x : ℝ => φ x * (Work.Spaces.w x) ^ 2 * x) z)
      ≤ |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        + 3 * (φ z * (Work.Spaces.w z) ^ 2) := by
  obtain ⟨-, -, -, -, -, -, hW1le, -, -, -, -⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  have hW1 := hW1le z hz
  have hderiv := truncW1_deriv φ hφsm hz
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hz1 : 0 ≤ z * (Work.Spaces.w z) ^ 2 := mul_nonneg (le_of_lt hz) hw2
  have hA : 0 ≤ (deriv φ z + |deriv φ z|) * (z * (Work.Spaces.w z) ^ 2) :=
    mul_nonneg (by linarith [neg_le_abs (deriv φ z)]) hz1
  have hB : 0 ≤ φ z
      * (deriv (fun z => z * (Work.Spaces.w z) ^ 2) z + 3 * (Work.Spaces.w z) ^ 2) :=
    mul_nonneg (hφ0 z) (by linarith [hW1])
  rw [hderiv]
  nlinarith [hA, hB]

/-- The angular AM–GM: for `z > 0`,
`∫_θ G(z,θ)·u(z,θ) ≤ ½∫_θ G(z,θ)² + ½∫_θ u(z,θ)²`. -/
theorem ae_slice_amgm (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, G z θ * u z θ)
      ≤ (1 / 2) * (∫ θ in Iθ, (G z θ) ^ 2) + (1 / 2) * (∫ θ in Iθ, (u z θ) ^ 2) := by
  obtain ⟨hu2, -, -, hG2⟩ := slice_sq_integrable α u G h hz
  have hbsl := (sliceFacts α u G h z (Set.mem_Ioi.mpr hz)).1
  have hGu : MeasureTheory.IntegrableOn (fun θ => G z θ * u z θ) Iθ :=
    hbsl.congr (ae_bslOp_eq_G α u G h hz)
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => (1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) Iθ :=
    (hG2.add hu2).const_mul (1 / 2)
  have hle : (∫ θ in Iθ, G z θ * u z θ)
      ≤ ∫ θ in Iθ, (1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) :=
    integral_mono_ae hGu hmaj (Filter.Eventually.of_forall fun θ => by
      have hsq := sq_nonneg (G z θ - u z θ)
      nlinarith [hsq])
  rw [integral_const_mul, integral_add hG2 hu2] at hle
  linarith

end Work.FTS.EllipticEst.Prop.CutEnergyAux
