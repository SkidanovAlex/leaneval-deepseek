/-
# The `K_θ`-Cauchy–Schwarz bound on the angular integral of the `D_z`-jets

Target of this module: `Work.FTS_EllLimOK.ThetaJets.integral_Ktheta_dzIter_le`, the bound

  `∫_{s>0} (∫_θ |K_θ θ| · |D_z^j g s θ| / s) ≤ C · |g|_{ℋ⁶}`  for `j ≤ 6`,

valid for every `g` smooth on the open quadrant with `HkMem α 6 g`; the constant `C` is
universal (in particular `α`-free).

## Route

Write `Wlam s = s/(1+s)² = 1/(s·w s)` (the radial weight) and `Sw θ = sin(2θ)^{η/2}`.
On `Iθ` the angular factor is nonnegative (`|K_θ θ| = K θ = 3 sinθ cos²θ`), so the angular
integrand factorises as

  `|K_θ θ| · |D_z^j g s θ| / s = Wlam s · (|K_θ θ| · Sw θ · (|D_z^j g s θ| · w s / Sw θ))`,

and two Cauchy–Schwarz steps bound the resulting iterated integral:

* **in `θ`** (`abs_integral_K_abs_S_q_le`): the weighted datum `|D_z^j g s θ| · w s / Sw θ`
  has absolute value at most `sqrt (HkIntegrand α 6 g s θ)` (the `D_z^j`-summand of the
  integrand, `Work.Spaces.sq_le_HkIntegrand_z`), so by Cauchy–Schwarz against the fixed
  angular profile `|K_θ| · Sw ∈ L²(Iθ)` one gets
  `∫_θ |K_θ θ| |D_z^j g s θ| / s ≤ Wlam s · BK · sqrt (∫_θ HkIntegrand α 6 g s θ)` with
  `BK = sqrt (∫_θ (K θ · Sw θ)²)` (`integral_Ktheta_dzIter_div_s_le`);
* **in `s`** (`wlam_sqrt_le`): `Wlam ∈ L²((0,∞))` and `s ↦ ∫_θ HkIntegrand α 6 g s θ ∈ L¹`
  with `∫_{s>0} ∫_θ HkIntegrand = HkSq α 6 g`, so Cauchy–Schwarz gives
  `∫_{s>0} Wlam s · sqrt (∫_θ HkIntegrand α 6 g s θ) ≤ sqrt W2 · HkNorm α 6 g` with
  `W2 = ∫_{s>0} Wlam²`.

The remaining bookkeeping is `MeasureTheory.IntegrableOn` for the target function, obtained
from the pointwise bound together with AM–GM (`Wlam · sqrt H ≤ (Wlam² + H)/2`) and the a.e.
strong measurability of the parametric integral (`aesm_integral_abs_Ktheta_dzIter`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]` once the
two sibling modules `wlam_sqrt_le` and `aesm_integral_abs_Ktheta_dzIter` are proved.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Elliptic.L12densFacts
import Submission.Work.FTS_EllLimOK.ThetaJets.wlam_sqrt_le
import Submission.Work.FTS_EllLimOK.ThetaJets.aesm_integral_abs_Ktheta_dzIter

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ThetaJets

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. The angular factor is nonnegative on `Iθ` -/

/-- On the angular interval, `|K_θ θ| = K_θ θ = 3 sinθ cos²θ`, in particular
`|K_θ θ| = Work.Spaces.K θ`. -/
theorem abs_Ktheta_eq_K {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Elliptic.Ktheta θ| = Work.Spaces.K θ := by
  have h : Work.Elliptic.Ktheta θ = Work.Spaces.K θ := rfl
  rw [h, abs_of_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ)]

/-! ## 2. The factorisation of the angular integrand -/

/-- For `s > 0` and `θ ∈ Iθ` the angular integrand of the target factorises as the radial
weight `Wlam s = 1/(s · w s)` times the weighted angular pairing
`|K_θ θ| · Sw θ · (|u s θ| · w s / Sw θ)`:
`|K_θ θ| · |u s θ| / s = Wlam s · (|K_θ θ| · Sw θ · Gaz' s θ)`. -/
theorem Ktheta_abs_div_s_factor (u : ℝ → ℝ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Elliptic.Ktheta θ| * |u s θ| / s
        = Work.FTS.GalBasis.cc.Wlam s
          * (|Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ
              * (|u s θ| * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ))) := by
  intro θ hθ
  rw [abs_Ktheta_eq_K hθ, Work.FTS.GalBasis.cc.Wlam, Work.Spaces.w]
  by_cases hS : Work.FTS.GalBasis.cc.Sw θ = 0
  · have hK : Work.Spaces.K θ = 0 := Work.FTS.GalBasis.cc.sw_eq_zero_imp_K_eq_zero hθ hS
    rw [hS, hK]
    simp
  · have hs0 : s ≠ 0 := ne_of_gt hs
    have h1s : (1 : ℝ) + s ≠ 0 := by linarith
    field_simp

/-! ## 3. Angular Cauchy–Schwarz -/

/-- **Angular Cauchy–Schwarz.**  If the `θ`-slice of the `ℋ^k`-integrand is integrable and
the weighted datum `q` is pointwise dominated by its square root on `Iθ`, then the pairing of
`q` against `|K_θ| · Sw` is bounded by `BK · sqrt (∫_θ HkIntegrand α k g s θ)`. -/
theorem abs_integral_K_abs_S_q_le {α : ℝ} (k : ℕ) {g : ℝ → ℝ → ℝ} {q : ℝ → ℝ} {s : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g s θ)
      Work.Spaces.Iθ)
    (hq : ∀ θ ∈ Work.Spaces.Iθ,
      |q θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k g s θ)) :
    |∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ|
      ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k g s θ) := by
  set u : ℝ → ℝ := fun θ => |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ with hu
  set v : ℝ → ℝ := fun θ => q θ with hv
  set w : ℝ → ℝ := fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k g s θ) with hw
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hHk_nn : ∀ θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k g s θ :=
    fun θ => Work.Spaces.HkIntegrand_nonneg α k g s θ
  have hw_nn : ∀ θ : ℝ, 0 ≤ w θ := by
    intro θ; rw [hw]; exact Real.sqrt_nonneg _
  have hvw : ∀ θ ∈ Work.Spaces.Iθ, |v θ| ≤ w θ := by
    intro θ hθ; rw [hv, hw]; exact hq θ hθ
  have hcont_u : Continuous u := by
    rw [hu]
    have hKc : Continuous fun θ : ℝ => |Work.Elliptic.Ktheta θ| := by
      change Continuous fun θ : ℝ => |3 * Real.sin θ * Real.cos θ ^ 2|
      fun_prop
    exact hKc.mul Work.FTS.GalBasis.cc.continuous_sw
  have hw_aesm : AEStronglyMeasurable w (volume.restrict Work.Spaces.Iθ) := by
    rw [hw]
    exact (hint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  have hu2_int : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ :=
    (hcont_u.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hw2_int : IntegrableOn (fun θ => (w θ) ^ 2) Work.Spaces.Iθ := by
    refine hint.congr_fun (fun θ _ => ?_) hIθ
    rw [hw]; exact (Real.sq_sqrt (hHk_nn θ)).symm
  have huw_int : IntegrableOn (fun θ => |u θ| * w θ) Work.Spaces.Iθ := by
    have hmaj : IntegrableOn (fun θ => ((u θ) ^ 2 + (w θ) ^ 2) / 2) Work.Spaces.Iθ :=
      (hu2_int.add hw2_int).div_const 2
    refine hmaj.mono' ((hcont_u.abs.aestronglyMeasurable).mul hw_aesm) ?_
    filter_upwards with θ
    have h1 : 0 ≤ |u θ| := abs_nonneg _
    have h2 : 0 ≤ w θ := hw_nn θ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1]
    have key : |u θ| * w θ ≤ (|u θ| ^ 2 + (w θ) ^ 2) / 2 := by
      nlinarith [sq_nonneg (|u θ| - w θ), sq_nonneg (|u θ| + w θ)]
    rw [sq_abs (u θ)] at key
    exact key
  have hMemLp_u : MemLp (fun θ => |u θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => |u θ|) hcont_u.abs.aestronglyMeasurable).mpr
      (hu2_int.congr (Filter.Eventually.of_forall fun θ => (sq_abs (u θ)).symm))
  have hMemLp_w : MemLp w 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq (μ := volume.restrict Work.Spaces.Iθ) hw_aesm).mpr hw2_int
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt (u := fun θ => |u θ|)
    (v := w) hMemLp_u hMemLp_w
  have hsqrt_u : Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2) = Work.FTS.GalBasis.cc.BK := by
    rw [Work.FTS.GalBasis.cc.BK]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    simp only [hu]
    rw [sq_abs, abs_Ktheta_eq_K hθ]
  have hsqrt_w : Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2)
      = Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    rw [hw]; exact Real.sq_sqrt (hHk_nn θ)
  have h1 : |∫ θ in Work.Spaces.Iθ, u θ * v θ|
      ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun θ => u θ * v θ))
  have h2 : ∫ θ in Work.Spaces.Iθ, |u θ * v θ| ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => abs_nonneg _) huw_int ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => by
      show |u θ * v θ| ≤ |u θ| * w θ
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hvw θ hθ) (abs_nonneg _)
  have h3 : ∫ θ in Work.Spaces.Iθ, |u θ| * w θ
      = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := by
    rw [abs_of_nonneg]
    exact MeasureTheory.integral_nonneg fun θ => mul_nonneg (abs_nonneg _) (hw_nn θ)
  calc |∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ|
      = |∫ θ in Work.Spaces.Iθ, u θ * v θ| := by simp only [hu, hv]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ * v θ| := h1
    _ ≤ ∫ θ in Work.Spaces.Iθ, |u θ| * w θ := h2
    _ = |∫ θ in Work.Spaces.Iθ, |u θ| * w θ| := h3
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, |u θ| ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (w θ) ^ 2) := hcs
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k g s θ) := by
        rw [hsqrt_u, hsqrt_w]

/-! ## 4. The pointwise (in `s`) bound on the angular integral -/

/-- **The pointwise bound.**  For `s > 0`, `g ∈ ℋ^k_α` and `j ≤ k`,
`∫_θ |K_θ θ| |D_z^j g s θ| / s ≤ Wlam s · BK · sqrt (∫_θ HkIntegrand α k g s θ)`. -/
theorem integral_Ktheta_dzIter_div_s_le {α : ℝ} (k : ℕ) {g : ℝ → ℝ → ℝ} {j : ℕ}
    (hmem : Work.Spaces.HkMem α k g) (hj : j ≤ k) {s : ℝ} (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ, |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s)
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * Real.sqrt
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g s θ)) := by
  set q : ℝ → ℝ := fun θ => |Work.Spaces.DzIter j g s θ|
    * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ) with hq
  have hslice : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g s θ) Work.Spaces.Iθ :=
    hmem.1 s hs.le
  have hqbd : ∀ θ ∈ Work.Spaces.Iθ, |q θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α k g s θ) := by
    intro θ _
    have hsq : (Work.Spaces.DzIter j g s θ
        * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ)) ^ 2
        ≤ Work.Spaces.HkIntegrand α k g s θ := by
      have h := Work.Spaces.sq_le_HkIntegrand_z α k g s θ j hj
      simpa only [Work.FTS.GalBasis.cc.Sw_apply] using h
    have habs : |Work.Spaces.DzIter j g s θ
        * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ)|
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α k g s θ) := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq_eq_abs] at h
    rw [hq]
    calc |(|Work.Spaces.DzIter j g s θ| * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ))|
        = |Work.Spaces.DzIter j g s θ| * |Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ| := by
          rw [abs_mul, abs_abs]
      _ = |Work.Spaces.DzIter j g s θ * (Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ)| :=
          (abs_mul _ _).symm
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α k g s θ) := habs
  have hkey : (∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s)
      = Work.FTS.GalBasis.cc.Wlam s * ∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => Ktheta_abs_div_s_factor (fun a b => Work.Spaces.DzIter j g a b) hs θ hθ)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ := by
    refine MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_)
    have h1 : 0 ≤ |Work.Elliptic.Ktheta θ| := abs_nonneg _
    have h2 : 0 ≤ Work.FTS.GalBasis.cc.Sw θ :=
      Work.FTS.GalBasis.cc.Sw_nonneg_of_mem_Iθ hθ
    have h3 : 0 ≤ q θ := by
      rw [hq]
      exact mul_nonneg (abs_nonneg _)
        (div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) h2)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  rw [hkey]
  refine mul_le_mul_of_nonneg_left ?_ (Work.FTS.GalBasis.cc.Wlam_nonneg hs.le)
  calc ∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ
      = |∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * Work.FTS.GalBasis.cc.Sw θ * q θ| :=
        (abs_of_nonneg hnn).symm
    _ ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k g s θ) := abs_integral_K_abs_S_q_le k hslice hqbd

/-! ## 5. The target -/

theorem integral_Ktheta_dzIter_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (j : ℕ),
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → j ≤ 6 →
      MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0:ℝ), (∫ θ in Work.Spaces.Iθ,
        |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s))
        ≤ C * Work.Spaces.HkNorm α 6 g := by
  refine ⟨Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1,
    by nlinarith [Work.FTS.GalBasis.cc.BK_nonneg,
      Real.sqrt_nonneg Work.FTS.GalBasis.cc.W2], ?_⟩
  intro α g j hsm hmem hj
  set Af : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ,
    |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s with hAf
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.HkIntegrand α 6 g s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  have hbound : ∀ s ∈ Set.Ioi (0 : ℝ), Af s
      ≤ Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by
    intro s hs
    have h := integral_Ktheta_dzIter_div_s_le (α := α) 6 (g := g) (j := j) hmem hj hs
    rw [hAf, hA, hH]
    calc (∫ θ in Work.Spaces.Iθ,
          |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s)
        ≤ Work.FTS.GalBasis.cc.Wlam s
            * (Work.FTS.GalBasis.cc.BK * Real.sqrt (H s)) := h
      _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * Real.sqrt (H s)) := by ring
  have hAf_nn : ∀ s ∈ Set.Ioi (0 : ℝ), 0 ≤ Af s := by
    intro s hs
    rw [hAf]
    refine MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => ?_)
    show 0 ≤ |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s
    have hrs : |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| / s
        = |Work.Elliptic.Ktheta θ| * |Work.Spaces.DzIter j g s θ| * (1 / s) := by ring
    rw [hrs]
    have hs0 : 0 < s := hs
    positivity
  have hAf_aesm : AEStronglyMeasurable Af (volume.restrict (Set.Ioi 0)) := by
    rw [hAf]
    exact aesm_integral_abs_Ktheta_dzIter j hsm
  obtain ⟨hWA_int, -, hWA_le⟩ := wlam_sqrt_le α 6 hmem
  have hWA_int' : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s * A s)
      (Set.Ioi 0) := by simpa only [hA, hH] using hWA_int
  have hWA_le' : (∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * A s)
      ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 6 g) := by
    simpa only [hA, hH] using hWA_le
  have hmaj_int : IntegrableOn
      (fun s => Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s))
      (Set.Ioi 0) := hWA_int'.const_mul _
  have hint : IntegrableOn Af (Set.Ioi 0) := by
    refine hmaj_int.mono' hAf_aesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hAf_nn s hs)]
    exact hbound s hs
  refine ⟨by simpa only [hAf] using hint, ?_⟩
  have hmain : (∫ s in Set.Ioi (0 : ℝ), Af s)
      ≤ ∫ s in Set.Ioi (0 : ℝ),
          Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hAf_nn) hmaj_int
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  have hsplit : (∫ s in Set.Ioi (0 : ℝ),
        Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s))
      = Work.FTS.GalBasis.cc.BK
        * ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * A s :=
    MeasureTheory.integral_const_mul _ _
  have hBK_nn : 0 ≤ Work.FTS.GalBasis.cc.BK := Work.FTS.GalBasis.cc.BK_nonneg
  have hW2_nn : 0 ≤ Real.sqrt Work.FTS.GalBasis.cc.W2 := Real.sqrt_nonneg _
  calc (∫ s in Set.Ioi (0 : ℝ), Af s)
      ≤ Work.FTS.GalBasis.cc.BK
          * ∫ s in Set.Ioi (0 : ℝ), Work.FTS.GalBasis.cc.Wlam s * A s := by
        rw [hsplit] at hmain; exact hmain
    _ ≤ Work.FTS.GalBasis.cc.BK
          * (Real.sqrt Work.FTS.GalBasis.cc.W2 * Real.sqrt (Work.Spaces.HkSq α 6 g)) :=
        mul_le_mul_of_nonneg_left hWA_le' hBK_nn
    _ = Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2
          * Work.Spaces.HkNorm α 6 g := by
        rw [Work.Spaces.HkNorm]
        ring
    _ ≤ (Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 + 1)
          * Work.Spaces.HkNorm α 6 g := by
        have hx : (0 : ℝ) ≤ Work.FTS.GalBasis.cc.BK * Real.sqrt Work.FTS.GalBasis.cc.W2 :=
          mul_nonneg hBK_nn hW2_nn
        have hy : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
        nlinarith [mul_nonneg hx hy]

end Work.FTS_EllLimOK.ThetaJets
