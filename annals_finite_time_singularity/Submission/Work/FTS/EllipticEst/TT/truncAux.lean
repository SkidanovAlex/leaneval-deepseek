/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for `Work.FTS.EllipticEst.TT.truncIntegrable`

This module collects the measure-theoretic and pointwise infrastructure for the marginal
integrability statement `Work.FTS.EllipticEst.TT.truncIntegrable`: for an `AeData` datum and a
compactly supported `C²` cutoff `ψ` (supported in `[a,b] ⊂ (0,∞)`), the four `z`-functions
`ψ·|lzMass|`, `ψ·mass`, `ψ·z²·dzMass` and `ψ·|srcMass|` are integrable on `(0,∞)`.

Contents:

* `psi_abs_le_wsq` — the weight bound `|ψ z| ≤ C · w(z)²` for `z > 0`, which is what allows a
  functional `ψ` to play the role of the cutoff weight `W·w²` of the sibling module
  `Dispatch.aeJointIntegrableF` (there `w ≥ 1` on `(0,∞)`, and `ψ` is bounded and vanishes off
  the compact set `[a,b]`);
* `aesm_prod_sEta_snd` — continuity of `θ ↦ σ θ = sin(2θ)^{-η}` on the open quadrant;
* `continuousOn_fst_comp` — continuity on the open quadrant of a function of `z` alone which is
  continuous on `(0,∞)`;
* `smoothOpen_Lzero` — `L₀Ψ` is `C^∞` on the open quadrant when `Ψ` is;
* `integrable_sigma_pair_nu` — the AM–GM domination
  `|A(z)| σ |f g| ≤ C (HkIntegrand α 0 f + HkIntegrand α 0 g)/2` which makes the
  `σ`-weighted pairing `A(z)·σ·f·g` jointly integrable against `nuFts` from the joint
  integrability of the two level-`0` integrands;
* `aesm_mul_absIntegral` — a.e. strong measurability of `z ↦ A z · |∫_θ Λ(z,θ)|` from
  continuity of `Λ` on the open quadrant (Fubini measurability of the partial integral).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.TT.aeDzDefs
import Submission.Work.FTS.EllipticEst.Dispatch.aeJointIntegrableF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The weight bound `|ψ| ≤ C w²` on `(0,∞)` -/

/-- A `C²` function on `(0,∞)` supported in `[a,b]` with `0 < a < b` is bounded by a constant
multiple of `w(z)²` for `z > 0`: it is bounded on the compact `[a,b]`, and `w ≥ 1` on `(0,∞)`. -/
theorem psi_abs_le_wsq (ψ : ℝ → ℝ) (hψd : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hψs : ∀ z, z ∉ Set.Icc a b → ψ z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → |ψ z| ≤ C * (Work.Spaces.w z) ^ 2 := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hψd.continuousOn.mono hsub)
  refine ⟨max M 0, le_max_right _ _, fun z hz0 => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · have h1 : |ψ z| ≤ M := by
      have h := hM z hz
      rwa [Real.norm_eq_abs] at h
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
      nlinarith [hz0]
    have h2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := one_le_pow₀ hw1
    calc |ψ z| ≤ max M 0 := le_trans h1 (le_max_left _ _)
      _ = max M 0 * 1 := (mul_one _).symm
      _ ≤ max M 0 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  · rw [hψs z hz, abs_zero]
    positivity

/-! ## Continuity on the open quadrant -/

/-- `σ θ = sin(2θ)^{-η}` is continuous on the open quadrant, as a function of `θ` alone. -/
theorem aesm_prod_sEta_snd :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsm : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos hθ)))
  exact h1.comp continuous_snd.continuousOn (fun p hp => hp.2)

/-- Continuity on the open quadrant of a function of `z` alone which is continuous on `(0,∞)`. -/
theorem continuousOn_fst_comp {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1) Work.FTS.EllipticEst.Q0 :=
  hf.comp continuous_fst.continuousOn
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)

/-- `L₀Ψ = -∂_θ²Ψ + ∂_θ(tan θ·Ψ) - 6Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_Lzero {Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.Lzero Ψ) := by
  have htΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl h
  have hC : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => -(Work.Spaces.pthIter 2 Ψ z θ)
      + Work.Spaces.pth (fun z θ : ℝ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_add_bsl
        (Work.FTS.EllipticEst.Cert.smoothOpen_neg_bsl
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl h 2))
        (Work.FTS.EllipticEst.SmoothOpen.pth htΨ))
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl 6 h)
  exact hC

/-! ## AM–GM domination by the level-`0` integrands -/

/-- **The `σ`-weighted pairing `A(z)·σ(θ)·f·g` is jointly integrable** as soon as
`|A z| ≤ C·w(z)²` for `z > 0` and the level-`0` `ℋ`-integrands of `f` and `g` are jointly
integrable: the pointwise estimate
`|A| σ |f g| ≤ C w² σ (f²+g²)/2 = C (HkIntegrand f + HkIntegrand g)/2`
holds on the open quadrant, which is a.e. for `nuFts`. -/
theorem integrable_sigma_pair_nu {α C : ℝ} {f g : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hC : 0 ≤ C) (hA : ∀ z, 0 < z → |A z| ≤ C * (Work.Spaces.w z) ^ 2)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => A p.1 * (Work.FTS.EllipticEst.sEta p.2 * (f p.1 p.2 * g p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.nuFts)
    (hf : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 f p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts)
    (hg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 g p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => A p.1 * (Work.FTS.EllipticEst.sEta p.2 * (f p.1 p.2 * g p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
  refine ((hf.add hg).const_mul C).mono' haesm ?_
  filter_upwards [Work.FTS.EllipticEst.Dispatch.ae_mem_Ioi_nu,
    Work.FTS.EllipticEst.Dispatch.ae_mem_Ioo_nu] with p hz hθ
  obtain ⟨z, θ⟩ := p
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : 0 ≤ Work.FTS.EllipticEst.sEta θ := AeDz.sig_nonneg hθI
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hHf : Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    AeDz.hkIntegrand_eq α f hθI
  have hHg : Work.Spaces.HkIntegrand α 0 g z θ
      = (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    AeDz.hkIntegrand_eq α g hθI
  have hfg : |f z θ| * |g z θ| ≤ ((f z θ) ^ 2 + (g z θ) ^ 2) / 2 := by
    have hh : 0 ≤ (|f z θ| - |g z θ|) ^ 2 := sq_nonneg _
    rw [sub_sq, sq_abs, sq_abs] at hh
    linarith
  have hnorm : ‖A z * (Work.FTS.EllipticEst.sEta θ * (f z θ * g z θ))‖
      = |A z| * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) := by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσnn]
  have h1 : 0 ≤ Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|) :=
    mul_nonneg hσnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have e1 : 0 ≤ (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_nonneg hw2 (mul_nonneg (sq_nonneg _) hσnn)
  have e2 : 0 ≤ (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    mul_nonneg hw2 (mul_nonneg (sq_nonneg _) hσnn)
  calc ‖A z * (Work.FTS.EllipticEst.sEta θ * (f z θ * g z θ))‖
      = |A z| * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) := hnorm
    _ ≤ (C * (Work.Spaces.w z) ^ 2)
          * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|)) :=
        mul_le_mul_of_nonneg_right (hA z hz) h1
    _ = C * ((Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.sEta θ * (|f z θ| * |g z θ|))) := by ring
    _ ≤ C * ((Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.sEta θ * (((f z θ) ^ 2 + (g z θ) ^ 2) / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine mul_le_mul_of_nonneg_left ?_ hw2
        exact mul_le_mul_of_nonneg_left hfg hσnn
    _ ≤ C * (Work.Spaces.HkIntegrand α 0 f z θ
          + Work.Spaces.HkIntegrand α 0 g z θ) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [hHf, hHg]
        nlinarith [e1, e2]

/-! ## A.e. strong measurability of `A z · |∫_θ Λ(z,θ)|` -/

/-- If `Λ` is continuous on the open quadrant and `A` is a.e. strongly measurable, then
`z ↦ A z · |∫_θ Λ (z,θ)|` is a.e. strongly measurable on `(0,∞)` (Fubini measurability of the
partial integral, then composition with `|·|` and with multiplication). -/
theorem aesm_mul_absIntegral {A : ℝ → ℝ} {Λ : ℝ × ℝ → ℝ}
    (hA : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΛ : ContinuousOn Λ Work.FTS.EllipticEst.Q0) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => A z * |∫ θ, Λ (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ, Λ (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Work.FTS.EllipticEst.Dispatch.aesm_prod_of_continuousOn_Q0 hΛ).integral_prod_right'
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun z => |∫ θ, Λ (z, θ) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)|)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    have h := h1.norm
    simpa only [Real.norm_eq_abs] using h
  exact continuous_mul.comp_aestronglyMeasurable₂ hA h2

end Work.FTS.EllipticEst.TT
