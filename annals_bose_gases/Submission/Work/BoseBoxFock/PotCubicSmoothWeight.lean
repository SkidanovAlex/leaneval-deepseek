import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.lowCut_invFT_scaled
import Submission.Work.BoseFixR.Rb5Lin.W1Facts
import Submission.Work.BoseRowsL.Row2.chat_conv
import Submission.Work.SmallBoxBridge.Kernel.kinKernelC_eq_fourierInv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicSmoothWeight` — the UV-smoothing of the `Ŵ₁` weight

## What this file is for

The cubic row `PotCubic` (`PotGroupDefs.lean`) carries the `k`-weight

    `W1 k = uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) * chat (W1fun v h ℓ) (kmomLab ℓ N k)`

(`KzEnvHon`), where `uvCut fu Λ k = fu.f (‖k‖/Λ)` is the UV cut-off of the honest model.  The
cut-off is *essential*: it is what makes the lattice `k`-sum finite (`uvCut = 0` for
`‖k‖ ≥ 2Λ`) and what keeps the labels `k` and `s - k` away from the wrap-around of the cube
`Lab N`.  But `chat (W1fun v h ℓ)` is the Fourier transform of an `L¹`-function only — `W1fun`
is `g₀/(χ⋆χ)(·/ℓ)` with `g₀ = v(1-ω)` and `v` only `L¹ ∩ L^∞`, so it has **no regularity**: no
Poisson summation and no absolutely convergent lattice tail is available for it directly.

The point of this file is the observation that the **truncated** weight is the cosine transform
of a *smooth, rapidly decreasing* function: with

    `uvKernel fu Λ := 𝓕⁻(ζ_Λ) = kinKernel (fun r => fu.f (r / Λ))`,
    `uvSmear fu Λ f := uvKernel fu Λ ⋆ f`,

one has

    `uvCut fu Λ k * chat (W1fun v h ℓ) k = chat (uvSmear fu Λ (W1fun v h ℓ)) k`      (`chat_uvSmear`)

and `uvSmear fu Λ (W1fun v h ℓ)` is `C^∞` with rapid decay, while its Fourier transform
`uvCut fu Λ · chat (W1fun v h ℓ)` is compactly supported.  Consequently *every* lattice sum with
this weight is absolutely convergent with superpolynomially small tails, and the
Poisson-sampling bricks `latSampling_one`/`latSampling_decay`/`latSampling_pair` apply verbatim.

The remaining discrepancy is `uvSmear fu Λ (W1fun v h ℓ) - W1fun v h ℓ` — the *smoothing* of the
kernel at momentum scale `Λ` — and it is small in `L¹` as `Λ → ∞`
(`Work.BoseBoxFock.uvSmear_L1_tendsto`): this is exactly the mechanism by which the target's
`∃ Nmin` absorbs the UV cut-off (`Nmin μ` is chosen so that `Λ = uvRad ℓ (Nmin μ)` is huge).

## Content of this file

* `uvKernel`, `uvSmear`: the smoothing kernel and the smoothed weight;
* `chat_uvKernel` — **the design lemma**: `chat (uvKernel fu Λ) = uvCut fu Λ`;
* `integrable_uvKernel`, `chat_uvSmear` — the end-to-end identity
  `chat (uvSmear fu Λ f) = uvCut fu Λ · chat f` for `f ∈ L¹`;
* `one_le_norm_latVec`, `W1fun_add_latVec_eq_zero` — the **no-aliasing** lemma: for the box
  regime `2R < ℓ`, the lattice translates `z + ℓ•d` (`d ≠ 0`) of a box point `z` are outside
  `supp W1fun ⊆ B(0,R)`, so the periodisation of `W1fun` has no images.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The smoothing kernel and the smoothed weight -/

/-- **The UV-smoothing kernel** `ψ_Λ := 𝓕⁻(ζ_Λ)` — the inverse (`p`-convention) Fourier transform
of the UV cut-off `ζ_Λ = uvCut fu Λ`.  By construction `chat ψ_Λ = ζ_Λ`
(`chat_uvKernel`), so that the operator `f ↦ ψ_Λ ⋆ f` is the multiplier `ζ_Λ(√-Δ)` — i.e. the
UV-truncation of `W₁(√-Δ)` — but realised as *convolution with a smooth rapidly decreasing
kernel*, which is the form in which the lattice sums and the Poisson/aliasing estimates can be
evaluated. -/
noncomputable def uvKernel (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) : E3 → ℝ :=
  Submission.BoseGases.kinKernel (fun r : ℝ => fu.f (r / Λ))

/-- The explicit form of `uvKernel`: `(2π)⁻³∫_p fu.f(‖p‖/Λ)cos⟪p,z⟫dp`. -/
lemma uvKernel_apply (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (z : E3) :
    uvKernel fu Λ z
      = ((2 * π) ^ 3)⁻¹ * ∫ p : E3, fu.f (‖p‖ / Λ) * Real.cos (inner ℝ p z) := rfl

/-- `uvKernel fu Λ` is even (the cosine transform of an even symbol). -/
lemma uvKernel_even (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (z : E3) :
    uvKernel fu Λ (-z) = uvKernel fu Λ z := by
  rw [uvKernel_apply, uvKernel_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [inner_neg_right, Real.cos_neg]

/-- **The smoothed weight** `ψ_Λ ⋆ f`: the position-space kernel whose cosine transform is
`uvCut fu Λ · chat f`. -/
noncomputable def uvSmear (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (f : E3 → ℝ) : E3 → ℝ :=
  fun x => ∫ y : E3, uvKernel fu Λ (x - y) * f y

/-! ## 2. The symbol `ζ_Λ = f(‖·‖/Λ)` as a Schwartz function -/

/-- The UV cut-off as a complex-valued function of the momentum: `ζ_Λ(ξ) = f(2π‖ξ‖/Λ)`, i.e.
Mathlib's Fourier convention for the symbol `p ↦ f(‖p‖/Λ)` (`kinKernelC_eq_fourierInv`: the
inverse Fourier transform of `ζ_Λ` at `ξ` is `kinKernelC (fun r => f(r/Λ)) ξ = uvKernel fu Λ ξ`). -/
noncomputable def uvSymbol (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) : E3 → ℂ :=
  fun ξ => ((fu.f (2 * π * ‖ξ‖ / Λ) : ℝ) : ℂ)

lemma uvSymbol_eq_comp (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) (ξ : E3) :
    uvSymbol fu Λ ξ = lowCutProf fu ((2 * π / Λ) • ξ) := by
  rw [uvSymbol, lowCutProf]
  congr 2
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π / Λ)]
  ring

lemma uvSymbol_contDiff (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    ContDiff ℝ (⊤ : ℕ∞) (uvSymbol fu Λ) := by
  have hcomp : uvSymbol fu Λ = lowCutProf fu ∘ (fun ξ : E3 => (2 * π / Λ) • ξ) :=
    funext (uvSymbol_eq_comp fu hΛ)
  rw [hcomp]
  exact (contDiff_lowCutProf fu).comp (contDiff_const_smul (𝕜 := ℝ) (2 * π / Λ))

lemma uvSymbol_hasCompactSupport (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    HasCompactSupport (uvSymbol fu Λ) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : E3) (Λ / π))
    (isCompact_closedBall 0 _) ?_
  intro ξ hξ
  rw [Function.mem_support] at hξ
  by_contra hmem
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hmem
  refine hξ ?_
  rw [uvSymbol, fu.zero _ ?_, Complex.ofReal_zero]
  have hπξ : Λ < π * ‖ξ‖ := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hmem
    linarith
  rw [le_div_iff₀ hΛ]
  nlinarith [hπξ]

theorem integrable_uvSymbol (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (uvSymbol fu Λ) :=
  (uvSymbol_contDiff fu hΛ).continuous.integrable_of_hasCompactSupport
    (uvSymbol_hasCompactSupport fu hΛ)

theorem integrable_fourier_uvSymbol (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (FourierTransform.fourier (uvSymbol fu Λ)) := by
  have h2 : Integrable (FourierTransform.fourier
      (((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap (uvSymbol_contDiff fu hΛ) :
        SchwartzMap E3 ℂ) : E3 → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable
      (FourierTransform.fourier ((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap
        (uvSymbol_contDiff fu hΛ)))
  have hcoe : (((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap (uvSymbol_contDiff fu hΛ) :
      SchwartzMap E3 ℂ) : E3 → ℂ) = uvSymbol fu Λ :=
    funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x
  rwa [hcoe] at h2

/-! ## 3. The design lemma: `chat ψ_Λ = ζ_Λ` -/

/-- `kinKernelC` at the scaled LowCut is the inverse Fourier transform of `uvSymbol`. -/
lemma kinKernelC_lowCut_eq_fourierInv (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) :
    (fun z : E3 => Submission.BoseGases.kinKernelC (fun r : ℝ => fu.f (r / Λ)) z)
      = FourierTransform.fourierInv (uvSymbol fu Λ) := by
  funext z
  rw [Work.SmallBoxBridge.Kernel.kinKernelC_eq_fourierInv]
  apply congrArg (fun g : E3 → ℂ => FourierTransform.fourierInv g z)
  funext ξ
  rw [uvSymbol]

/-- **THE DESIGN LEMMA.**  The UV cut-off is the cosine transform of the smoothing kernel:
`chat ψ_Λ = ζ_Λ`.  Equivalently `𝓕 ψ_Λ = ζ_Λ`, i.e. the truncated weight `Ŵ₁ζ_Λ` of the cubic row
is *exactly* the Fourier transform of the smooth rapidly decreasing kernel `ψ_Λ = uvKernel fu Λ`.

This is the fact that removes the "no regularity of `W1fun`" obstruction: from it, every lattice
sum with the weight `uvCut fu Λ · chat W1fun` becomes a Poisson sum of a Schwartz kernel. -/
theorem chat_uvKernel (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) (p : E3) :
    Work.BoseFixR.chat (uvKernel fu Λ) p = uvCut fu Λ p := by
  have hk : (fun z : E3 => ((uvKernel fu Λ z : ℝ) : ℂ))
      = FourierTransform.fourierInv (uvSymbol fu Λ) := by
    funext z
    calc ((uvKernel fu Λ z : ℝ) : ℂ)
        = Submission.BoseGases.kinKernelC (fun r : ℝ => fu.f (r / Λ)) z :=
          (Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal (fun r : ℝ => fu.f (r / Λ)) z).symm
      _ = FourierTransform.fourierInv (uvSymbol fu Λ) z :=
          congrFun (kinKernelC_lowCut_eq_fourierInv fu Λ) z
  have hinv := (uvSymbol_contDiff fu hΛ).continuous.fourier_fourierInv_eq
    (integrable_uvSymbol fu hΛ) (integrable_fourier_uvSymbol fu hΛ)
  rw [Work.BoseFixR.chat, hk, Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, hinv, uvSymbol, uvCut]
  rw [Complex.ofReal_re]
  apply congrArg fu.f
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)]
  field_simp

/-! ## 4. The smoothed weight -/

/-- The complexification of `uvKernel fu Λ` is the inverse Fourier transform of the symbol, hence
is a Schwartz function. -/
lemma uvKernel_cast_eq_fourierInv (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) :
    (fun z : E3 => ((uvKernel fu Λ z : ℝ) : ℂ))
      = FourierTransform.fourierInv (uvSymbol fu Λ) := by
  funext z
  calc ((uvKernel fu Λ z : ℝ) : ℂ)
      = Submission.BoseGases.kinKernelC (fun r : ℝ => fu.f (r / Λ)) z :=
        (Work.SmallBoxBridge.Kernel.kinKernelC_eq_ofReal (fun r : ℝ => fu.f (r / Λ)) z).symm
    _ = FourierTransform.fourierInv (uvSymbol fu Λ) z :=
        congrFun (kinKernelC_lowCut_eq_fourierInv fu Λ) z

/-- `uvKernel fu Λ` is integrable: it is the real part of (the complexification of) the inverse
Fourier transform of the compactly supported smooth symbol, i.e. of a Schwartz function. -/
theorem integrable_uvKernel (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) :
    Integrable (uvKernel fu Λ) := by
  have hcoe : (((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap (uvSymbol_contDiff fu hΛ) :
      SchwartzMap E3 ℂ) : E3 → ℂ) = uvSymbol fu Λ :=
    funext fun x => HasCompactSupport.toSchwartzMap_toFun _ _ x
  have h1 : Integrable
      ((FourierTransform.fourierInv ((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap
        (uvSymbol_contDiff fu hΛ)) : SchwartzMap E3 ℂ) : E3 → ℂ) :=
    SchwartzMap.integrable _
  have h2 : (fun z : E3 => ((uvKernel fu Λ z : ℝ) : ℂ))
      = ((FourierTransform.fourierInv ((uvSymbol_hasCompactSupport fu hΛ).toSchwartzMap
        (uvSymbol_contDiff fu hΛ)) : SchwartzMap E3 ℂ) : E3 → ℂ) := by
    rw [SchwartzMap.fourierInv_coe, hcoe, ← uvKernel_cast_eq_fourierInv]
  have h3 : Integrable (fun z : E3 => Complex.re (((uvKernel fu Λ z : ℝ) : ℂ))) :=
    Complex.reCLM.integrable_comp (h2 ▸ h1)
  simpa only [Complex.ofReal_re] using h3

/-- **The end-to-end design identity.**  The UV-truncated weight is the cosine transform of the
smoothed kernel: for every `f ∈ L¹`,

    `chat (uvSmear fu Λ f) p = uvCut fu Λ p * chat f p` ,

i.e. the operator `f ↦ ψ_Λ ⋆ f` is the multiplier by the UV cut-off `ζ_Λ = uvCut fu Λ`. -/
theorem chat_uvSmear (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) {f : E3 → ℝ}
    (hf : Integrable f) (p : E3) :
    Work.BoseFixR.chat (uvSmear fu Λ f) p = uvCut fu Λ p * Work.BoseFixR.chat f p := by
  have hKe := integrable_uvKernel fu hΛ
  have hfun : uvSmear fu Λ f = fun z : E3 => ∫ x : E3, f x * uvKernel fu Λ (z - x) := by
    funext z
    rw [uvSmear]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hfun, Work.BoseRowsL.Row2.chat_conv_chat_eq hf hKe (uvKernel_even fu Λ) p,
    chat_uvKernel fu hΛ p, mul_comm]

/-! ## 5. No aliasing: the lattice translates of the box miss `supp W1fun` -/

/-- A non-zero integer lattice vector has norm at least `1`. -/
lemma one_le_norm_latVec {d : Fin 3 → ℤ} (hd : d ≠ 0) : (1 : ℝ) ≤ ‖latVec d‖ := by
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext fun i => h i)
  have h1 : (1 : ℝ) ≤ |(((d i : ℤ)) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |d i| := Int.one_le_abs hi
    exact_mod_cast h2
  calc (1 : ℝ) ≤ |(((d i : ℤ)) : ℝ)| := h1
    _ = |latVec d i| := by rw [latVec_apply]
    _ ≤ ‖latVec d‖ := by
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (latVec d) i

/-- **The no-aliasing lemma.**  In the box regime `‖z‖ + R < ℓ` (which holds for the box points
`z ∈ Λ` and `2R < ℓ`), the lattice translates `z + ℓ•latVec d` (`d ≠ 0`) are at distance `> R`
from the origin, hence outside `supp (W1fun v h ℓ) ⊆ B(0,R)`.  This is what makes the
periodisation `Σ_d W1fun (· + ℓ•d)` equal to `W1fun` alone inside the box. -/
theorem W1fun_add_latVec_eq_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R ℓ : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {z : E3} {d : Fin 3 → ℤ}
    (hd : d ≠ 0) (hz : ‖z‖ + R < ℓ) :
    Work.BoseFixR.W1fun v h ℓ (z + ℓ • latVec d) = 0 := by
  have hℓpos : 0 < ℓ := by linarith [norm_nonneg z]
  have hsp : ‖ℓ • latVec d‖ = ℓ * ‖latVec d‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓpos.le]
  have h1 : R ≤ ‖z + ℓ • latVec d‖ := by
    have h2 : ‖ℓ • latVec d‖ - ‖z‖ ≤ ‖z + ℓ • latVec d‖ := by
      have h3 : ‖ℓ • latVec d‖ ≤ ‖z + ℓ • latVec d‖ + ‖z‖ := by
        have h5 := norm_sub_le (z + ℓ • latVec d) z
        rw [show z + ℓ • latVec d - z = ℓ • latVec d by abel] at h5
        exact h5
      linarith
    have h4 : ℓ ≤ ‖ℓ • latVec d‖ := by
      rw [hsp]
      nlinarith [one_le_norm_latVec hd, hℓpos]
    linarith
  have hg0 : Submission.BoseGases.g0 v h (z + ℓ • latVec d) = 0 :=
    Submission.BoseGases.g0_zero_of_norm_ge hv_supp h1 h
  simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hg0]

end Work.BoseBoxFock
