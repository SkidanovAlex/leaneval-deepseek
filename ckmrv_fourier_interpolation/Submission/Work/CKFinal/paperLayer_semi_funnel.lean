import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.psumData
import Submission.Work.Asymptotics.FunnelAsm.decomp
import Submission.Work.Asymptotics.HalfFunnel.GcuspRow11Small
import Submission.Work.Asymptotics.HalfFunnel.funnelKernelWindow
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.HalfFunnel.funnelLayer
import Submission.Work.Asymptotics.HalfFunnel.funnelFlat

/-!
# The `r`-seminorm bound for the CKMRV layer on the funnel

`Work.Asymptotics.HalfFunnel.funnelLayer` bounds the `r`-seminorms of the *punctured* layer
`layer = if r = 0 then 0 else paperLayer` on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`, in the split form
`α (Im τ)^{-β} + γ ‖τ‖^δ`.  The requested lemma concerns the paper's layer itself, which differs
from `layer` only at the single point `r = 0`:

* the split form `α (Im τ)^{-β} + γ ‖τ‖^δ` is dominated by `(α + γ) (scale τ)^{max β δ}`, since
  both `(Im τ)^{-1}` and `‖τ‖` are bounded by `scale τ = 1 + (Im τ)^{-1} + ‖τ‖ ≥ 1`;
* at `r = 0` the weight `|r|^k` vanishes for `k ≥ 1`, and for `k = 0` the value of
  `∂_r^l paperLayer(τ, ·)` at `0` is the limit of its values at `r ≠ 0` (paperLayer is analytic in
  `r` on the funnel — it is a sum of `layerLow`, `layerTrunc` and the elementary `highPart`), and
  those are bounded by the same expression because `layer` and `paperLayer` agree off `0`.
-/

namespace Work.CKFinal

open UpperHalfPlane Filter Topology
open scoped Topology ContDiff

/-- The split bound `α (Im τ)^{-β} + γ ‖τ‖^δ` (with `α, β, γ, δ ≥ 0`) is dominated by
`(α + γ) (scale τ)^{max β δ}`. -/
lemma semi_funnel_scale_domination {α β γ δ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hδ : 0 ≤ δ) (τ : UpperHalfPlane) :
    α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ
      ≤ (α + γ) * (Work.Kernels.scale τ) ^ max β δ := by
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hS0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have him0 : (0 : ℝ) < τ.im := τ.im_pos
  have him : (τ.im)⁻¹ ≤ Work.Kernels.scale τ := by
    rw [Work.Kernels.scale]; linarith [norm_nonneg ((τ : ℂ))]
  have hnorm : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := by
    rw [Work.Kernels.scale]; linarith [inv_nonneg.mpr him0.le]
  have hpow : (τ.im) ^ (-β) = ((τ.im)⁻¹) ^ β := by
    rw [Real.inv_rpow him0.le β, Real.rpow_neg him0.le β]
  have h1 : (τ.im) ^ (-β) ≤ (Work.Kernels.scale τ) ^ max β δ := by
    rw [hpow]
    exact le_trans (Real.rpow_le_rpow (inv_nonneg.mpr him0.le) him hβ)
      (Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left β δ))
  have h2 : ‖(τ : ℂ)‖ ^ δ ≤ (Work.Kernels.scale τ) ^ max β δ :=
    le_trans (Real.rpow_le_rpow (norm_nonneg _) hnorm hδ)
      (Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right β δ))
  have hm1 : α * (τ.im) ^ (-β) ≤ α * (Work.Kernels.scale τ) ^ max β δ :=
    mul_le_mul_of_nonneg_left h1 hα
  have hm2 : γ * ‖(τ : ℂ)‖ ^ δ ≤ γ * (Work.Kernels.scale τ) ^ max β δ :=
    mul_le_mul_of_nonneg_left h2 hγ
  calc α * (τ.im) ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ
      ≤ α * (Work.Kernels.scale τ) ^ max β δ + γ * (Work.Kernels.scale τ) ^ max β δ :=
        add_le_add hm1 hm2
    _ = (α + γ) * (Work.Kernels.scale τ) ^ max β δ := by ring

/-- The paper's layer `paperLayer (Gcusp ℓ d) ℓ d τ ·` is analytic in `r` at every funnel point. -/
lemma semi_funnel_contDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
      ContDiff ℝ ω (fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) := by
  intro τ hτ hτ2
  obtain ⟨-, -, -, hLowCD, -⟩ := Work.Asymptotics.HalfFunnel.funnelLayerLow_input ℓ d hd
    (Work.Asymptotics.HalfFunnel.funnelFlat ℓ d hd) 0 0
  obtain ⟨-, -, -, hTruncCD, -⟩ := Work.Asymptotics.HalfFunnel.funnelLayerTrunc ℓ d hd
    (Work.Asymptotics.HalfFunnel.funnelKernelWindow ℓ d hd)
    (Work.Asymptotics.HalfFunnel.GcuspRow11Small ℓ d hd) 0 0
  have h3 : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) :=
    Work.Asymptotics.contDiff_omega_highPart (Work.Asymptotics.Gcusp ℓ d) τ
  have hfun : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)
      = fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
          + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s
          + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s := by
    funext s; rw [Work.Asymptotics.paperLayer]
  rw [hfun]
  exact ((hLowCD τ hτ hτ2).add (hTruncCD τ hτ hτ2)).add h3

theorem paperLayer_semi_funnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hb⟩ :=
    Work.Asymptotics.HalfFunnel.funnelLayer ℓ d hd
      (Work.Asymptotics.HalfFunnel.funnelFlat ℓ d hd) k l
  refine ⟨α + γ, max β δ, by linarith, le_trans hβ (le_max_left β δ), ?_⟩
  intro τ hτ hτ2 r
  have hCnn : (0 : ℝ) ≤ α + γ := by linarith
  have hS0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hpoint : ∀ s : ℝ, s ≠ 0 →
      (fun t : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ t)
        =ᶠ[𝓝 s] (fun t : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ t) := by
    intro s hs
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    rw [Work.Asymptotics.layer, if_neg ht]
  have hbound : ∀ s : ℝ, s ≠ 0 →
      |s| ^ k * ‖iteratedDeriv l (fun t : ℝ =>
        Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ t) s‖
        ≤ (α + γ) * (Work.Kernels.scale τ) ^ max β δ :=
    fun s hs => le_trans (hb τ s hτ hτ2)
      (semi_funnel_scale_domination hα hβ hγ hδ τ)
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [abs_zero, pow_zero, one_mul]
      have hcont : ContinuousAt (iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s)) 0 :=
        ((semi_funnel_contDiff ℓ d hd τ hτ hτ2).continuous_iteratedDeriv l le_top).continuousAt
      have hlim : Tendsto (fun s : ℝ => ‖iteratedDeriv l (fun t : ℝ =>
          Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ t) s‖)
          (𝓝[{0}ᶜ] (0 : ℝ))
          (𝓝 ‖iteratedDeriv l (fun t : ℝ =>
            Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ t) 0‖) :=
        hcont.norm.tendsto.mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : s ≠ 0 := by simpa using hs
      rw [Work.Asymptotics.iteratedDeriv_congr_of_eventuallyEq (hpoint s hs0) l]
      simpa using hbound s hs0
    · rw [abs_zero, zero_pow hk.ne', zero_mul]
      exact mul_nonneg hCnn (Real.rpow_nonneg hS0.le _)
  · rw [Work.Asymptotics.iteratedDeriv_congr_of_eventuallyEq (hpoint r hr) l]
    exact hbound r hr

end Work.CKFinal
