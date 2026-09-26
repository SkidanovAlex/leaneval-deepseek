import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.ae_tail_bound_of_TailBound
import Submission.Work.Asymptotics.layerLow_seminorm
import Submission.Work.Asymptotics.layerTrunc_seminorm_of_tailBound
import Submission.Work.Asymptotics.highPart_seminorm_scaled

noncomputable section

open MeasureTheory UpperHalfPlane Filter
open scoped Topology ContDiff

namespace Work.Asymptotics

/-! ## Smoothness of the three pieces -/

lemma contDiff_omega_layerLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N)
    {τ : UpperHalfPlane} (hτ : τ ∈ Work.Asymptotics.DomainD) :
    ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) := by
  obtain ⟨c, N', hc, hflat'⟩ := hflat 0 (le_refl 0)
  have hscale : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hlow : ContDiff ℝ ω (fun r : ℝ => ∫ t in (0:ℝ)..1,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    refine contDiff_omega_intervalIntegral_exp (B := c * (Work.Kernels.scale τ) ^ N')
      (mul_nonneg hc (Real.rpow_nonneg hscale.le _)) hmeasK.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have := hflat' τ t hτ ht.1 ht.2
    rwa [Real.rpow_zero, mul_one] at this
  simp only [layerLow]
  exact contDiff_omega_sinSq.mul hlow

lemma contDiff_omega_layerTrunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hT : Work.Asymptotics.TailBound ℓ d G) {τ : UpperHalfPlane}
    (hτ : τ ∈ Work.Asymptotics.DomainD) :
    ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) := by
  obtain ⟨C, M, hC, hM, hbd⟩ := ae_tail_bound_of_TailBound ℓ d G hT τ hτ
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) :=
    measurable_Kaxis_Kfun ℓ d hd τ
  have hmeasA : Measurable (fun t : ℝ => Aexp G τ t) := by unfold Aexp; fun_prop
  have htrunc : ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici 1,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t) *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    refine contDiff_omega_integral_Ici_exp (C := C) (M := M) hC hM
      (hmeasK.sub hmeasA).aestronglyMeasurable ?_
    filter_upwards [hbd] with t ht
    exact ht
  simp only [layerTrunc]
  exact contDiff_omega_sinSq.mul htrunc

/-! ## The scale comparison -/

lemma paperLayer_scale_rpow_le {τ : UpperHalfPlane} {M : ℝ} (hM : 0 ≤ M) :
    Work.Kernels.scale τ ^ M ≤ 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by
  set u : ℝ := (τ.im)⁻¹ with hudef
  set v : ℝ := ‖(τ : ℂ)‖ with hvdef
  have hu0 : 0 ≤ u := by rw [hudef]; exact inv_nonneg.mpr τ.im_pos.le
  have hv0 : 0 ≤ v := by rw [hvdef]; exact norm_nonneg _
  have hmax1 : 1 ≤ max u v := by
    by_contra h
    rw [not_le, max_lt_iff] at h
    obtain ⟨h1, h2⟩ := h
    have him : 1 < τ.im := by
      rcases (inv_lt_one_iff₀.mp (by rw [← hudef]; exact h1)) with h3 | h3
      · exact absurd h3 (not_le.mpr τ.im_pos)
      · exact h3
    have hle : τ.im ≤ v := by rw [hvdef]; exact Work.Kernels.im_le_coe_norm τ
    linarith
  have hsc : Work.Kernels.scale τ ≤ 3 * max u v := by
    rw [Work.Kernels.scale, ← hudef, ← hvdef]
    linarith [le_max_left u v, le_max_right u v]
  have hstep1 : Work.Kernels.scale τ ^ M ≤ (3 * max u v) ^ M :=
    Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hsc hM
  have hstep2 : (3 * max u v) ^ M = 3 ^ M * (max u v) ^ M :=
    Real.mul_rpow (by norm_num) (le_trans hu0 (le_max_left u v))
  have hstep3 : (max u v) ^ M = max (u ^ M) (v ^ M) := Real.rpow_max hu0 hv0 hM
  have hstep4 : max (u ^ M) (v ^ M) ≤ u ^ M + v ^ M :=
    max_le (le_add_of_nonneg_right (Real.rpow_nonneg hv0 M))
      (le_add_of_nonneg_left (Real.rpow_nonneg hu0 M))
  have huM : u ^ M = (τ.im) ^ (-M) := by
    rw [hudef, Real.inv_rpow τ.im_pos.le, Real.rpow_neg τ.im_pos.le]
  have hvM : v ^ M = ‖(τ : ℂ)‖ ^ M := by rw [hvdef]
  calc Work.Kernels.scale τ ^ M ≤ (3 * max u v) ^ M := hstep1
    _ = 3 ^ M * (max u v) ^ M := hstep2
    _ = 3 ^ M * max (u ^ M) (v ^ M) := by rw [hstep3]
    _ ≤ 3 ^ M * (u ^ M + v ^ M) :=
        mul_le_mul_of_nonneg_left hstep4 (Real.rpow_nonneg (by norm_num) M)
    _ = 3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M) := by rw [huM, hvM]

/-! ## The assembly -/

/-- **The `r`-seminorm bound for the layer `paperLayer = low + trunc + high`.**

The three pieces are estimated separately:
* `layerLow`: `4 sin²(πr²/2) ∫_0^1 K(τ,it)e^{-πr²t}dt`, bounded by `hflat` (the kernel is flat at the
  cusp `0`), which is what gives the super-polynomial decay in `λ = πr²` (substituting `s = λt`
  turns `|K| ≤ c t^N` into `O(λ^{-N})`);
* `layerTrunc`: `4 sin²(πr²/2) ∫_1^∞ (K - Aexp)(τ,it)e^{-πr²t}dt`, bounded by `hT`; the integral
  converges for every `λ ≥ 0` (on the window `[1,(scale τ)^{N₀}]` the integrand is polynomial,
  beyond it it is `O(t^M e^{-πt})`), and the pieces over the window and beyond the threshold
  contribute `e^{-λ}/λ` resp. `e^{-λ(scale τ)^{N₀}}`, both super-polynomially small in `λ`;
* `layerHigh`: the explicit expression `highPart`, whose seminorms are bounded by the explicit
  factors `λψ₁(λ)e^{-λ}`, `ψ₁(λ)(λ+1)e^{-λ}`, `μψ₁(μ)e^{-μ}`, `ψ₁(μ)(μ+1)e^{-μ` times the
  moderate growth of `G` (`mu = λ - 2π`).

The conclusion is written in the target form `α(im τ)^{-β} + γ‖τ‖^δ`, which is equivalent to
`c(scale τ)^N` (`scale τ = 1 + (im τ)⁻¹ + ‖τ‖`). -/
theorem paperLayer_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.DomainD → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ c * (Work.Kernels.scale τ) ^ N' * t ^ N)
    (hT : Work.Asymptotics.TailBound ℓ d G) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  intro k l
  obtain ⟨cL, NL, hcL, hL⟩ := layerLow_seminorm ℓ d hd hflat k l
  obtain ⟨cT, NT, hcT, hTb⟩ := layerTrunc_seminorm_of_tailBound ℓ d hd G hT k l
  obtain ⟨cH, NH, hcH, hHb⟩ := highPart_seminorm_scaled G hG k l
  set M : ℝ := max (max (max NL NT) NH) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hNL : NL ≤ M :=
    le_trans (le_trans (le_max_left NL NT) (le_max_left (max NL NT) NH)) (le_max_left _ _)
  have hNT : NT ≤ M :=
    le_trans (le_trans (le_max_right NL NT) (le_max_left (max NL NT) NH)) (le_max_left _ _)
  have hNH : NH ≤ M := le_trans (le_max_right (max NL NT) NH) (le_max_left _ _)
  have hc : 0 ≤ cL + cT + cH := by linarith
  refine ⟨(cL + cT + cH) * 3 ^ M, M, (cL + cT + cH) * 3 ^ M, M,
    by positivity, hM0, by positivity, hM0, ?_⟩
  intro τ r hτ
  have hS1 : 1 ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hlow_at : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => layerLow ℓ d τ s) r :=
    ((contDiff_omega_layerLow ℓ d hd hflat hτ).contDiffAt).of_le le_top
  have htrunc_at : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => layerTrunc G ℓ d τ s) r :=
    ((contDiff_omega_layerTrunc ℓ d hd G hT hτ).contDiffAt).of_le le_top
  have hhigh_at : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => highPart G τ s) r :=
    ((contDiff_omega_highPart G τ).contDiffAt).of_le le_top
  have hsplit1 : iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r := by
    change iteratedDeriv l ((fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s)
      + fun s : ℝ => highPart G τ s) r = _
    exact iteratedDeriv_add (hlow_at.add htrunc_at) hhigh_at
  have hsplit2 : iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r := by
    change iteratedDeriv l ((fun s : ℝ => layerLow ℓ d τ s)
      + fun s : ℝ => layerTrunc G ℓ d τ s) r = _
    exact iteratedDeriv_add hlow_at htrunc_at
  have hsplit : iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r := by
    rw [hsplit1, hsplit2]
  have hA := hL τ r hτ
  have hB := hTb τ r hτ
  have hC := hHb τ r hτ
  have hNLb : cL * Work.Kernels.scale τ ^ NL ≤ cL * Work.Kernels.scale τ ^ M :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 hNL) hcL
  have hNTb : cT * Work.Kernels.scale τ ^ NT ≤ cT * Work.Kernels.scale τ ^ M :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 hNT) hcT
  have hNHb : cH * Work.Kernels.scale τ ^ NH ≤ cH * Work.Kernels.scale τ ^ M :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 hNH) hcH
  have hkey := paperLayer_scale_rpow_le (τ := τ) hM0
  rw [hsplit]
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2 : ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
              + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
            ≤ ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
              + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖ := norm_add_le _ _
        linarith [norm_add_le
          (iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
            + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r)
          (iteratedDeriv l (fun s : ℝ => highPart G τ s) r), h2]
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖ := by ring
    _ ≤ cL * Work.Kernels.scale τ ^ NL + cT * Work.Kernels.scale τ ^ NT
          + cH * Work.Kernels.scale τ ^ NH := by linarith
    _ ≤ (cL + cT + cH) * Work.Kernels.scale τ ^ M := by
        have hsum : cL * Work.Kernels.scale τ ^ M + cT * Work.Kernels.scale τ ^ M
            + cH * Work.Kernels.scale τ ^ M
            = (cL + cT + cH) * Work.Kernels.scale τ ^ M := by ring
        linarith [hNLb, hNTb, hNHb]
    _ ≤ ((cL + cT + cH) * 3 ^ M) * (τ.im) ^ (-M)
          + ((cL + cT + cH) * 3 ^ M) * ‖(τ : ℂ)‖ ^ M := by
        calc (cL + cT + cH) * Work.Kernels.scale τ ^ M
            ≤ (cL + cT + cH)
                * (3 ^ M * ((τ.im) ^ (-M) + ‖(τ : ℂ)‖ ^ M)) :=
              mul_le_mul_of_nonneg_left hkey hc
          _ = ((cL + cT + cH) * 3 ^ M) * (τ.im) ^ (-M)
                + ((cL + cT + cH) * 3 ^ M) * ‖(τ : ℂ)‖ ^ M := by ring


end Work.Asymptotics
