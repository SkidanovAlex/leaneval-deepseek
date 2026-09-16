import Mathlib.NumberTheory.LSeries.Nonvanishing

noncomputable section
open Complex Filter
open scoped Real Topology

namespace Commons.NumberTheory.Zeta

/-!
# `zeta_logDeriv_re_axis_bound`

The real part of `−ζ′/ζ` on the real axis `s = σ ∈ (1, 2]` satisfies

    Re(−ζ′/ζ)(σ) ≤ 1/(σ − 1) + C

for some absolute constant `C > 0`.

**Proof.**  Write `ζ₁(s) = (s − 1)·ζ(s)` (the completion of `ζ` at `s = 1`, an
entire function with `ζ₁(1) = 1`).  Taking logarithmic derivatives of the identity
`ζ(s) = (s−1)⁻¹·ζ₁(s)` gives, for `s ≠ 1` with `ζ₁(s) ≠ 0`,

    ζ′/ζ(s) = ζ₁′/ζ₁(s) − 1/(s − 1),

hence

    Re(−ζ′/ζ)(σ) = 1/(σ − 1) − Re(ζ₁′/ζ₁)(σ).

On the segment `σ ∈ [1, 2]` the function `ζ₁` is zero-free: for `σ = 1` this is
`ζ₁(1) = 1`, and for `σ > 1` it follows from `(σ − 1) ζ(σ) = ζ₁(σ)` together with
the standard (Mathlib) non-vanishing of `ζ` on `Re s ≥ 1`.  Hence `ζ₁′/ζ₁` is
continuous (indeed analytic) on the compact interval `[1, 2]`, so it is bounded:
`Re(ζ₁′/ζ₁)(σ) ≥ −C₀` for all `σ ∈ [1, 2]`.  Substituting yields the claim with
`C = max C₀ 0 + 1`.
-/

/-- **Log-derivative identity for the completion `ζ₁`.**  For `s ≠ 1` with
`ζ₁ s ≠ 0`,

    ζ′/ζ(s) = ζ₁′/ζ₁(s) − 1/(s − 1). -/
private lemma deriv_zeta_div_zeta_eq (s : ℂ) (hs : s ≠ 1) (hZ : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by
  rw [riemannZeta_eq_inv_sub_mul hs, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hZ, h1]
  ring

/-- `ζ₁ = (s − 1)·ζ` does not vanish on the real segment `[1, 2]`. -/
private lemma riemannZeta₁_ne_zero_of_mem_Icc (σ : ℝ) (hσ : σ ∈ Set.Icc (1 : ℝ) 2) :
    riemannZeta₁ (σ : ℂ) ≠ 0 := by
  intro hz
  have hσ1 : (1 : ℝ) ≤ σ := hσ.1
  by_cases hs1 : σ = 1
  · subst hs1
    rw [Complex.ofReal_one, riemannZeta₁_one] at hz
    exact one_ne_zero hz
  · have hsc : (σ : ℂ) ≠ 1 := by
      intro h
      apply hs1
      have := congrArg Complex.re h
      simpa using this
    have hζ : riemannZeta (σ : ℂ) = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hsc, hz, mul_zero]
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1) hζ

/-- `Re(ζ₁′/ζ₁) ≥ −C₀` on the real segment `[1, 2]`, by compactness. -/
private lemma zeta1_logDeriv_re_lower_on_Icc :
    ∃ C : ℝ, ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
      -C ≤ (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re := by
  have hderiv : Continuous (deriv riemannZeta₁) :=
    (differentiable_riemannZeta₁.contDiff (n := ⊤)).continuous_deriv le_top
  have hnum : ContinuousOn (fun σ : ℝ => deriv riemannZeta₁ (σ : ℂ)) (Set.Icc (1 : ℝ) 2) :=
    (hderiv.comp Complex.continuous_ofReal).continuousOn
  have hden : ContinuousOn (fun σ : ℝ => riemannZeta₁ (σ : ℂ)) (Set.Icc (1 : ℝ) 2) :=
    ((differentiable_riemannZeta₁.continuous).comp Complex.continuous_ofReal).continuousOn
  have hne : ∀ σ ∈ Set.Icc (1 : ℝ) 2, riemannZeta₁ (σ : ℂ) ≠ 0 :=
    fun σ hσ => riemannZeta₁_ne_zero_of_mem_Icc σ hσ
  have hcont : ContinuousOn
      (fun σ : ℝ => deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)) (Set.Icc (1 : ℝ) 2) :=
    hnum.div hden hne
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨C₀, ?_⟩
  intro σ hσ
  have hnorm : -(deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re ≤
      ‖deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)‖ := by
    have h := Complex.re_le_norm (-(deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)))
    rw [Complex.neg_re, norm_neg] at h
    exact h
  have := hC₀ σ hσ
  linarith

theorem zeta_logDeriv_re_axis_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨C₀, hC₀⟩ := zeta1_logDeriv_re_lower_on_Icc
  refine ⟨max C₀ 0 + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2
  have hσmem : σ ∈ Set.Icc (1 : ℝ) 2 := ⟨le_of_lt hσ1, hσ2⟩
  set s : ℂ := (σ : ℂ) with hs
  have hsne : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h]; simp
    rw [hs] at hre
    simp at hre
    linarith
  have hZ : riemannZeta₁ s ≠ 0 := by
    rw [hs]
    exact riemannZeta₁_ne_zero_of_mem_Icc σ hσmem
  have hId : deriv riemannZeta s / riemannZeta s =
      deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ :=
    deriv_zeta_div_zeta_eq s hsne hZ
  have hneg : (-deriv riemannZeta s) / riemannZeta s =
      (s - 1)⁻¹ - deriv riemannZeta₁ s / riemannZeta₁ s := by
    rw [neg_div, hId, neg_sub]
  have hre : ((-deriv riemannZeta s) / riemannZeta s).re =
      ((s - 1)⁻¹).re - (deriv riemannZeta₁ s / riemannZeta₁ s).re := by
    rw [hneg, Complex.sub_re]
  have hsub : s - 1 = ((σ - 1 : ℝ) : ℂ) := by
    rw [hs]; push_cast; ring
  have hreinv : ((s - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hbound : -C₀ ≤ (deriv riemannZeta₁ s / riemannZeta₁ s).re := by
    rw [hs]
    exact hC₀ σ hσmem
  have hgoal : ((-deriv riemannZeta s) / riemannZeta s).re ≤ 1 / (σ - 1) + (max C₀ 0 + 1) := by
    rw [hre, hreinv]
    have hmax : C₀ ≤ max C₀ 0 := le_max_left C₀ 0
    linarith
  exact hgoal

end Commons.NumberTheory.Zeta