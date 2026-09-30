import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.vk_L_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared definitions for the Vinogradov–Korobov zero-free region (node V3, exponent `6/7`)

This module holds the definitions shared by the node `V3` (`LFunction_zeroFree_VK`,
the zero-free region of Vinogradov–Korobov type for Dirichlet `L`-functions) and by the
delegated lemma `LFunction_strip_VK` (the strip logarithmic-derivative bound derived from
the growth bound `V2`), together with a couple of elementary real/elementary-zeta estimates
that both use.

* `VKGrowth A c` — the Vinogradov–Korobov growth bound in the strip
  `‖L(σ+it,χ)‖ ≤ A N (log(|t|+3))^{6/7}` for `σ ≥ 1 - c (log(|t|+3))^{-6/7}` (node `V2`).
* `VKDenom N γ η` — the logarithmic denominator `log(N+2) + log log(|γ|+3) + log(1/η) + 1`.
* `VKStrip c E` — the strip logarithmic-derivative bounds (regular form and pole form)
  with constants `c`, `E`.
-/

set_option autoImplicit false

namespace Work.BMF

open Complex

/-- **Vinogradov–Korobov growth bound for `L(s, χ)` near the line `Re s = 1`** (node `V2`,
`Submission.Work.BMF.L_growth_VK`), as a predicate: there are constants `A > 0` and `c > 0` such
that for every modulus `N ≥ 1` and every character `χ` mod `N`,
`‖L(σ+it, χ)‖ ≤ A N (log(|t|+3))^{6/7}` whenever `3 ≤ |t|`,
`1 - c (log(|t|+3))^{-6/7} ≤ σ` and `σ ≤ 2`. -/
def VKGrowth (A c : ℝ) : Prop :=
  0 < A ∧ 0 < c ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (σ t : ℝ),
      3 ≤ |t| → 1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          A * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ)

/-- The logarithmic denominator `log(N+2) + log log(|γ|+3) + log(1/η) + log(1/x) + 1`
occurring in the strip logarithmic-derivative bound. -/
noncomputable def VKDenom (N : ℕ) (γ η x : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (Real.log (|γ| + 3)) + Real.log (1 / η) +
    Real.log (1 / x) + 1

/-- **The strip logarithmic-derivative bound of Vinogradov–Korobov type.**

`VKStrip c E` says: there is the constant `E > 0` (the first conjunct) such that for every
modulus `N`, every character `χ` mod `N`, every `|γ| ≥ 10`, every `0 < x ≤ η/8` with
`x + 2η ≤ 1` and every `η ≤ c (log(|γ|+3))^{-6/7}`:

* (regular form) `-Re (L'/L)(1+x+iγ, χ) ≤ E · VKDenom N γ η x / η`;
* (pole form) if moreover `0 < β < 1`, `1-β ≤ η/16` and `L(β+iγ, χ) = 0`, then
  `-Re (L'/L)(1+x+iγ, χ) ≤ -1/(x+1-β) + E · VKDenom N γ η x / η`.

The pole form is the input of the classical `3-4-1` zero detection argument, at the zero's own
height; the regular form is applied to a character inducing `χ²`. -/
def VKStrip (c E : ℝ) : Prop :=
  0 < E ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (γ x η : ℝ),
      10 ≤ |γ| → 0 < x → x ≤ η / 8 → x + 2 * η ≤ 1 →
      η ≤ c * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) →
      (-logDeriv (DirichletCharacter.LFunction χ)
          (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re ≤
        E * VKDenom N γ η x / η) ∧
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (γ x η β : ℝ),
      10 ≤ |γ| → 0 < x → x ≤ η / 8 → x + 2 * η ≤ 1 →
      η ≤ c * Real.log (|γ| + 3) ^ (-(6 / 7 : ℝ)) →
      0 < β → β < 1 → 1 - β ≤ η / 16 →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 →
      (-logDeriv (DirichletCharacter.LFunction χ)
          (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re ≤
        -1 / (x + 1 - β) + E * VKDenom N γ η x / η)

/-- **Upper bound for `ζ` just to the right of `1`**: there is an absolute constant `C > 0` with
`‖ζ(1+x)‖ ≤ C/x` for `0 < x ≤ 1/2`.  (Immediate from `ζ(s) = (s-1)⁻¹ ζ₁(s)` with `ζ₁` entire,
`ζ₁(1) = 1`, and compactness of `[1, 3/2]`.) -/
theorem riemannZeta_norm_le_const_div :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
      ‖riemannZeta (((1 + x : ℝ) : ℂ))‖ ≤ C / x := by
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) (3 / 2) →
      ‖riemannZeta₁ ((σ : ℂ))‖ ≤ C₁ := by
    have hcont : ContinuousOn (fun σ : ℝ => ‖riemannZeta₁ ((σ : ℂ))‖) (Set.Icc (1 : ℝ) (3 / 2)) :=
      (differentiable_riemannZeta₁.continuous.comp continuous_ofReal).norm.continuousOn
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    exact ⟨C₁, fun σ hσ => by simpa using hC₁ σ hσ⟩
  refine ⟨max (max C₁ 0) 1, by positivity, ?_⟩
  intro x hx hx2
  have hne : ((1 + x : ℝ) : ℂ) ≠ 1 := by
    intro h
    have h' : (1 + x : ℝ) = 1 := by exact_mod_cast h
    linarith
  have hfac : riemannZeta (((1 + x : ℝ) : ℂ)) =
      ((x : ℂ))⁻¹ * riemannZeta₁ (((1 + x : ℝ) : ℂ)) := by
    rw [riemannZeta_eq_inv_sub_mul hne]
    congr 1
    push_cast
    ring
  have hb : ‖riemannZeta₁ (((1 + x : ℝ) : ℂ))‖ ≤ max (max C₁ 0) 1 := by
    have hmem : (1 + x : ℝ) ∈ Set.Icc (1 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
    have h := hC₁ (1 + x) hmem
    exact le_trans h (le_trans (le_max_left _ _) (le_max_left _ _))
  have hxi : ‖((x : ℂ))⁻¹‖ = 1 / x := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, inv_eq_one_div]
  rw [hfac, norm_mul, hxi]
  calc (1 / x) * ‖riemannZeta₁ _‖ ≤ (1 / x) * max (max C₁ 0) 1 :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ max (max C₁ 0) 1 / x := by rw [one_div, inv_mul_eq_div]

/-- **`L(1+x+iγ, χ)` is bounded below by a constant multiple of `x`**, uniformly in the
modulus and in the character. -/
theorem exists_LFunction_norm_lower_one_add :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (x γ : ℝ),
      0 < x → x ≤ 1 / 2 →
        x / C ≤ ‖DirichletCharacter.LFunction χ (((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := riemannZeta_norm_le_const_div
  refine ⟨max C₀ 1, by positivity, ?_⟩
  intro N hN χ x γ hx hx2
  have hN' : NeZero N := hN
  set s : ℂ := ((1 + x : ℝ) : ℂ) + (γ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + x := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hlow := vk_L_lower χ (s := s) hs1
  have hζlt : (riemannZeta (s.re : ℂ)).re ≤ max C₀ 1 / x := by
    have h1 : ‖riemannZeta (((1 + x : ℝ) : ℂ))‖ ≤ C₀ / x := hC₀ x hx hx2
    have h2 : (riemannZeta (((1 + x : ℝ) : ℂ))).re ≤
        ‖riemannZeta (((1 + x : ℝ) : ℂ))‖ := Complex.re_le_norm _
    have h3 : C₀ / x ≤ max C₀ 1 / x :=
      div_le_div_of_nonneg_right (le_max_left _ _) hx.le
    rw [hsre]
    linarith
  have h1 : 1 ≤ ‖DirichletCharacter.LFunction χ s‖ * (max C₀ 1 / x) :=
    le_trans hlow (mul_le_mul_of_nonneg_left hζlt (norm_nonneg _))
  have h2 : x / max C₀ 1 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
    rw [div_le_iff₀ (by positivity)]
    calc x = x * 1 := by ring
      _ ≤ x * (‖DirichletCharacter.LFunction χ s‖ * (max C₀ 1 / x)) :=
          mul_le_mul_of_nonneg_left h1 hx.le
      _ = ‖DirichletCharacter.LFunction χ s‖ * max C₀ 1 := by field_simp
  simpa [hs] using h2

/-- **Analyticity of `L(·, χ)` on a disc avoiding `1`.** -/
lemma LFunction_analyticOnNhd_closedBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {c : ℂ} {R : ℝ} (h1 : (1 : ℂ) ∉ Metric.closedBall c R) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall c R) := by
  intro z hz
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hz1 : z ≠ 1 := fun h => h1 (h ▸ hz)
  filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
  exact DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw)

end Work.BMF
