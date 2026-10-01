/-
# Area 4 / HB §12 — the test function of Heath-Brown's Lemma 7.1 / 7.4

Namespace `Work.LinnikAreas.Density4`.  Heath-Brown's §12 (the new zero-density estimate,
Lemma 12.1) is applied with the extremal test function of his §7.  With parameters
`0 < θ < π` and `λ̂ > 0` put

* `ζ = -λ̂ tan θ`  (`zetaT`),  `γ = θ/ζ`  (`gammaT`);
* `g(t) = λ̂(1+tan²θ)(cos(ζt) - cos θ)` on `[-γ,γ]`, `0` outside (`gT`);
* `f = g ⊛ g`  (`fT`), given in closed form by HB's Lemma 7.1/7.4 (see `fT_eq_conv`);
* `F(z) = ∫₀^{2γ} e^{-zt} f(t) dt`  (`FT`).

For `θ > π/2` (the branch used in HB's Table 13, where `θ ≈ λ/2 - λ₁/6 + 1.7`) one has
`tan θ < 0`, hence `ζ > 0` and `γ > 0`, and `cos θ < 0`; and for `|t| ≤ γ` one has
`|ζt| ≤ θ < π`, so `cos(ζt) ≥ cos θ` — hence `g ≥ 0`, so `f = g ⊛ g ≥ 0` and `f` is supported
in `[0,2γ]`: the two conditions needed in §5/§12.

All closed forms here were re-derived from HB §7 and cross-checked numerically (quadrature)
before being stated.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- `ζ = -λ̂ tan θ` (HB §7 with `ρ = iζ/λ̂`: `ζ = -λ̂ tan θ`).  For `π/2 < θ < π` and `λ̂ > 0`
this is `λ̂ |tan θ| > 0`. -/
def zetaT (θ lam : ℝ) : ℝ := - lam * Real.tan θ

/-- `γ = θ/ζ` (HB §7). -/
def gammaT (θ lam : ℝ) : ℝ := θ / zetaT θ lam

/-- HB §7: `g(t) = λ̂(1+tan²θ)(cos(ζt) - cos θ)` on `[-γ,γ]`, `0` outside. -/
def gT (θ lam : ℝ) (t : ℝ) : ℝ :=
  if |t| ≤ gammaT θ lam then lam * (1 + Real.tan θ ^ 2) * (Real.cos (zetaT θ lam * t) - Real.cos θ)
  else 0

/-- HB Lemma 7.1/7.4: the closed form of `f = g ⊛ g`, **clamped to its support** `[0,2γ]`
(the unclamped trigonometric expression is the identity only on that interval).  Derived from HB §7;
the identity with the convolution of `gT` — for *every* `x : ℝ` — is the lemma `testfun_conv`. -/
def fT (θ lam : ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x ≤ 2 * gammaT θ lam then
    lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
      ( (2 * gammaT θ lam - x) * (Real.cos (zetaT θ lam * x) / 2 + Real.cos θ ^ 2)
        + Real.sin (2 * θ - zetaT θ lam * x) / (2 * zetaT θ lam)
        - Real.sin (2 * θ) / zetaT θ lam
        + 2 * Real.cos θ * Real.sin (zetaT θ lam * x - θ) / zetaT θ lam )
  else 0

/-- HB §7: the Laplace transform `F(z) = ∫₀^{2γ} e^{-zt} f(t) dt` of the test function. -/
def FT (θ lam : ℝ) (z : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(2 * gammaT θ lam), Real.exp (-(z * t)) * fT θ lam t


/-- The test-function parameter `θ` of HB's Table 13 (`θ ≈ λ/2 - λ₁/6 + 1.7`, `λ̂ = λ`), and the
argument `F(-λ₁)` of (12.1).  `theta13` is the value HB used; the numerical certificate
`table13_cert` verifies that the resulting bound is `< N₀ + 1`. -/
def theta13 (lam lam1 : ℝ) : ℝ := lam / 2 - lam1 / 6 + 17 / 10

/-- **HB (12.1) with the §7 test function**: the bound
`F(-λ₁)(F(-λ₁) - f(0)/6) / ((F(λ-λ₁) - f(0)/6)² - F(-λ₁)f(0)/6)` for the test function with
parameters `θ = θ13 λ λ₁` and `λ̂ = λ`.  Lemma 12.1 then gives `N(λ) ≤ bnd13 λ λ₁ + ε`. -/
def bnd13 (lam lam1 : ℝ) : ℝ :=
  FT (theta13 lam lam1) lam (-lam1) *
    (FT (theta13 lam lam1) lam (-lam1) - fT (theta13 lam lam1) lam 0 / 6) /
  ((FT (theta13 lam lam1) lam (lam - lam1) - fT (theta13 lam lam1) lam 0 / 6) ^ 2
    - FT (theta13 lam lam1) lam (-lam1) * fT (theta13 lam lam1) lam 0 / 6)

/-- For `π/2 < θ < π`, `cos θ < 0`. -/
lemma cos_neg_of_gt_half_pi {θ : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) :
    Real.cos θ < 0 :=
  Real.cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [Real.pi_pos])

/-- For `π/2 < θ < π`, `tan θ < 0`. -/
lemma tan_neg_of_half_pi_lt {θ : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) :
    Real.tan θ < 0 := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_neg_of_pos_of_neg (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hθ2)
    (cos_neg_of_gt_half_pi hθ1 hθ2)

/-- For `0 ≤ θ < π`, `-1 < cos θ`. -/
lemma neg_one_lt_cos_of_lt_pi {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi) :
    -1 < Real.cos θ := by
  have h1 : Real.cos Real.pi < Real.cos θ :=
    Real.strictAntiOn_cos ⟨hθ0, le_of_lt hθ⟩ ⟨Real.pi_pos.le, le_refl _⟩ hθ
  rwa [Real.cos_pi] at h1

/-- For `π/2 < θ < π` and `λ̂ > 0`, `ζ = -λ̂ tan θ > 0`. -/
lemma zetaT_pos {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    0 < zetaT θ lam := by
  rw [zetaT]
  exact mul_pos_of_neg_of_neg (by linarith) (tan_neg_of_half_pi_lt hθ1 hθ2)

/-- For `π/2 < θ < π` and `λ̂ > 0`, `γ = θ/ζ > 0`. -/
lemma gammaT_pos {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    0 < gammaT θ lam :=
  div_pos (lt_trans (by linarith [Real.pi_pos]) hθ1) (zetaT_pos hθ1 hθ2 hlam)

/-- On `(-γ,γ)`, `|ζt| < θ`; hence `cos(ζt) ≥ cos θ` and `g > 0`. -/
lemma gT_pos {θ lam t : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam)
    (ht : |t| < gammaT θ lam) : 0 < gT θ lam t := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hθ0 : 0 < θ := lt_trans (by linarith [Real.pi_pos]) hθ1
  have habs : |zetaT θ lam * t| < θ := by
    rw [abs_mul, abs_of_pos hζ]
    have h1 : zetaT θ lam * |t| < zetaT θ lam * gammaT θ lam :=
      mul_lt_mul_of_pos_left ht hζ
    rwa [gammaT, mul_div_cancel₀ _ (ne_of_gt hζ)] at h1
  have hmem1 : |zetaT θ lam * t| ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨abs_nonneg _, le_of_lt (lt_trans habs hθ2)⟩
  have hmem2 : θ ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_of_lt hθ0, le_of_lt hθ2⟩
  have hcosθ : Real.cos θ < Real.cos (zetaT θ lam * t) := by
    have h := Real.strictAntiOn_cos hmem1 hmem2 habs
    rwa [Real.cos_abs] at h
  rw [gT, if_pos (le_of_lt ht)]
  exact mul_pos (mul_pos hlam (by positivity)) (by linarith)

end Work.LinnikAreas.Density4
