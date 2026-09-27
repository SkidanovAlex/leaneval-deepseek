import Mathlib
import Submission.Work.EQ.Defs

/-!
# Setup for `exists_stableGerm`

We construct the linearised local stable germ of the equichordal half map.

Write `λ = eqLam a = (1-a)/(1+a) ∈ (0,1)` and `h_ρ(u) = -u + u³ ρ(u)`.
The germ equation `GermFE a h 0 = 0` (cleared form) reads, with `A = h(u/λ)`, `B = h u`,
`C = h(λu)` and `S = √(1+B²)`:

  `(B-A)(C-B) + a B (C-A) S = 0`.

Writing `B = u β`, `A = (u/λ) α`, `C = λ u γ` and dividing by `u²` the equation becomes
`G(ρ)(u) = 0` where `G = GlinOf + GnlOf` is the explicit function of `u`, `ρ u`, `ρ (λu)`,
`ρ (u/λ)` and `S = (1 + u² β²)^{1/2}` defined below; the "constant" (order `u⁰`) terms cancel
precisely because `1 - λ = a(1+λ)`.

`GlinOf` is linear in `ρ` and telescopes:  `∑_j λ^{4j+2} Glin(λ^{2j+1}u) = -a ρ(u)`.
Hence the equation `G = 0` is equivalent to the fixed point equation `ρ = Θ(ρ)` for the
nonlinear operator `ThetaOf` below, which is a contraction on the ball `‖ρ‖ ≤ 1` (sup norm
on the closed disc of radius `germR a`).

All definitions are stated for a general function `ρ : ℂ → ℂ`; the analyticity hypotheses
enter only in the lemmas.
-/

namespace Work.EQ

open Complex Metric Filter

noncomputable section

variable {a : ℝ}

/-- `λ = eqLam a` regarded as a complex number. -/
noncomputable def lamC (a : ℝ) : ℂ := (eqLam a : ℂ)

/-- The radius of the disc on which the germ is constructed.  It is chosen small enough
that all the elementary estimates below hold; any sufficiently small radius would do. -/
noncomputable def germR (a : ℝ) : ℝ := min ((eqLam a) ^ 2 / 16) (a / 100)

/-- `κ = 1/λ - λ`, as a complex number. -/
noncomputable def kapC (a : ℝ) : ℂ := ((eqLam a)⁻¹ - eqLam a : ℝ)

/-- `h_ρ(u) = -u + u³ ρ(u)`.  `ρ` is the unknown of the fixed point equation; the resulting
germ is `h_ρ`. -/
noncomputable def hOf (ρ : ℂ → ℂ) (u : ℂ) : ℂ := -u + u ^ 3 * ρ u

/-- `β = h_ρ(u)/u = -1 + u² ρ(u)`. -/
noncomputable def betaOf (ρ : ℂ → ℂ) (u : ℂ) : ℂ := -1 + u ^ 2 * ρ u

/-- `S = √(1 + (h_ρ u)²) = (1 + u² β²)^{1/2}` (principal branch). -/
noncomputable def SOf (ρ : ℂ → ℂ) (u : ℂ) : ℂ := (1 + u ^ 2 * (betaOf ρ u) ^ 2) ^ (1 / 2 : ℂ)

/-- `W = (S - 1)/u² = β²/(1 + S)`, the analytic version of `(S-1)/u²`. -/
noncomputable def WOf (ρ : ℂ → ℂ) (u : ℂ) : ℂ := (betaOf ρ u) ^ 2 / (1 + SOf ρ u)

/-- `A₁ = ρ(u) - λ^{-3} ρ(u/λ)`. -/
noncomputable def A1Of (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  ρ u - ((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)

/-- `A₂ = λ³ ρ(λu) - ρ(u)`. -/
noncomputable def A2Of (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  (lamC a) ^ 3 * ρ (lamC a * u) - ρ u

/-- `A₃ = λ³ ρ(λu) - λ^{-3} ρ(u/λ)`. -/
noncomputable def A3Of (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  (lamC a) ^ 3 * ρ (lamC a * u) - ((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)

/-- The linear part of the residual: `a (λ² ρ(λu) - λ^{-2} ρ(u/λ))`. -/
noncomputable def GlinOf (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  (a : ℂ) * ((lamC a) ^ 2 * ρ (lamC a * u) - ((lamC a) ^ 2)⁻¹ * ρ (u / lamC a))

/-- The non-linear part of the residual. -/
noncomputable def GnlOf (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  -((a : ℂ) * kapC a * WOf ρ u)
    + u ^ 2 * A1Of a ρ u * A2Of a ρ u
    + (a : ℂ) * u ^ 2 * ρ u * A3Of a ρ u
    + (a : ℂ) * u ^ 2 * WOf ρ u * (-(A3Of a ρ u) + kapC a * ρ u)
    + (a : ℂ) * u ^ 4 * WOf ρ u * ρ u * A3Of a ρ u

/-- The full residual `G = Glin + Gnl`; the germ equation is `G(ρ)(u) = 0`. -/
noncomputable def GOf (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ := GlinOf a ρ u + GnlOf a ρ u

/-- An explicit Lipschitz constant for `GnlOf` on the unit ball: the estimate
`‖Gnl(ρ₁) u - Gnl(ρ₂) u‖ ≤ λ² r² (gLipK a) M` holds whenever `‖ρᵢ‖ ≤ 1` and `‖ρ₁-ρ₂‖ ≤ M`
on the disc of radius `germR a`. -/
noncomputable def gLipK (a : ℝ) : ℝ :=
  12 * a * ((eqLam a)⁻¹ - eqLam a)
    + 2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3)
    + 2 * a * (1 + ((eqLam a) ^ 3)⁻¹)
    + 4 * a * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a))
    + a * (1 + ((eqLam a) ^ 3)⁻¹)

/-- The fixed point operator `Θ(ρ)(u) = a⁻¹ ∑_j λ^{4j+2} Gnl(ρ)(λ^{2j+1} u)`. -/
noncomputable def ThetaOf (a : ℝ) (ρ : ℂ → ℂ) (u : ℂ) : ℂ :=
  (a : ℂ)⁻¹ * ∑' (j : ℕ), (lamC a) ^ (4 * j + 2) * GnlOf a ρ ((lamC a) ^ (2 * j + 1) * u)

/-- The resolvent `Λ⁻¹ F (u) = -∑_j λ^{-(2j+1)} F(λ^{2j+1} u)` of the linear map
`Λ F (u) = F(λu)/λ - λ F(u/λ)` appearing in the telescoping identity. -/
noncomputable def LamInvOf (a : ℝ) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  -∑' (j : ℕ), ((lamC a) ^ (2 * j + 1))⁻¹ * F ((lamC a) ^ (2 * j + 1) * u)

end



section LamFacts

lemma eqLam_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma eqLam_lt_one {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma eqLam_le_one {a : ℝ} (h0 : 0 < a) : eqLam a ≤ 1 := by
  rw [eqLam, div_le_one (by linarith)]; linarith

lemma eqLam_nonneg {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1) : 0 ≤ eqLam a := by
  rw [eqLam]; exact div_nonneg (by linarith) (by linarith)

lemma one_sub_eqLam_gs {a : ℝ} (h0 : 0 < a) : 1 - eqLam a = a * (1 + eqLam a) := by
  have ha : (1 + a : ℝ) ≠ 0 := by linarith
  rw [eqLam]
  field_simp
  ring

lemma a_eq {a : ℝ} (h0 : 0 < a) : a = (1 - eqLam a) / (1 + eqLam a) := by
  have ha : (1 + a : ℝ) ≠ 0 := by linarith
  rw [eqLam]
  field_simp
  ring

lemma lamC_ne_zero_gs {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : lamC a ≠ 0 := by
  simp only [lamC, ne_eq]
  exact_mod_cast (ne_of_gt (eqLam_pos h0 h1))

lemma kapC_ne_zero {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : kapC a ≠ 0 := by
  simp only [kapC, ne_eq]
  intro h
  have hh : (eqLam a)⁻¹ - eqLam a = 0 := by exact_mod_cast h
  have hpos := eqLam_pos h0 h1
  have hlt := eqLam_lt_one h0 h1
  have h1' : (eqLam a)⁻¹ = eqLam a := sub_eq_zero.mp hh
  have h2 := congrArg (fun x : ℝ => x * eqLam a) h1'
  rw [inv_mul_cancel₀ (ne_of_gt hpos)] at h2
  nlinarith [sq_nonneg (eqLam a), sq_lt_sq' (by linarith : -(1:ℝ) < eqLam a) hlt]

section GermRFacts

lemma germR_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : 0 < germR a := by
  rw [germR]
  exact lt_min (by have := eqLam_pos h0 h1; positivity) (by positivity)

lemma germR_le_lam_sq (a : ℝ) : germR a ≤ (eqLam a) ^ 2 / 16 := min_le_left _ _

lemma germR_le_a_div (a : ℝ) : germR a ≤ a / 100 := min_le_right _ _

lemma germR_lt_one {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : germR a < 1 := by
  have h := germR_le_lam_sq a
  have h2 : (eqLam a) ^ 2 / 16 < 1 := by
    have hl := eqLam_lt_one h0 h1
    have hp := eqLam_pos h0 h1
    nlinarith
  linarith

lemma germR_le_one {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : germR a ≤ 1 :=
  le_of_lt (germR_lt_one h0 h1)

lemma lam_mul_germR_le_germR {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    eqLam a * germR a ≤ germR a := by
  have hp := eqLam_pos h0 h1
  have hlt := eqLam_lt_one h0 h1
  have hr := germR_pos h0 h1
  nlinarith

lemma lam_pow_six_eq_lam_sq_mul_sq_sq (a : ℝ) :
    (eqLam a) ^ 2 * ((eqLam a) ^ 2 / 16) ^ 2 = (eqLam a) ^ 6 / 256 := by ring

lemma lam_sq_mul_germR_sq_le {a : ℝ} (h0 : 0 < a) (h1 : a < 1) :
    (eqLam a) ^ 2 * (germR a) ^ 2 ≤ 1 / 256 := by
  have h := germR_le_lam_sq a
  have hp := eqLam_pos h0 h1
  have hlt := eqLam_lt_one h0 h1
  have hr : 0 ≤ germR a := le_of_lt (germR_pos h0 h1)
  have h1' : (germR a) ^ 2 ≤ ((eqLam a) ^ 2 / 16) ^ 2 := by
    have h2 : 0 ≤ (eqLam a)^2/16 := by positivity
    nlinarith
  have h2 : (eqLam a)^2 * (germR a)^2 ≤ (eqLam a)^2 * ((eqLam a)^2/16)^2 :=
    mul_le_mul_of_nonneg_left h1' (by positivity)
  have h4 : (eqLam a)^6 ≤ 1 := pow_le_one₀ (le_of_lt hp) (le_of_lt hlt)
  rw [lam_pow_six_eq_lam_sq_mul_sq_sq a] at h2
  linarith

lemma germR_sq_le {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : (germR a) ^ 2 ≤ 1 / 256 := by
  have h := germR_le_lam_sq a
  have hp := eqLam_pos h0 h1
  have hlt := eqLam_lt_one h0 h1
  have hr : 0 ≤ germR a := le_of_lt (germR_pos h0 h1)
  have h1' : (germR a) ^ 2 ≤ ((eqLam a) ^ 2 / 16) ^ 2 := by
    have h2 : 0 ≤ (eqLam a)^2/16 := by positivity
    nlinarith
  have h4 : (eqLam a)^4 ≤ 1 := pow_le_one₀ (le_of_lt hp) (le_of_lt hlt)
  have h3 : ((eqLam a)^2/16)^2 = (eqLam a)^4/256 := by ring
  rw [h3] at h1'
  linarith

lemma germR_le_lam {a : ℝ} (h0 : 0 < a) (h1 : a < 1) : germR a ≤ eqLam a := by
  have h := germR_le_lam_sq a
  have hp := eqLam_pos h0 h1
  have hlt := eqLam_lt_one h0 h1
  nlinarith

end GermRFacts

end LamFacts

end Work.EQ
