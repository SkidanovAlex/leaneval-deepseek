import Mathlib
import Submission.Work.EQ.GermSetup
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.WOf_lipschitz
import Submission.Work.EQ.WOf_bound

/-!
# Lipschitz continuity of the non-linear part `GnlOf` of the germ residual

`GnlOf a ρ u` is the non-linear part of the residual of the cleared germ equation
(`Submission/Work/EQ/GermSetup.lean`), a polynomial expression in
`W = WOf ρ u = β²/(1+S)`, `A₁ = ρu - λ⁻³ρ(u/λ)`, `A₂ = λ³ρ(λu) - ρu` and
`A₃ = λ³ρ(λu) - λ⁻³ρ(u/λ)`, with coefficients involving `a`, `u`, `κ = λ⁻¹ - λ`.

Here we prove that `GnlOf a · u` is Lipschitz in `ρ` on the unit ball of the sup-norm on the
disc of radius `germR a`, with the explicit constant `λ² r² · gLipK a`:

`‖Gnl(ρ₁)u - Gnl(ρ₂)u‖ ≤ M · (λ² r² · gLipK a)` whenever `‖ρᵢ‖ ≤ 1` and `‖ρ₁-ρ₂‖ ≤ M`
on `‖z‖ ≤ r = germR a` and `‖u‖ ≤ λ r`.

Every term of `GnlOf` carries an explicit factor `u²` (or higher), except `-aκW`, whose
`ρ`-dependence enters only through `β = -1 + u²ρu`; hence all differences gain a factor
`(λ r)²`.  The individual estimates are

* `‖W₁-W₂‖ ≤ 5 λ²r² M`, `‖W‖ ≤ 2`;
* `‖A₁(ρ₁)-A₁(ρ₂)‖ ≤ (1+λ⁻³)M`, `‖A₂(ρ₁)-A₂(ρ₂)‖ ≤ (1+λ³)M`, `‖A₃(ρ₁)-A₃(ρ₂)‖ ≤ (1+λ⁻³)M`;
* `‖A₁‖ ≤ 1+λ⁻³`, `‖A₂‖ ≤ 1+λ³`, `‖A₃‖ ≤ 1+λ⁻³`, `‖κρu‖ ≤ κ`,

and the five summands' differences are dominated by `λ²r²M` times the five summands of
`gLipK a`.  The point `u/λ` (and `λu`) lie in the disc of radius `r` because `‖u‖ ≤ λ r`,
`λ < 1` and `λ⁻¹λ = 1`.
-/

namespace Work.EQ

open Complex Metric Filter

noncomputable section

variable {a : ℝ}

private lemma norm_lamC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ‖lamC a‖ = eqLam a := by
  rw [lamC, Complex.norm_of_nonneg (le_of_lt (eqLam_pos ha0 ha1))]

private lemma norm_lamC_cube {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ‖(lamC a) ^ 3‖ = (eqLam a) ^ 3 := by
  rw [norm_pow, norm_lamC ha0 ha1]

private lemma norm_inv_lamC_cube {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ‖((lamC a) ^ 3)⁻¹‖ = ((eqLam a) ^ 3)⁻¹ := by
  rw [norm_inv, norm_lamC_cube ha0 ha1]

/-- `‖u‖ ≤ germR a` follows from `‖u‖ ≤ eqLam a * germR a` because `eqLam a ≤ 1`. -/
private lemma u_norm_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ}
    (hu : ‖u‖ ≤ eqLam a * germR a) : ‖u‖ ≤ germR a := by
  have hle : eqLam a * germR a ≤ germR a := by
    have h1 := eqLam_le_one ha0
    have h2 := le_of_lt (germR_pos ha0 ha1)
    nlinarith
  linarith

/-- `‖lamC a * u‖ ≤ germR a` for `‖u‖ ≤ eqLam a * germR a`. -/
private lemma lam_mul_u_norm_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ}
    (hu : ‖u‖ ≤ eqLam a * germR a) : ‖lamC a * u‖ ≤ germR a := by
  rw [norm_mul, norm_lamC ha0 ha1]
  have hp := eqLam_pos ha0 ha1
  have hl := eqLam_lt_one ha0 ha1
  have hr : 0 ≤ germR a := le_of_lt (germR_pos ha0 ha1)
  have h3 : eqLam a * eqLam a ≤ 1 := by nlinarith
  calc eqLam a * ‖u‖ ≤ eqLam a * (eqLam a * germR a) :=
        mul_le_mul_of_nonneg_left hu (le_of_lt hp)
    _ = (eqLam a * eqLam a) * germR a := by ring
    _ ≤ 1 * germR a := mul_le_mul_of_nonneg_right h3 hr
    _ = germR a := one_mul _

/-- `‖u / lamC a‖ ≤ germR a` for `‖u‖ ≤ eqLam a * germR a`. -/
private lemma div_lam_u_norm_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {u : ℂ}
    (hu : ‖u‖ ≤ eqLam a * germR a) : ‖u / lamC a‖ ≤ germR a := by
  rw [norm_div, norm_lamC ha0 ha1]
  rw [div_le_iff₀ (eqLam_pos ha0 ha1)]
  have : ‖u‖ ≤ germR a * eqLam a := by rw [mul_comm]; exact hu
  linarith

/-- `M ≥ 0` is forced by the hypotheses of the Lipschitz estimate. -/
private lemma M_nonneg {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℂ → ℂ} {M : ℝ}
    (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M) : 0 ≤ M :=
  le_trans (norm_nonneg _) (hM 0 (by rw [norm_zero]; exact le_of_lt (germR_pos ha0 ha1)))

private lemma A1_lip {a : ℝ} {ρ₁ ρ₂ : ℂ → ℂ} {M : ℝ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A1Of a ρ₁ u - A1Of a ρ₂ u‖ ≤ (1 + ((eqLam a) ^ 3)⁻¹) * M := by
  have h1 := hM u (u_norm_le ha0 ha1 hu)
  have h2 := hM (u / lamC a) (div_lam_u_norm_le ha0 ha1 hu)
  have hnn : 0 ≤ ((eqLam a) ^ 3)⁻¹ := by have hp := eqLam_pos ha0 ha1; positivity
  have hsplit : A1Of a ρ₁ u - A1Of a ρ₂ u
      = (ρ₁ u - ρ₂ u) - ((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a)) := by
    simp only [A1Of]; ring
  rw [hsplit]
  calc ‖(ρ₁ u - ρ₂ u) - ((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a))‖
      ≤ ‖ρ₁ u - ρ₂ u‖ + ‖((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a))‖ :=
        norm_sub_le _ _
    _ = ‖ρ₁ u - ρ₂ u‖ + ((eqLam a) ^ 3)⁻¹ * ‖ρ₁ (u / lamC a) - ρ₂ (u / lamC a)‖ := by
        rw [norm_mul, norm_inv_lamC_cube ha0 ha1]
    _ ≤ M + ((eqLam a) ^ 3)⁻¹ * M := by
        have := mul_le_mul_of_nonneg_left h2 hnn
        linarith
    _ = (1 + ((eqLam a) ^ 3)⁻¹) * M := by ring

private lemma A2_lip {a : ℝ} {ρ₁ ρ₂ : ℂ → ℂ} {M : ℝ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A2Of a ρ₁ u - A2Of a ρ₂ u‖ ≤ (1 + (eqLam a) ^ 3) * M := by
  have h1 := hM u (u_norm_le ha0 ha1 hu)
  have h2 := hM (lamC a * u) (lam_mul_u_norm_le ha0 ha1 hu)
  have hnn : 0 ≤ (eqLam a) ^ 3 := by
    have hp := eqLam_pos ha0 ha1; positivity
  have hsplit : A2Of a ρ₁ u - A2Of a ρ₂ u
      = (lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u)) - (ρ₁ u - ρ₂ u) := by
    simp only [A2Of]; ring
  rw [hsplit]
  calc ‖(lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u)) - (ρ₁ u - ρ₂ u)‖
      ≤ ‖(lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u))‖ + ‖ρ₁ u - ρ₂ u‖ :=
        norm_sub_le _ _
    _ = (eqLam a) ^ 3 * ‖ρ₁ (lamC a * u) - ρ₂ (lamC a * u)‖ + ‖ρ₁ u - ρ₂ u‖ := by
        rw [norm_mul, norm_lamC_cube ha0 ha1]
    _ ≤ (eqLam a) ^ 3 * M + M := by
        have := mul_le_mul_of_nonneg_left h2 hnn
        linarith
    _ = (1 + (eqLam a) ^ 3) * M := by ring

private lemma A3_lip {a : ℝ} {ρ₁ ρ₂ : ℂ → ℂ} {M : ℝ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A3Of a ρ₁ u - A3Of a ρ₂ u‖ ≤ (1 + ((eqLam a) ^ 3)⁻¹) * M := by
  have h1 := hM u (u_norm_le ha0 ha1 hu)
  have h2 := hM (u / lamC a) (div_lam_u_norm_le ha0 ha1 hu)
  have h3 := hM (lamC a * u) (lam_mul_u_norm_le ha0 ha1 hu)
  have hnn1 : 0 ≤ (eqLam a) ^ 3 := by have hp := eqLam_pos ha0 ha1; positivity
  have hnn2 : 0 ≤ ((eqLam a) ^ 3)⁻¹ := by have hp := eqLam_pos ha0 ha1; positivity
  have hsplit : A3Of a ρ₁ u - A3Of a ρ₂ u
      = (lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u))
        - ((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a)) := by
    simp only [A3Of]; ring
  rw [hsplit]
  calc ‖(lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u))
        - ((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a))‖
      ≤ ‖(lamC a) ^ 3 * (ρ₁ (lamC a * u) - ρ₂ (lamC a * u))‖
        + ‖((lamC a) ^ 3)⁻¹ * (ρ₁ (u / lamC a) - ρ₂ (u / lamC a))‖ := norm_sub_le _ _
    _ = (eqLam a) ^ 3 * ‖ρ₁ (lamC a * u) - ρ₂ (lamC a * u)‖
        + ((eqLam a) ^ 3)⁻¹ * ‖ρ₁ (u / lamC a) - ρ₂ (u / lamC a)‖ := by
        rw [norm_mul, norm_mul, norm_lamC_cube ha0 ha1, norm_inv_lamC_cube ha0 ha1]
    _ ≤ (eqLam a) ^ 3 * M + ((eqLam a) ^ 3)⁻¹ * M := by
        have h4 := mul_le_mul_of_nonneg_left h3 hnn1
        have h5 := mul_le_mul_of_nonneg_left h2 hnn2
        linarith
    _ ≤ (1 + ((eqLam a) ^ 3)⁻¹) * M := by
        rw [add_mul, one_mul]
        have hp := eqLam_pos ha0 ha1
        have hl := eqLam_lt_one ha0 ha1
        have h6 : (eqLam a) ^ 3 ≤ 1 := pow_le_one₀ hp.le hl.le
        have hMnn := M_nonneg ha0 ha1 hM
        have h8 := mul_le_mul_of_nonneg_right h6 hMnn
        linarith

private lemma A1_norm {a : ℝ} {ρ : ℂ → ℂ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A1Of a ρ u‖ ≤ 1 + ((eqLam a) ^ 3)⁻¹ := by
  have h1 := hρ u (u_norm_le ha0 ha1 hu)
  have h2 := hρ (u / lamC a) (div_lam_u_norm_le ha0 ha1 hu)
  have hnn : 0 ≤ ((eqLam a) ^ 3)⁻¹ := by have hp := eqLam_pos ha0 ha1; positivity
  calc ‖A1Of a ρ u‖ = ‖ρ u - ((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)‖ := by rw [A1Of]
    _ ≤ ‖ρ u‖ + ‖((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)‖ := norm_sub_le _ _
    _ = ‖ρ u‖ + ((eqLam a) ^ 3)⁻¹ * ‖ρ (u / lamC a)‖ := by
        rw [norm_mul, norm_inv_lamC_cube ha0 ha1]
    _ ≤ 1 + ((eqLam a) ^ 3)⁻¹ * 1 := by
        have := mul_le_mul_of_nonneg_left h2 hnn
        linarith
    _ = 1 + ((eqLam a) ^ 3)⁻¹ := by ring

private lemma A2_norm {a : ℝ} {ρ : ℂ → ℂ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A2Of a ρ u‖ ≤ 1 + (eqLam a) ^ 3 := by
  have h1 := hρ u (u_norm_le ha0 ha1 hu)
  have h2 := hρ (lamC a * u) (lam_mul_u_norm_le ha0 ha1 hu)
  have hnn : 0 ≤ (eqLam a) ^ 3 := by have hp := eqLam_pos ha0 ha1; positivity
  calc ‖A2Of a ρ u‖ = ‖(lamC a) ^ 3 * ρ (lamC a * u) - ρ u‖ := by rw [A2Of]
    _ ≤ ‖(lamC a) ^ 3 * ρ (lamC a * u)‖ + ‖ρ u‖ := norm_sub_le _ _
    _ = (eqLam a) ^ 3 * ‖ρ (lamC a * u)‖ + ‖ρ u‖ := by
        rw [norm_mul, norm_lamC_cube ha0 ha1]
    _ ≤ (eqLam a) ^ 3 * 1 + 1 := by
        have := mul_le_mul_of_nonneg_left h2 hnn
        linarith
    _ = 1 + (eqLam a) ^ 3 := by ring

private lemma A3_norm {a : ℝ} {ρ : ℂ → ℂ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖A3Of a ρ u‖ ≤ 1 + ((eqLam a) ^ 3)⁻¹ := by
  have hp := eqLam_pos ha0 ha1
  have hl := eqLam_lt_one ha0 ha1
  have h1 := hρ u (u_norm_le ha0 ha1 hu)
  have h2 := hρ (u / lamC a) (div_lam_u_norm_le ha0 ha1 hu)
  have h3 := hρ (lamC a * u) (lam_mul_u_norm_le ha0 ha1 hu)
  have hnn : 0 ≤ ((eqLam a) ^ 3)⁻¹ := by positivity
  have hnn3 : 0 ≤ (eqLam a) ^ 3 := by positivity
  have h6 : (eqLam a) ^ 3 ≤ 1 := pow_le_one₀ hp.le hl.le
  calc ‖A3Of a ρ u‖ = ‖(lamC a) ^ 3 * ρ (lamC a * u) - ((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)‖ := by
        rw [A3Of]
    _ ≤ ‖(lamC a) ^ 3 * ρ (lamC a * u)‖ + ‖((lamC a) ^ 3)⁻¹ * ρ (u / lamC a)‖ := norm_sub_le _ _
    _ = (eqLam a) ^ 3 * ‖ρ (lamC a * u)‖ + ((eqLam a) ^ 3)⁻¹ * ‖ρ (u / lamC a)‖ := by
        rw [norm_mul, norm_mul, norm_lamC_cube ha0 ha1, norm_inv_lamC_cube ha0 ha1]
    _ ≤ (eqLam a) ^ 3 * 1 + ((eqLam a) ^ 3)⁻¹ * 1 := by
        have h4 := mul_le_mul_of_nonneg_left h3 hnn3
        have h5 := mul_le_mul_of_nonneg_left h2 hnn
        linarith
    _ ≤ 1 + ((eqLam a) ^ 3)⁻¹ := by linarith

/-- Product Lipschitz estimate: `‖x₁y₁ - x₂y₂‖ ≤ b₁d₂ + d₁b₂` from the four marginal bounds. -/
private lemma mul_lip {x₁ x₂ y₁ y₂ : ℂ} {b₁ b₂ d₁ d₂ : ℝ}
    (hx : ‖x₁ - x₂‖ ≤ b₁) (hy : ‖y₁‖ ≤ d₂) (hx' : ‖x₂‖ ≤ d₁) (hy' : ‖y₁ - y₂‖ ≤ b₂)
    (hb₁ : 0 ≤ b₁) (hd₁ : 0 ≤ d₁) :
    ‖x₁ * y₁ - x₂ * y₂‖ ≤ b₁ * d₂ + d₁ * b₂ := by
  have hsplit : x₁ * y₁ - x₂ * y₂ = (x₁ - x₂) * y₁ + x₂ * (y₁ - y₂) := by ring
  rw [hsplit]
  calc ‖(x₁ - x₂) * y₁ + x₂ * (y₁ - y₂)‖
      ≤ ‖(x₁ - x₂) * y₁‖ + ‖x₂ * (y₁ - y₂)‖ := norm_add_le _ _
    _ = ‖x₁ - x₂‖ * ‖y₁‖ + ‖x₂‖ * ‖y₁ - y₂‖ := by rw [norm_mul, norm_mul]
    _ ≤ b₁ * d₂ + d₁ * b₂ :=
        add_le_add (mul_le_mul hx hy (norm_nonneg _) hb₁) (mul_le_mul hx' hy' (norm_nonneg _) hd₁)

private lemma add_lip {x₁ x₂ y₁ y₂ : ℂ} {b₁ b₂ : ℝ}
    (hx : ‖x₁ - x₂‖ ≤ b₁) (hy : ‖y₁ - y₂‖ ≤ b₂) :
    ‖(x₁ + y₁) - (x₂ + y₂)‖ ≤ b₁ + b₂ := by
  have hsplit : (x₁ + y₁) - (x₂ + y₂) = (x₁ - x₂) + (y₁ - y₂) := by ring
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add hx hy)

private lemma neg_lip {x₁ x₂ : ℂ} {b : ℝ} (hx : ‖x₁ - x₂‖ ≤ b) : ‖(-x₁) - (-x₂)‖ ≤ b := by
  have hsplit : (-x₁) - (-x₂) = -(x₁ - x₂) := by ring
  rw [hsplit, norm_neg]
  exact hx

private lemma mul_const_lip {c x y : ℂ} {b : ℝ} (h : ‖x - y‖ ≤ b) :
    ‖c * x - c * y‖ ≤ ‖c‖ * b := by
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg c)

/-- Norm bound for `K_ρ = -A₃(ρ) + κρu`. -/
private lemma K_norm {a : ℝ} {ρ : ℂ → ℂ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ∀ z, ‖z‖ ≤ germR a → ‖ρ z‖ ≤ 1) (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖-(A3Of a ρ u) + kapC a * ρ u‖
      ≤ 1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a) := by
  have hkap : 0 ≤ (eqLam a)⁻¹ - eqLam a := by
    have hp := eqLam_pos ha0 ha1
    have hl := eqLam_lt_one ha0 ha1
    have h1 : 1 ≤ (eqLam a)⁻¹ := (one_le_inv₀ hp).mpr (le_of_lt hl)
    linarith
  have hkapC : ‖kapC a‖ = (eqLam a)⁻¹ - eqLam a := by
    rw [kapC, Complex.norm_of_nonneg hkap]
  have hA3 := A3_norm ha0 ha1 hρ hu
  have hr := hρ u (u_norm_le ha0 ha1 hu)
  have haux := norm_add_le (-(A3Of a ρ u)) (kapC a * ρ u)
  rw [norm_neg, norm_mul, hkapC] at haux
  calc ‖-(A3Of a ρ u) + kapC a * ρ u‖
      ≤ ‖A3Of a ρ u‖ + ((eqLam a)⁻¹ - eqLam a) * ‖ρ u‖ := haux
    _ ≤ (1 + ((eqLam a) ^ 3)⁻¹) + ((eqLam a)⁻¹ - eqLam a) * 1 :=
        add_le_add hA3 (mul_le_mul_of_nonneg_left hr hkap)
    _ = 1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a) := by ring

/-- Difference bound for `K_ρ = -A₃(ρ) + κρu`. -/
private lemma K_lip {a : ℝ} {ρ₁ ρ₂ : ℂ → ℂ} {M : ℝ} {u : ℂ} (ha0 : 0 < a) (ha1 : a < 1)
    (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖(-(A3Of a ρ₁ u) + kapC a * ρ₁ u) - (-(A3Of a ρ₂ u) + kapC a * ρ₂ u)‖
      ≤ (1 + ((eqLam a) ^ 3)⁻¹) * M + ((eqLam a)⁻¹ - eqLam a) * M := by
  have hkap : 0 ≤ (eqLam a)⁻¹ - eqLam a := by
    have hp := eqLam_pos ha0 ha1
    have hl := eqLam_lt_one ha0 ha1
    have h1 : 1 ≤ (eqLam a)⁻¹ := (one_le_inv₀ hp).mpr (le_of_lt hl)
    linarith
  have hkapC : ‖kapC a‖ = (eqLam a)⁻¹ - eqLam a := by
    rw [kapC, Complex.norm_of_nonneg hkap]
  have hA3 := A3_lip ha0 ha1 hM hu
  have hr := hM u (u_norm_le ha0 ha1 hu)
  have h2 := mul_const_lip (c := kapC a) hr
  have h1 := add_lip (neg_lip hA3) h2
  rw [hkapC] at h1
  exact h1

/-- **Lipschitz continuity of the non-linear part of the germ residual.**  With
`λ = eqLam a`, `r = germR a`, if `‖ρᵢ‖ ≤ 1` and `‖ρ₁ - ρ₂‖ ≤ M` on `‖z‖ ≤ r`, then for
`‖u‖ ≤ λ r` one has `‖GnlOf a ρ₁ u - GnlOf a ρ₂ u‖ ≤ M · (λ² r² · gLipK a)`. -/
theorem Gnl_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℂ → ℂ}
    (h₁ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z‖ ≤ 1) (h₂ : ∀ z, ‖z‖ ≤ germR a → ‖ρ₂ z‖ ≤ 1)
    {M : ℝ} (hM : ∀ z, ‖z‖ ≤ germR a → ‖ρ₁ z - ρ₂ z‖ ≤ M)
    {u : ℂ} (hu : ‖u‖ ≤ eqLam a * germR a) :
    ‖GnlOf a ρ₁ u - GnlOf a ρ₂ u‖ ≤ M * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a) := by
  have hp : 0 < eqLam a := eqLam_pos ha0 ha1
  have hl : eqLam a < 1 := eqLam_lt_one ha0 ha1
  have hMnn : 0 ≤ M := M_nonneg ha0 ha1 hM
  have hnninv : 0 ≤ ((eqLam a) ^ 3)⁻¹ := by positivity
  have hkap : 0 ≤ (eqLam a)⁻¹ - eqLam a := by
    have h1 : 1 ≤ (eqLam a)⁻¹ := (one_le_inv₀ hp).mpr (le_of_lt hl)
    linarith
  set om : ℝ := (eqLam a) ^ 2 * (germR a) ^ 2 with hom_def
  have hom : 0 ≤ om := by rw [hom_def]; positivity
  have homle : om ≤ 1 / 256 := by rw [hom_def]; exact lam_sq_mul_germR_sq_le ha0 ha1
  have hu2 : ‖u‖ ^ 2 ≤ om := by
    rw [hom_def]
    have h : ‖u‖ ^ 2 ≤ (eqLam a * germR a) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    rw [mul_pow] at h
    exact h
  have hu4 : ‖u‖ ^ 4 ≤ om * om := by
    have h : (‖u‖ ^ 2) ^ 2 ≤ om ^ 2 := pow_le_pow_left₀ (by positivity) hu2 2
    have h2 : ‖u‖ ^ 4 = (‖u‖ ^ 2) ^ 2 := by ring
    rw [h2, ← pow_two]
    exact h
  set T1 : ℂ := -((a : ℂ) * kapC a) * (WOf ρ₁ u - WOf ρ₂ u) with hT1def
  set T2 : ℂ := u ^ 2 * (A1Of a ρ₁ u * A2Of a ρ₁ u - A1Of a ρ₂ u * A2Of a ρ₂ u) with hT2def
  set T3 : ℂ := (a : ℂ) * u ^ 2 * (ρ₁ u * A3Of a ρ₁ u - ρ₂ u * A3Of a ρ₂ u) with hT3def
  set T4 : ℂ := (a : ℂ) * u ^ 2 * (WOf ρ₁ u * (-(A3Of a ρ₁ u) + kapC a * ρ₁ u)
      - WOf ρ₂ u * (-(A3Of a ρ₂ u) + kapC a * ρ₂ u)) with hT4def
  set T5 : ℂ := (a : ℂ) * u ^ 4 * (WOf ρ₁ u * ρ₁ u * A3Of a ρ₁ u
      - WOf ρ₂ u * ρ₂ u * A3Of a ρ₂ u) with hT5def
  have hsub : GnlOf a ρ₁ u - GnlOf a ρ₂ u = T1 + T2 + T3 + T4 + T5 := by
    rw [hT1def, hT2def, hT3def, hT4def, hT5def]
    simp only [GnlOf]
    ring
  have hW' : ‖WOf ρ₁ u - WOf ρ₂ u‖ ≤ 5 * om * M := by
    rw [hom_def]
    exact WOf_lipschitz ha0 ha1 h₁ h₂ hM hu
  have hW2 : ‖WOf ρ₂ u‖ ≤ 2 := WOf_bound ha0 ha1 h₂ (u_norm_le ha0 ha1 hu)
  -- Term 1
  have hT1b : ‖T1‖ ≤ 12 * a * ((eqLam a)⁻¹ - eqLam a) * om * M := by
    rw [hT1def]
    have hk : ‖(a : ℂ) * kapC a‖ = a * ((eqLam a)⁻¹ - eqLam a) := by
      rw [norm_mul, Complex.norm_of_nonneg (le_of_lt ha0), kapC, Complex.norm_of_nonneg hkap]
    rw [norm_mul, norm_neg, hk]
    have hcoef : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) := mul_nonneg (le_of_lt ha0) hkap
    calc a * ((eqLam a)⁻¹ - eqLam a) * ‖WOf ρ₁ u - WOf ρ₂ u‖
        ≤ a * ((eqLam a)⁻¹ - eqLam a) * (5 * om * M) := mul_le_mul_of_nonneg_left hW' hcoef
      _ = 5 * (a * ((eqLam a)⁻¹ - eqLam a)) * om * M := by ring
      _ ≤ 12 * a * ((eqLam a)⁻¹ - eqLam a) * om * M := by
          have hc : 0 ≤ a * ((eqLam a)⁻¹ - eqLam a) * om * M :=
            mul_nonneg (mul_nonneg hcoef hom) hMnn
          nlinarith
  -- Term 2
  have hT2b : ‖T2‖ ≤ 2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3) * om * M := by
    rw [hT2def]
    have hA1 := A1_lip ha0 ha1 hM hu
    have hA2 := A2_lip ha0 ha1 hM hu
    have hn1 := A1_norm ha0 ha1 h₂ hu
    have hn2 := A2_norm ha0 ha1 h₁ hu
    have hb1 : 0 ≤ (1 + ((eqLam a) ^ 3)⁻¹) * M := mul_nonneg (by positivity) hMnn
    have hd1 : 0 ≤ 1 + ((eqLam a) ^ 3)⁻¹ := by positivity
    have hX := mul_lip hA1 hn2 hn1 hA2 hb1 hd1
    have hX' : ‖A1Of a ρ₁ u * A2Of a ρ₁ u - A1Of a ρ₂ u * A2Of a ρ₂ u‖
        ≤ 2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3) * M := by
      refine le_trans hX (le_of_eq ?_)
      ring
    rw [norm_mul, norm_pow]
    calc ‖u‖ ^ 2 * ‖A1Of a ρ₁ u * A2Of a ρ₁ u - A1Of a ρ₂ u * A2Of a ρ₂ u‖
        ≤ om * (2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3) * M) :=
          mul_le_mul hu2 hX' (norm_nonneg _) hom
      _ = 2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3) * om * M := by ring
  -- Term 3
  have hT3b : ‖T3‖ ≤ 2 * a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M := by
    rw [hT3def]
    have hr1 := hM u (u_norm_le ha0 ha1 hu)
    have hr2 := h₂ u (u_norm_le ha0 ha1 hu)
    have hA3 := A3_lip ha0 ha1 hM hu
    have hn3 := A3_norm ha0 ha1 h₁ hu
    have hX := mul_lip hr1 hn3 hr2 hA3 hMnn (by norm_num)
    have hX' : ‖ρ₁ u * A3Of a ρ₁ u - ρ₂ u * A3Of a ρ₂ u‖
        ≤ 2 * (1 + ((eqLam a) ^ 3)⁻¹) * M := by
      refine le_trans hX (le_of_eq ?_)
      ring
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt ha0)]
    calc a * ‖u‖ ^ 2 * ‖ρ₁ u * A3Of a ρ₁ u - ρ₂ u * A3Of a ρ₂ u‖
        ≤ a * om * (2 * (1 + ((eqLam a) ^ 3)⁻¹) * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu2 (le_of_lt ha0)) hX' (norm_nonneg _)
            (mul_nonneg (le_of_lt ha0) hom)
      _ = 2 * a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M := by ring
  -- Term 4
  have hT4b : ‖T4‖ ≤ 4 * a * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * om * M := by
    rw [hT4def]
    have hK1 := K_norm ha0 ha1 h₁ hu
    have hK12 := K_lip ha0 ha1 hM hu
    have hb1 : 0 ≤ 5 * om * M := mul_nonneg (mul_nonneg (by norm_num) hom) hMnn
    have hd1 : (0 : ℝ) ≤ 2 := by norm_num
    have hX := mul_lip hW' hK1 hW2 hK12 hb1 hd1
    have hQ : 0 ≤ 1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a) := by linarith
    have hMQ : 0 ≤ M * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) := mul_nonneg hMnn hQ
    have h5 : 5 * om + 2 ≤ 4 := by linarith
    have hX' : ‖WOf ρ₁ u * (-(A3Of a ρ₁ u) + kapC a * ρ₁ u)
        - WOf ρ₂ u * (-(A3Of a ρ₂ u) + kapC a * ρ₂ u)‖
        ≤ 4 * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * M := by
      refine le_trans hX ?_
      calc (5 * om * M) * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a))
            + 2 * ((1 + ((eqLam a) ^ 3)⁻¹) * M + ((eqLam a)⁻¹ - eqLam a) * M)
          = M * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * (5 * om + 2) := by ring
        _ ≤ M * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * 4 :=
            mul_le_mul_of_nonneg_left h5 hMQ
        _ = 4 * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * M := by ring
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt ha0)]
    calc a * ‖u‖ ^ 2 * ‖WOf ρ₁ u * (-(A3Of a ρ₁ u) + kapC a * ρ₁ u)
          - WOf ρ₂ u * (-(A3Of a ρ₂ u) + kapC a * ρ₂ u)‖
        ≤ a * om * (4 * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu2 (le_of_lt ha0)) hX' (norm_nonneg _)
            (mul_nonneg (le_of_lt ha0) hom)
      _ = 4 * a * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * om * M := by ring
  -- Term 5
  have hT5b : ‖T5‖ ≤ a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M := by
    rw [hT5def]
    have hr1n := h₁ u (u_norm_le ha0 ha1 hu)
    have hr2n := h₂ u (u_norm_le ha0 ha1 hu)
    have hr1l := hM u (u_norm_le ha0 ha1 hu)
    have hA3n := A3_norm ha0 ha1 h₁ hu
    have hA3l := A3_lip ha0 ha1 hM hu
    have hb1 : 0 ≤ 5 * om * M := mul_nonneg (mul_nonneg (by norm_num) hom) hMnn
    have hd1 : (0 : ℝ) ≤ 2 := by norm_num
    have hstep1 : ‖WOf ρ₁ u * ρ₁ u - WOf ρ₂ u * ρ₂ u‖ ≤ M * (5 * om + 2) := by
      have hX := mul_lip hW' hr1n hW2 hr1l hb1 hd1
      refine le_trans hX (le_of_eq ?_)
      ring
    have hWρ2 : ‖WOf ρ₂ u * ρ₂ u‖ ≤ 2 := by
      have h := mul_le_mul hW2 hr2n (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      simpa using h
    have hb2 : 0 ≤ M * (5 * om + 2) := mul_nonneg hMnn (by linarith)
    have hd2 : (0 : ℝ) ≤ 2 := by norm_num
    have hstep2 : ‖WOf ρ₁ u * ρ₁ u * A3Of a ρ₁ u - WOf ρ₂ u * ρ₂ u * A3Of a ρ₂ u‖
        ≤ M * (1 + ((eqLam a) ^ 3)⁻¹) * (5 * om + 4) := by
      have hX := mul_lip hstep1 hA3n hWρ2 hA3l hb2 hd2
      refine le_trans hX (le_of_eq ?_)
      ring
    have hom5 : om * (5 * om + 4) ≤ 1 := by
      have h1 : 5 * om + 4 ≤ 5 * (1 / 256) + 4 := by linarith
      have h2 : om * (5 * om + 4) ≤ (1 / 256) * (5 * (1 / 256) + 4) :=
        mul_le_mul homle h1 (by linarith) (by norm_num)
      linarith
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt ha0)]
    calc a * ‖u‖ ^ 4 * ‖WOf ρ₁ u * ρ₁ u * A3Of a ρ₁ u - WOf ρ₂ u * ρ₂ u * A3Of a ρ₂ u‖
        ≤ a * (om * om) * (M * (1 + ((eqLam a) ^ 3)⁻¹) * (5 * om + 4)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu4 (le_of_lt ha0)) hstep2 (norm_nonneg _)
            (mul_nonneg (le_of_lt ha0) (mul_nonneg hom hom))
      _ = a * om * M * (1 + ((eqLam a) ^ 3)⁻¹) * (om * (5 * om + 4)) := by ring
      _ ≤ a * om * M * (1 + ((eqLam a) ^ 3)⁻¹) * 1 :=
          mul_le_mul_of_nonneg_left hom5 (by positivity)
      _ = a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M := by ring
  -- Assembly
  have hsum : ‖T1 + T2 + T3 + T4 + T5‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ := by
    have h1 := norm_add_le T1 T2
    have h2 := norm_add_le (T1 + T2) T3
    have h3 := norm_add_le (T1 + T2 + T3) T4
    have h4 := norm_add_le (T1 + T2 + T3 + T4) T5
    linarith
  rw [hsub]
  calc ‖T1 + T2 + T3 + T4 + T5‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ := hsum
    _ ≤ 12 * a * ((eqLam a)⁻¹ - eqLam a) * om * M
        + 2 * (1 + ((eqLam a) ^ 3)⁻¹) * (1 + (eqLam a) ^ 3) * om * M
        + 2 * a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M
        + 4 * a * (1 + ((eqLam a) ^ 3)⁻¹ + ((eqLam a)⁻¹ - eqLam a)) * om * M
        + a * (1 + ((eqLam a) ^ 3)⁻¹) * om * M := by linarith [hT1b, hT2b, hT3b, hT4b, hT5b]
    _ = M * ((eqLam a) ^ 2 * (germR a) ^ 2 * gLipK a) := by
        rw [hom_def, gLipK]; ring

end

end Work.EQ
