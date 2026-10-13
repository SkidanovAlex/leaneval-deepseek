import Mathlib
import Submission.Work.WilkiesH.Interp.V2Defs

/-!
# Area I (`v2` route) — the explicit numerical parameters

This file fixes the *explicit* choices of the parameters `b, d, ρ, Q, ε` used in
`Work.WilkiesH.Interp.exists_params_v2`.

For a fixed dimension `μ`:

* `ρ = 1/K` with `K = 2μ+4` — a constant depending only on `μ`;
* `b = E·(g+1)^A·Lg^B` where `Lg = ⌈log H⌉ + 1`, and `A, B, E` are (large) constants
  depending only on `μ`;
* `d` is the `(μ+1)`-st root of `(μ+1)! · (8g+9) · (b+1)^μ`, rounded up;
* `Q = 4·N₁·⌈exp (b·log K / λ)⌉ + 2` where `N₁ = monoCount (μ+1) d` and
  `λ = N₁ / monoCount μ b - 1`;
* `ε = liou μ d Q g H / (4·N₁·Q·d·(μ+1))`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesConjecture

/-! ## Definitions -/

/-- `K = 2μ + 4`: the reciprocal of the box radius. -/
def KK (μ : ℕ) : ℕ := 2 * μ + 4

/-- The box radius `ρ = 1/K`. -/
def rhoV (μ : ℕ) : ℝ := ((KK μ : ℝ))⁻¹

/-- `⌈log H⌉ + 1`, a natural upper bound for `log H` when `H ≥ 1`. -/
def lgNat (H : ℕ) : ℕ := Nat.ceil (Real.log (H : ℝ)) + 1

/-- Exponent of `g+1` in `b`. -/
def AA (μ : ℕ) : ℕ := 100 * (μ + 1) ^ 3

/-- Exponent of `⌈log H⌉+1` in `b`. -/
def BB (μ : ℕ) : ℕ := 100 * (μ + 1) ^ 3

/-- The multiplicative constant in `b`. -/
def EE (μ : ℕ) : ℕ := (μ + 2) ^ (40 * (μ + 1) ^ 2)

/-- The flatness order `b`. -/
def bV (μ g H : ℕ) : ℕ := EE μ * (g + 1) ^ (AA μ) * (lgNat H) ^ (BB μ)

/-- The quantity whose `(μ+1)`-st root is (roughly) the degree `d`. -/
def RR (μ g b : ℕ) : ℕ := (μ + 1).factorial * (8 * g + 9) * (b + 1) ^ μ

/-- The degree `d`, chosen so that `monoCount (μ+1) d ≥ (8g+9)·monoCount μ b`. -/
def dV (μ g b : ℕ) : ℕ := Nat.ceil (((RR μ g b : ℝ)) ^ (1 / ((μ : ℝ) + 1))) + 1

/-- `N₁ = monoCount (μ+1) d`, the number of columns of the interpolation system. -/
def N1V (μ g H : ℕ) : ℕ := Work.WilkiesH.monoCount (μ + 1) (dV μ g (bV μ g H))

/-- `m = monoCount μ b`, the number of rows of the interpolation system. -/
def mV (μ g H : ℕ) : ℕ := Work.WilkiesH.monoCount μ (bV μ g H)

/-- `λ = N₁ / m - 1`, the "slack" in the Siegel cardinality condition. -/
def lamV (μ g H : ℕ) : ℕ := N1V μ g H / mV μ g H - 1

/-- The coefficient bound `Q`. -/
def QV (μ g H : ℕ) : ℕ :=
  4 * N1V μ g H *
      Nat.ceil (Real.exp ((bV μ g H : ℝ) * Real.log (KK μ) / (((lamV μ g H : ℕ) : ℝ)))) +
    2

/-- The neighbourhood width `ε`, chosen so that the Lipschitz term is exactly `liou/4`. -/
def epsV (μ g H : ℕ) : ℝ :=
  liou μ (dV μ g (bV μ g H)) (QV μ g H) g H /
    (4 * (N1V μ g H : ℝ) * (QV μ g H : ℝ) * (dV μ g (bV μ g H) : ℝ) * ((μ : ℝ) + 1))

/-- Exponent of `1+g` in the polynomial `q`. -/
def Ec (μ : ℕ) : ℕ := 1000 * (μ + 1) ^ 4

/-- Exponent of `1+log H` in the polynomial `q`. -/
def Fc (μ : ℕ) : ℕ := 1000 * (μ + 1) ^ 4

/-- The constant coefficient of the polynomial `q`. -/
def CCc (μ : ℕ) : ℕ := (μ + 2) ^ (100 * (μ + 1) ^ 2)

/-- The constant of the master inequality. -/
noncomputable def CM (μ : ℕ) : ℝ := 10 * ((μ : ℝ) + 2) ^ 2 + 100

/-- The polynomial `q` dominating `b`, `d·⌈1/ρ⌉^μ` and `log (1/ε)`. -/
def qPoly (μ : ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C ((CCc μ : ℝ)) * (1 + MvPolynomial.X 0) *
    (1 + MvPolynomial.X 1) ^ (Ec μ) * (1 + MvPolynomial.X 2) ^ (Fc μ)

/-! ## Elementary properties of the parameters -/

lemma KK_pos (μ : ℕ) : 0 < KK μ := by simp [KK]

lemma two_le_KK (μ : ℕ) : 2 ≤ KK μ := by simp [KK]

lemma one_lt_KK (μ : ℕ) : 1 < KK μ := by have := two_le_KK μ; omega

lemma rhoV_pos (μ : ℕ) : 0 < rhoV μ := by
  rw [rhoV]
  exact inv_pos.mpr (Nat.cast_pos.mpr (KK_pos μ))

lemma rhoV_eq (μ : ℕ) : rhoV μ = 1 / (KK μ : ℝ) := by
  rw [rhoV, one_div]

lemma sqrt_mu_mul_rhoV_le_one (μ : ℕ) : Real.sqrt (μ : ℝ) * rhoV μ ≤ 1 := by
  have hK : 0 < (KK μ : ℝ) := Nat.cast_pos.mpr (KK_pos μ)
  have h1 : Real.sqrt (μ : ℝ) ≤ (KK μ : ℝ) := by
    have hμ : Real.sqrt (μ : ℝ) ≤ (μ : ℝ) + 1 := by
      rcases Nat.eq_zero_or_pos μ with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ μ := by exact_mod_cast h
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg μ), Real.sqrt_nonneg (μ : ℝ)]
    have h2 : (μ : ℝ) + 1 ≤ (KK μ : ℝ) := by
      simp only [KK]
      push_cast
      linarith
    linarith
  rw [rhoV, inv_eq_one_div, ← div_eq_mul_one_div]
  exact (div_le_one hK).mpr h1

lemma lgNat_pos (H : ℕ) : 1 ≤ lgNat H := by simp [lgNat]

lemma log_le_lgNat (H : ℕ) : Real.log (H : ℝ) ≤ (lgNat H : ℝ) := by
  have := Nat.le_ceil (Real.log (H : ℝ))
  simp only [lgNat]
  push_cast
  linarith

/-- `log H ≥ 0` for natural `H`. -/
lemma log_nat_nonneg (H : ℕ) : 0 ≤ Real.log (H : ℝ) := by
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

lemma lgNat_le (H : ℕ) : (lgNat H : ℝ) ≤ Real.log (H : ℝ) + 2 := by
  have hlt := Nat.ceil_lt_add_one (log_nat_nonneg H)
  have h2 : (lgNat H : ℝ) = (Nat.ceil (Real.log (H : ℝ)) : ℝ) + 1 := by
    simp only [lgNat]
    push_cast
    ring
  rw [h2]; linarith

lemma one_le_bV (μ g H : ℕ) : 1 ≤ bV μ g H := by
  simp only [bV]
  have h1 : 1 ≤ EE μ := by
    simp only [EE]
    exact Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (g + 1) ^ (AA μ) := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (lgNat H) ^ (BB μ) := Nat.one_le_pow _ _ (lgNat_pos H)
  calc 1 = 1 * 1 * 1 := by ring
    _ ≤ EE μ * (g + 1) ^ (AA μ) * (lgNat H) ^ (BB μ) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

lemma one_le_dV (μ g b : ℕ) : 1 ≤ dV μ g b := by
  simp only [dV]
  omega

lemma one_le_N1V (μ g H : ℕ) : 1 ≤ N1V μ g H := by
  simp only [N1V]
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩

lemma one_le_mV (μ g H : ℕ) : 1 ≤ mV μ g H := by
  simp only [mV]
  exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩

lemma one_le_QV (μ g H : ℕ) : 1 ≤ QV μ g H := by
  simp only [QV]
  omega

/-! ## Abbreviations for the parameter values at a point `(μ,g,H)` -/

def bX (μ g H : ℕ) : ℕ := bV μ g H
def dX (μ g H : ℕ) : ℕ := dV μ g (bV μ g H)
def N1X (μ g H : ℕ) : ℕ := N1V μ g H
def mX (μ g H : ℕ) : ℕ := mV μ g H
def QX (μ g H : ℕ) : ℕ := QV μ g H
def lamX (μ g H : ℕ) : ℕ := lamV μ g H

/-- `⌈ρ^(-b)⌉`, the factor in the Siegel cardinality condition. -/
def rpbX (μ g H : ℕ) : ℕ := Nat.ceil ((rhoV μ) ^ (-(bV μ g H : ℤ)))

/-- `K = 2μ+4` as a real number. -/
def Kr (μ : ℕ) : ℝ := ((KK μ : ℕ) : ℝ)

/-- `⌈log H⌉ + 1` as a real number. -/
def Lgr (H : ℕ) : ℝ := (lgNat H : ℝ)

/-- The ceiling factor appearing in `QV`. -/
def ceilQV (μ g H : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((bV μ g H : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℝ))))

/-- `QV` in terms of `ceilQV`. -/
lemma QV_eq_four (μ g H : ℕ) : QV μ g H = 4 * N1V μ g H * ceilQV μ g H + 2 := rfl

lemma le_ceilQV (μ g H : ℕ) :
    Real.exp ((bV μ g H : ℝ) * Real.log (Kr μ) / ((lamV μ g H : ℝ))) ≤ ((ceilQV μ g H : ℕ) : ℝ) := by
  simp only [ceilQV]
  exact Nat.le_ceil _

/-- Evaluation of `qPoly` at an arbitrary point. -/
lemma qPoly_eval (μ : ℕ) (v : Fin 3 → ℝ) :
    MvPolynomial.eval v (qPoly μ) =
      (CCc μ : ℝ) * (1 + v 0) * (1 + v 1) ^ (Ec μ) * (1 + v 2) ^ (Fc μ) := by
  simp only [qPoly, MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_C, map_one]

/-- The first (Taylor) term of `above` at the parameters of the `v2` construction. -/
noncomputable def tayV (μ g H : ℕ) : ℝ :=
  Real.sqrt (N1V μ g H : ℝ) * (rhoV μ) ^ (bV μ g H) *
    (∑ j ∈ Finset.range (bV μ g H + 1),
      ((Real.sqrt (μ : ℝ)) ^ (3 * j) * ((dV μ g (bV μ g H) : ℕ) : ℝ) ^ j) /
        (((j.factorial : ℕ) : ℝ)))

/-- The second (Taylor remainder) term of `above` at the parameters of the `v2` construction. -/
noncomputable def remV (μ g H : ℕ) : ℝ :=
  (N1V μ g H : ℝ) * (QV μ g H : ℝ) * (((dV μ g (bV μ g H) : ℕ) : ℝ) + 1) ^ (bV μ g H + 1) *
    ((Real.sqrt (μ : ℝ) * rhoV μ) ^ (bV μ g H + 1)) /
      ((((bV μ g H + 1).factorial : ℕ) : ℝ))

/-- The third (Lipschitz) term of `above` at the parameters of the `v2` construction. -/
noncomputable def lipV (μ g H : ℕ) : ℝ :=
  (N1V μ g H : ℝ) * (QV μ g H : ℝ) * ((dV μ g (bV μ g H) : ℕ) : ℝ) *
    ((μ : ℝ) + 1) * epsV μ g H

lemma above_eq_terms (μ g H : ℕ) :
    above μ (bV μ g H) (dV μ g (bV μ g H)) (QV μ g H) (rhoV μ) (epsV μ g H)
      = tayV μ g H + remV μ g H + lipV μ g H := rfl

lemma lipV_eq (μ g H : ℕ) :
    lipV μ g H = liou μ (dV μ g (bV μ g H)) (QV μ g H) g H / 4 := by
  have hN : ((N1V μ g H : ℕ) : ℝ) ≠ 0 := by
    have := one_le_N1V μ g H; positivity
  have hQ : ((QV μ g H : ℕ) : ℝ) ≠ 0 := by
    have := one_le_QV μ g H; positivity
  have hd : ((dV μ g (bV μ g H) : ℕ) : ℝ) ≠ 0 := by
    have := one_le_dV μ g (bV μ g H); positivity
  have hm : ((μ : ℝ) + 1) ≠ 0 := by positivity
  simp only [lipV, epsV]
  field_simp

end Work.WilkiesH.Interp
