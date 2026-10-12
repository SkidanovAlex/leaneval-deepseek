import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.scalarB1`

The **scalar (pure `ℝ`) arithmetic** of the in-box grouping row `InBoxCubeRowLarge`
(`Submission/Work/BoseB1Cube/inBoxCubeRowLarge_of_smallNArb.lean`).

The main proof there lives in a very large local context (the whole cube chapter), so every
`linarith`/`nlinarith`/`positivity` written *in situ* is expensive and several of them timed out.
The fix is the standard one: all the numeric content is factored into the little lemmas below,
each stated over a handful of real variables, where the automatic tactics are trivial.  The main
proof then only *instantiates* them.

Notation (the main proof's abbreviations): `V = boxMass`, `W = w1MassB`, `χ = chiMass`,
`S = boxFlatCount`, `Q = boxQCount`, `N = m·n' + n''` (the total slot count), `Ξ` a pointwise
bound of `chiSmallB²`, `𝔉 = ∫Φ²·demandWeight`, `μ` the admissible chemical potential,
`A = a v`, `Γ = PBΓ`, `εs = χ/(432²ΞV)` (the case-split threshold), `Kg` the free gap coefficient,
and `fib` the fibre sum `Work.BoseFixB1.fibSum`.

**Case 1** (`Q ≤ εs·N`): the descent `m·G₁ + G₂` pays the demand.
**Case 2** (`Q > εs·N`): the gap slot `Kg·μ·A·Q` pays the demand.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseB1Cube

/-! ## 0. Elementary square-root toolkit -/

lemma scB1_sqrt_mul_self (N t : ℝ) (hN : 0 ≤ N) (ht : 0 ≤ t) :
    Real.sqrt (N * (t * N)) = Real.sqrt t * N := by
  rw [show N * (t * N) = t * N ^ 2 by ring, Real.sqrt_mul ht, Real.sqrt_sq hN]

lemma scB1_sqrt_div_sq (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    Real.sqrt x / a = Real.sqrt (x / a ^ 2) := by
  rw [Real.sqrt_div hx, Real.sqrt_sq ha]

lemma scB1_sqrt_le_one_add (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ≤ 1 + x := by
  rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ 1 + x)]
  nlinarith [sq_nonneg x]

/-- `χ·a/χ ≤ a` (for `a ≥ 0`; the case `χ = 0` is trivial since `0/0 = 0`). -/
lemma scB1_chi_mul_div_le_self (a χ : ℝ) (ha : 0 ≤ a) : χ * a / χ ≤ a := by
  have h1 : χ * a / χ = (χ / χ) * a := by ring
  rw [h1]
  calc (χ / χ) * a ≤ 1 * a := mul_le_mul_of_nonneg_right (div_self_le_one χ) ha
    _ = a := one_mul a

/-- `√(a·b) ≤ (1+a)(1+b)`. -/
lemma scB1_sqrt_mul_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (1 + a) * (1 + b) := by
  rw [Real.sqrt_mul ha]
  exact mul_le_mul (scB1_sqrt_le_one_add a ha) (scB1_sqrt_le_one_add b hb)
    (Real.sqrt_nonneg b) (by linarith)

/-- `√(Ξχ/V)·√(χ/(432²ΞV)) = χ/(432·V)`: the cancellation making the Cauchy–Schwarz cross term of
`flatScountB_le_Qdecomp` numerically trivial. -/
lemma scB1_sqrt_chi_eq {V χ Ξ : ℝ} (hV : 0 < V) (hχ : 0 ≤ χ) (hΞ : 0 < Ξ) :
    Real.sqrt (Ξ * χ / V) * Real.sqrt (χ / (432 ^ 2 * Ξ * V)) = χ / (432 * V) := by
  have h1 : 0 ≤ Ξ * χ / V := by positivity
  rw [← Real.sqrt_mul h1,
    show Ξ * χ / V * (χ / (432 ^ 2 * Ξ * V)) = (χ / (432 * V)) ^ 2 by
      field_simp
      try ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- `2·(χ/(432V))·N/χ = N/(216V)` for `χ, V ≠ 0`. -/
lemma scB1_two_chi_div_eq (χ V N : ℝ) (hV : V ≠ 0) (hχ : χ ≠ 0) :
    2 * (χ / (432 * V)) * N / χ = N / (216 * V) := by
  field_simp
  ring

/-! ## 1. Case 1 (`Q ≤ εs·N`): the demand-side pieces -/

/-- **Case-1 middle piece**: `2√(Ξχ/V)√(SQ)/χ ≤ N/(216V)` when `Q ≤ εs·N`,
`εs = χ/(432²ΞV)`. -/
lemma scB1_case1_sqrtpiece {S Q V χ Ξ N εs : ℝ}
    (hV : 0 < V) (hΞ : 0 < Ξ) (hχ : 0 ≤ χ) (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hN : 0 ≤ N)
    (hSle : S ≤ N) (hQle : Q ≤ εs * N) (hεs : εs = χ / (432 ^ 2 * Ξ * V)) :
    2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ ≤ N / (216 * V) := by
  rcases eq_or_lt_of_le hχ with h0 | h0
  · rw [← h0]
    have hz : 2 * Real.sqrt (Ξ * 0 / V) * Real.sqrt (S * Q) / 0 = 0 := by
      simp [Real.sqrt_zero]
    rw [hz]
    positivity
  · have hεs0 : 0 ≤ εs := by rw [hεs]; positivity
    have hSQ : S * Q ≤ εs * N ^ 2 := by
      have h1 : S * Q ≤ N * (εs * N) := mul_le_mul hSle hQle hQ hN
      nlinarith only [h1]
    have hsq : Real.sqrt (S * Q) ≤ Real.sqrt εs * N := by
      have h1 := Real.sqrt_le_sqrt hSQ
      rwa [show εs * N ^ 2 = N * (εs * N) by ring,
        scB1_sqrt_mul_self N εs hN hεs0] at h1
    calc 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ
        ≤ 2 * Real.sqrt (Ξ * χ / V) * (Real.sqrt εs * N) / χ :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (by positivity)) hχ
      _ = 2 * (Real.sqrt (Ξ * χ / V) * Real.sqrt εs) * N / χ := by ring
      _ = 2 * (χ / (432 * V)) * N / χ := by
          rw [hεs, scB1_sqrt_chi_eq hV hχ hΞ]
      _ = N / (216 * V) := scB1_two_chi_div_eq χ V N (ne_of_gt hV) (ne_of_gt h0)

/-- **Case-1 excited piece**: `ΞQ/χ ≤ N/(432²V)` when `Q ≤ εs·N`, `εs = χ/(432²ΞV)`. -/
lemma scB1_case1_chiQpiece {Q χ Ξ N V εs : ℝ}
    (hV : 0 < V) (hΞ : 0 < Ξ) (hχ : 0 ≤ χ) (hQ : 0 ≤ Q) (hN : 0 ≤ N)
    (hQle : Q ≤ εs * N) (hεs : εs = χ / (432 ^ 2 * Ξ * V)) :
    Ξ * Q / χ ≤ N / (432 ^ 2 * V) := by
  rcases eq_or_lt_of_le hχ with h0 | h0
  · rw [← h0]
    have hz : Ξ * Q / 0 = 0 := div_zero _
    rw [hz]
    positivity
  · have h1 : Ξ * Q ≤ Ξ * (εs * N) := mul_le_mul_of_nonneg_left hQle hΞ.le
    refine le_trans (div_le_div_of_nonneg_right h1 hχ) ?_
    have h2 : Ξ * (εs * N) = χ * (N / (432 ^ 2 * V)) := by
      rw [hεs]
      field_simp
      try ring
    rw [h2]
    exact scB1_chi_mul_div_le_self (N / (432 ^ 2 * V)) χ (by positivity)

/-- **The `τ`-rewriting**: dividing the `flatScountB_le_Qdecomp` bound by `χ ≥ 0`. -/
lemma scB1_tau_bound {S Q V χ Ξ A0 : ℝ} (hV : 0 < V) (hχ : 0 ≤ χ) (hS : 0 ≤ S)
    (h : A0 ≤ (χ / V) * S + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) + Ξ * Q) :
    A0 / χ ≤ S / V + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ + Ξ * Q / χ := by
  have h1 : ((χ / V) * S) / χ ≤ S / V := by
    have h2 := scB1_chi_mul_div_le_self (S / V) χ (div_nonneg hS hV.le)
    rwa [show χ * (S / V) / χ = ((χ / V) * S) / χ by ring] at h2
  calc A0 / χ
      ≤ ((χ / V) * S + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) + Ξ * Q) / χ :=
        div_le_div_of_nonneg_right h hχ
    _ = ((χ / V) * S) / χ + (2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q)) / χ
          + (Ξ * Q) / χ := by rw [add_div, add_div]
    _ ≤ S / V + 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ + Ξ * Q / χ := by
        linarith only [h1]

/-- **Case-1 demand bound.**  From `𝔉 ≤ μτ + μ²`, `τ ≤ ρc(1 + 1/216 + 1/432²)`, `μ ≤ ρc` and
`c1 ≤ 1/100`: `c1·W·𝔉 ≤ μ·ρc·W/36`. -/
lemma scB1_case1_D {c1 W μ 𝔉 τf ρc : ℝ} (hc1 : 0 ≤ c1) (hc1' : c1 ≤ 1 / 100)
    (hW : 0 ≤ W) (hμ : 0 ≤ μ) (hρc : 0 ≤ ρc) (hμρ : μ ≤ ρc)
    (hF : 𝔉 ≤ μ * τf + μ ^ 2) (hτ : τf ≤ ρc * (1 + 1 / 216 + 1 / 432 ^ 2)) :
    c1 * (W * 𝔉) ≤ μ * ρc * W / 36 := by
  have h1 : μ * τf ≤ μ * (ρc * (1 + 1 / 216 + 1 / 432 ^ 2)) := mul_le_mul_of_nonneg_left hτ hμ
  have h2 : μ ^ 2 ≤ μ * ρc := by nlinarith only [hμ, hμρ]
  have h3 : 𝔉 ≤ μ * ρc * (2 + 1 / 216 + 1 / 432 ^ 2) := by
    nlinarith only [hF, h1, h2]
  have h4 : c1 * (2 + 1 / 216 + 1 / 432 ^ 2) ≤ 1 / 36 := by nlinarith only [hc1']
  calc c1 * (W * 𝔉) ≤ c1 * (W * (μ * ρc * (2 + 1 / 216 + 1 / 432 ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hW) hc1
    _ = (c1 * (2 + 1 / 216 + 1 / 432 ^ 2)) * (μ * ρc * W) := by ring
    _ ≤ (1 / 36) * (μ * ρc * W) := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = μ * ρc * W / 36 := by ring

/-- **Case-1 `M₁` piece**: `μρcW/36 ≤ m·(1/18)μ(n'/V)W + (1/4)((n''/V)−μ)²W` when
`ρc = (mn'+n'')/V` and `n'' ≤ mn'`. -/
lemma scB1_case1_M1 {μ ρc W m n' n'' V : ℝ} (hV : 0 < V) (hμ : 0 ≤ μ) (hW : 0 ≤ W)
    (hρc : ρc = (m * n' + n'') / V) (hnn : n'' ≤ m * n') :
    μ * ρc * W / 36 ≤ m * ((1 / 18) * μ * (n' / V) * W)
      + (1 / 4) * ((n'' / V) - μ) ^ 2 * W := by
  have h0 : 0 ≤ (1 / 4) * ((n'' / V) - μ) ^ 2 * W := by
    have := sq_nonneg ((n'' / V) - μ); nlinarith only [this, hW]
  have h1 : μ * ρc * W / 36 ≤ m * ((1 / 18) * μ * (n' / V) * W) := by
    have hle : (m * n' + n'') / V ≤ 2 * (m * n') / V := by
      refine div_le_div_of_nonneg_right ?_ hV.le
      linarith only [hnn]
    calc μ * ρc * W / 36 = (μ * W / 36) * ((m * n' + n'') / V) := by rw [hρc]; ring
      _ ≤ (μ * W / 36) * (2 * (m * n') / V) := by
          refine mul_le_mul_of_nonneg_left hle ?_
          have := mul_nonneg hμ hW; positivity
      _ = m * ((1 / 18) * μ * (n' / V) * W) := by ring
  linarith only [h0, h1]

/-- **Case-1 error-bracket piece**: `C_h·Z ≤ Cc·Zc` where `Z = μ²AΓW + μA`,
`Zc = μ²AΓχ + μA`, `Cc ≥ C_h·C_w·A`, `Cc ≥ C_h` and `W ≤ C_w·A·χ`. -/
lemma scB1_case1_E {Cc Ch Cw A W χ μ Γ : ℝ}
    (hCc1 : Ch * (Cw * A) ≤ Cc) (hCc2 : Ch ≤ Cc) (hCh : 0 ≤ Ch) (hW : 0 ≤ W)
    (hWle : W ≤ Cw * A * χ) (hμ : 0 ≤ μ) (hA : 0 ≤ A) (hΓ : 0 ≤ Γ) (hχ : 0 ≤ χ) :
    Ch * (μ ^ 2 * A * Γ * W + μ * A) ≤ Cc * (μ ^ 2 * A * Γ * χ + μ * A) := by
  have h1 : Ch * W ≤ Cc * χ := by
    calc Ch * W ≤ Ch * (Cw * A * χ) := mul_le_mul_of_nonneg_left hWle hCh
      _ = (Ch * (Cw * A)) * χ := by ring
      _ ≤ Cc * χ := mul_le_mul_of_nonneg_right hCc1 hχ
  have h3 : 0 ≤ μ ^ 2 * A * Γ := mul_nonneg (mul_nonneg (sq_nonneg μ) hA) hΓ
  have h2 : Ch * (μ ^ 2 * A * Γ * W) ≤ Cc * (μ ^ 2 * A * Γ * χ) := by
    calc Ch * (μ ^ 2 * A * Γ * W) = (Ch * W) * (μ ^ 2 * A * Γ) := by ring
      _ ≤ (Cc * χ) * (μ ^ 2 * A * Γ) := mul_le_mul_of_nonneg_right h1 h3
      _ = Cc * (μ ^ 2 * A * Γ * χ) := by ring
  have h4 : Ch * (μ * A) ≤ Cc * (μ * A) := mul_le_mul_of_nonneg_right hCc2 (mul_nonneg hμ hA)
  calc Ch * (μ ^ 2 * A * Γ * W + μ * A) = Ch * (μ ^ 2 * A * Γ * W) + Ch * (μ * A) := by ring
    _ ≤ Cc * (μ ^ 2 * A * Γ * χ) + Cc * (μ * A) := add_le_add h2 h4
    _ = Cc * (μ ^ 2 * A * Γ * χ + μ * A) := by ring

/-- **Case-1 error-bracket piece, the two-`Γ` form**: the descent's bracket carries `Γ₁ = PBΓ v μ`
while the demand's carries the enlarged `Γ₂ = (R/(ℓd))² + PBΓ v μ ≥ Γ₁`. -/
lemma scB1_case1_E2 {Cc Ch Cw A W χ Γ₁ Γ₂ μ : ℝ}
    (hCc1 : Ch * (Cw * A) ≤ Cc) (hCc2 : Ch ≤ Cc) (hCh : 0 ≤ Ch) (hW : 0 ≤ W)
    (hWle : W ≤ Cw * A * χ) (hμ : 0 ≤ μ) (hA : 0 ≤ A) (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (hχ : 0 ≤ χ) (hΓle : Γ₁ ≤ Γ₂) :
    Ch * (μ ^ 2 * A * Γ₁ * W + μ * A) ≤ Cc * (μ ^ 2 * A * Γ₂ * χ + μ * A) := by
  have h1 : μ ^ 2 * A * Γ₁ * W ≤ μ ^ 2 * A * Γ₂ * W := by
    refine mul_le_mul_of_nonneg_right ?_ hW
    exact mul_le_mul_of_nonneg_left hΓle (mul_nonneg (sq_nonneg μ) hA)
  have h2 : Ch * (μ ^ 2 * A * Γ₁ * W + μ * A) ≤ Ch * (μ ^ 2 * A * Γ₂ * W + μ * A) :=
    mul_le_mul_of_nonneg_left (add_le_add h1 (le_refl _)) hCh
  exact le_trans h2 (scB1_case1_E hCc1 hCc2 hCh hW hWle hμ hA hΓ₂ hχ)

/-- **Case-1 final assembly**: the pieces of `perBoxCubeLHSFun ≤ sbWordCube` at `Q ≤ εs·N`.

`hd` is the descent's conclusion at the *literal* size values (`m`, `n'`, `n''`, the count at the
group sizes), `hM1` the positive part of the descent bound compared with the demand's first term,
`hE` the two error brackets. -/
lemma scB1_case1_close {c1 W μ 𝔉 m n' n'' V ChZ CcZc sbWord ρc : ℝ}
    (hD : c1 * (W * 𝔉) ≤ μ * ρc * W / 36)
    (hM1 : μ * ρc * W / 36 ≤ m * ((1 / 18) * μ * (n' / V) * W)
        + (1 / 4) * ((n'' / V) - μ) ^ 2 * W)
    (hE : ChZ ≤ CcZc)
    (hd : m * ((1 / 18) * μ * (n' / V) * W)
        + ((1 / 4) * ((n'' / V) - μ) ^ 2 * W - (1 / 2) * μ ^ 2 * W - ChZ) ≤ sbWord) :
    c1 * (W * 𝔉) - (1 / 2) * μ ^ 2 * W - CcZc ≤ sbWord := by
  linarith only [hD, hM1, hE, hd]

/-! ## 2. Case 2 (`Q > εs·N`): the reduced hypotheses -/

/-- From the case hypothesis `εs·S < Q` (`εs = χ/(432²ΞV)`) deduce `χ·S ≤ 432²ΞVQ`. -/
lemma scB1_chiS_of {S Q V χ Ξ εs : ℝ} (hV : 0 < V) (hΞ : 0 < Ξ)
    (hεs : εs = χ / (432 ^ 2 * Ξ * V)) (h : S * εs < Q) :
    χ * S ≤ 432 ^ 2 * Ξ * V * Q := by
  have h1 : S * (χ / (432 ^ 2 * Ξ * V)) < Q := by rw [hεs] at h; exact h
  have h2 : (S * (χ / (432 ^ 2 * Ξ * V))) * (432 ^ 2 * Ξ * V) < Q * (432 ^ 2 * Ξ * V) :=
    mul_lt_mul_of_pos_right h1 (by positivity)
  have h3 : (S * (χ / (432 ^ 2 * Ξ * V))) * (432 ^ 2 * Ξ * V) = S * χ := by
    field_simp
  linarith only [h2, h3.le, h3.ge]

/-- From `εs·N < Q` together with `μV ≤ N` deduce `χ·μ ≤ 432²ΞQ`. -/
lemma scB1_chiMu_of {μ Q V χ Ξ εs N : ℝ} (hV : 0 < V) (hΞ : 0 < Ξ) (hχ : 0 ≤ χ)
    (hμ : 0 ≤ μ) (hεs : εs = χ / (432 ^ 2 * Ξ * V)) (hμV : μ * V ≤ N) (h : εs * N < Q) :
    χ * μ ≤ 432 ^ 2 * Ξ * Q := by
  have hεs0 : 0 ≤ εs := by rw [hεs]; positivity
  have h1 : εs * (μ * V) ≤ εs * N := mul_le_mul_of_nonneg_left hμV hεs0
  have h2 : εs * (μ * V) = χ * μ / (432 ^ 2 * Ξ) := by
    rw [hεs]; field_simp; try ring
  have h3 : χ * μ / (432 ^ 2 * Ξ) < Q := by linarith only [h1, h2.le, h2.ge, h]
  have h4 : (χ * μ / (432 ^ 2 * Ξ)) * (432 ^ 2 * Ξ) = χ * μ := by
    field_simp
  have h5 : (χ * μ / (432 ^ 2 * Ξ)) * (432 ^ 2 * Ξ) < Q * (432 ^ 2 * Ξ) :=
    mul_lt_mul_of_pos_right h3 (by positivity)
  nlinarith only [h4, h5]

/-- From `S·εs ≤ Q` deduce `χ·Λ ≤ 864ΞQ` where `Λ = 2√(Ξχ/V)√(SQ)/χ` is the Cauchy–Schwarz
cross term of `flatScountB_le_Qdecomp`. -/
lemma scB1_case2_chiLambda {S Q V χ Ξ εs : ℝ} (hV : 0 < V) (hΞ : 0 < Ξ) (hχ : 0 ≤ χ)
    (hQ : 0 ≤ Q) (hεs : εs = χ / (432 ^ 2 * Ξ * V)) (hSε : S * εs ≤ Q) :
    χ * (2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ) ≤ 864 * Ξ * Q := by
  rcases eq_or_lt_of_le hχ with h0 | h0
  · rw [← h0]
    have hz : (0 : ℝ) * (2 * Real.sqrt (Ξ * 0 / V) * Real.sqrt (S * Q) / 0) = 0 := by
      simp [Real.sqrt_zero]
    rw [hz]
    have := mul_nonneg (by linarith : (0:ℝ) ≤ Ξ) hQ
    linarith only [this]
  · have hεs0 : 0 < εs := by rw [hεs]; positivity
    have hSQ : S * Q ≤ Q ^ 2 / εs := by
      rw [le_div_iff₀ hεs0]
      nlinarith only [hSε, hQ]
    have hsq : Real.sqrt (S * Q) ≤ Q / Real.sqrt εs := by
      have h1 := Real.sqrt_le_sqrt hSQ
      rwa [Real.sqrt_div (sq_nonneg Q) εs, Real.sqrt_sq hQ] at h1
    have hval : Real.sqrt (Ξ * χ / V) / Real.sqrt εs = 432 * Ξ := by
      rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ Ξ * χ / V) εs]
      have h2 : Ξ * χ / V / εs = 432 ^ 2 * Ξ ^ 2 := by
        rw [hεs]; field_simp; try ring
      rw [h2, show 432 ^ 2 * Ξ ^ 2 = (432 * Ξ) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    calc χ * (2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ)
        = (χ / χ) * (2 * (Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q))) := by ring
      _ = 2 * (Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q)) := by
            rw [div_self (ne_of_gt h0), one_mul]
      _ ≤ 2 * (Real.sqrt (Ξ * χ / V) * (Q / Real.sqrt εs)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) (by norm_num)
      _ = 2 * (Real.sqrt (Ξ * χ / V) / Real.sqrt εs) * Q := by ring
      _ = 2 * (432 * Ξ) * Q := by rw [hval]
      _ = 864 * Ξ * Q := by ring

/-- The nonnegativity of `τ` from its defining bound. -/
lemma scB1_tau_nonneg {S V Λ Ξ Q χ : ℝ} (hV : 0 < V) (hΞ : 0 ≤ Ξ) (hχ : 0 ≤ χ) (hS : 0 ≤ S)
    (hΛ : 0 ≤ Λ) (hQ : 0 ≤ Q) :
    0 ≤ S / V + Λ + Ξ * Q / χ := by
  have h1 : 0 ≤ S / V := div_nonneg hS hV.le
  have h2 : 0 ≤ Ξ * Q / χ := div_nonneg (mul_nonneg hΞ hQ) hχ
  linarith only [h1, h2, hΛ]

/-- **Case-2 final assembly**: the gap slot plus the fibre row pay the demand. -/
lemma scB1_case2_close {c1 W μ 𝔉 fib Kg A Q CcZc sbWord : ℝ}
    (h : c1 * (W * 𝔉) + μ * fib ≤ Kg * μ * A * Q)
    (h2 : Kg * μ * A * Q - μ * fib ≤ sbWord)
    (hnn : 0 ≤ (1 / 2) * μ ^ 2 * W + CcZc) :
    c1 * (W * 𝔉) - (1 / 2) * μ ^ 2 * W - CcZc ≤ sbWord := by
  linarith only [h, h2, hnn]

/-! ## 3. `Kg`-bookkeeping

The free gap coefficient `Kg` is built in the main proof as a *sum* of `4·(each requirement)`, so
the four requirement inequalities of the case-2 core are immediate. -/

lemma scB1_Kg_of_sum {K1 K2 K3 K4 Kg : ℝ} (h1 : 0 ≤ K1) (h2 : 0 ≤ K2) (h3 : 0 ≤ K3)
    (h4 : 0 ≤ K4) (h : Kg = 4 * K1 + 4 * K2 + 4 * K3 + 4 * K4 + 1) :
    K1 ≤ Kg / 4 ∧ K2 ≤ Kg / 4 ∧ K3 ≤ Kg / 4 ∧ K4 ≤ Kg / 4 := by
  have e1 : 4 * K1 ≤ Kg := by linarith only [h2, h3, h4, h]
  have e2 : 4 * K2 ≤ Kg := by linarith only [h1, h3, h4, h]
  have e3 : 4 * K3 ≤ Kg := by linarith only [h1, h2, h4, h]
  have e4 : 4 * K4 ≤ Kg := by linarith only [h1, h2, h3, h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [e1, e2, e3, e4]

/-- The nonnegativity of the Cauchy–Schwarz cross term `Λ = 2√(Ξχ/V)√(SQ)/χ`. -/
lemma scB1_Lambda_nonneg {S Q V χ Ξ : ℝ} (hΞ : 0 ≤ Ξ) (hχ : 0 ≤ χ) (hS : 0 ≤ S) (hQ : 0 ≤ Q) :
    0 ≤ 2 * Real.sqrt (Ξ * χ / V) * Real.sqrt (S * Q) / χ := by
  rcases eq_or_lt_of_le hχ with h0 | h0
  · rw [← h0]
    have hz : 2 * Real.sqrt (Ξ * 0 / V) * Real.sqrt (S * Q) / 0 = 0 := by
      simp [Real.sqrt_zero]
    rw [hz]
  · positivity

end Work.BoseB1Cube
