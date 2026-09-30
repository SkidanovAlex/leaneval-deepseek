import Mathlib
import Submission.Work.BMF.zeta_arc_cost_def

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-!
# The numeric core of the Vinogradov–Korobov zero-free region

`Work.BMF.zeta_vk_arith` is the existence statement for the disc-radius window used in the
VK zero-free-region argument.  The proof picks the explicit constants

* `U := 1 + A + B + C₀`, `c₀ := 1/(10^22 · U^100)`, `c_λ := 10^20 · U^100`, `c₁ := c₀/10^6`,
* `T₁ := exp 3 - 3` (so that `ℓ = log(|t|+3) ≥ 3` and `L = log ℓ ≥ 1` for `|t| ≥ T₁`),

and for `|t| ≥ T₁` takes the window `[a,b] = [c_λ·x·L, 2c_λ·x·L]`, where `x = c₀/VKd(|t|+3)`.
On it, `2x/R ≤ 2/(c_λL)`, `x·L ≤ c₀`, `log(2/x) ≤ (log(2/c₀)+1)·L` and
`x·R^{1/2}·ℓ ≤ (2c_λ)^{1/2}c₀^{3/2}`, which turn the four required estimates into the
numerical inequalities `20D/(πc_λ) + 10 log U/(πc_λ) + (40B/π)(2c_λ)^{1/2}c₀^{3/2}
+ 100/(πc_λ) ≤ 1/100` with `D = log(2/c₀)+1 ≤ 300U`.

The auxiliary lemmas below are elementary inputs (`arcCost_le_self`, `vk_inputs_self`) and
two arithmetic trivialities (`five_four_sum_identity`, `div_pi_le_400`).
-/

namespace Work.BMF

open Real

/-- Explicit majorant for the circle-integral cost `Work.BMF.ArcCost` at the centre `1 + x`
(with `σ - 1 = x`): if `A ≤ U`, `log(2/x) ≤ D·L`, `1 ≤ ℓ`, `1 ≤ L` and `log(|τ|+3) + 1 ≤ 2ℓ`,
then `ArcCost A B (1+x) τ R ≤ 8DL + 4 log U + 8 B R^{3/2}·(2ℓ) + 40 L`. -/
lemma arcCost_le_self {A B U D x τ R ℓ L : ℝ} (hA : 0 < A) (hAU : A ≤ U) (hB : 0 < B)
    (hR : 0 < R) (hx : 0 < x) (hℓ : 1 ≤ ℓ) (hL : 1 ≤ L)
    (hτ : Real.log (|τ| + 3) + 1 ≤ 2 * ℓ)
    (hℓL : Real.log (2 * ℓ) ≤ 2 * L)
    (hlog : Real.log (2 / x) ≤ D * L) :
    ArcCost A B (1 + x) τ R
      ≤ 8 * D * L + 4 * Real.log U + 8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ) + 40 * L := by
  have hlogA : Real.log A ≤ Real.log U := Real.log_le_log hA hAU
  have hℓτ0 : (0 : ℝ) ≤ Real.log (|τ| + 3) := Real.log_nonneg (by linarith [abs_nonneg τ])
  have hτpos : 0 < Real.log (|τ| + 3) + 1 := by linarith
  have hloglog : Real.log (Real.log (|τ| + 3) + 1) ≤ 2 * L :=
    le_trans (Real.log_le_log hτpos hτ) hℓL
  have hB32 : 0 ≤ 8 * B * R ^ (3 / 2 : ℝ) := by positivity
  have h3 : 8 * B * R ^ (3 / 2 : ℝ) * (Real.log (|τ| + 3) + 1)
      ≤ 8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ) := mul_le_mul_of_nonneg_left hτ hB32
  have hLpos : 0 < L := by linarith
  have hlogL : Real.log L ≤ L := Real.log_le_self hLpos.le
  have hlog3 : Real.log 3 ≤ 2 := by
    have hexp : (3 : ℝ) ≤ Real.exp 2 := by
      have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [h]; nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)]
    exact hexp
  have h4 : 8 * (Real.log (Real.log (Real.log (|τ| + 3) + 1) + 1) + 1) + 8 ≤ 40 * L := by
    have hpos2 : 0 < Real.log (Real.log (|τ| + 3) + 1) + 1 := by
      have hh : 0 ≤ Real.log (Real.log (|τ| + 3) + 1) :=
        Real.log_nonneg (by linarith : (1 : ℝ) ≤ Real.log (|τ| + 3) + 1)
      linarith
    have h1 : Real.log (Real.log (Real.log (|τ| + 3) + 1) + 1) ≤ Real.log (2 * L + 1) :=
      Real.log_le_log hpos2 (by linarith)
    have h2 : Real.log (2 * L + 1) ≤ Real.log (3 * L) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3' : Real.log (3 * L) ≤ 2 + L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hLpos)]
      linarith
    linarith
  have hkey : ArcCost A B (1 + x) τ R
      = 8 * Real.log (2 / x) + 4 * Real.log A
        + 8 * B * R ^ (3 / 2 : ℝ) * (Real.log (|τ| + 3) + 1)
        + 8 * (Real.log (Real.log (|τ| + 3) + 1) + 1) + 8 := by
    unfold ArcCost
    rw [show (1 + x) - 1 = x by ring]
  rw [hkey]
  linarith


/-- `VKd y ≤ VKd y'`-free elementary inputs: with `x := c₀/VKd y` and `L := log(log y)`,
`x·L ≤ c₀`; `1 ≤ VKd y`; `log(2/x) ≤ (log(2/c₀)+1)·L`; `x^{3/2}L^{1/2} = c₀^{3/2}/log y`. -/
lemma vk_inputs_self {c₀ y : ℝ} (hc₀ : 0 < c₀) (hc2 : c₀ ≤ 2)
    (hℓ : 3 ≤ Real.log y) (hL : 1 ≤ Real.log (Real.log y)) :
    (c₀ / VKd y) * Real.log (Real.log y) ≤ c₀ ∧
    1 ≤ VKd y ∧
    Real.log (2 / (c₀ / VKd y)) ≤ (Real.log (2 / c₀) + 1) * Real.log (Real.log y) ∧
    (c₀ / VKd y) ^ (3 / 2 : ℝ) * (Real.log (Real.log y)) ^ (1 / 2 : ℝ)
      = c₀ ^ (3 / 2 : ℝ) / Real.log y := by
  have hℓ0 : 0 < Real.log y := by linarith
  have hL0 : 0 < Real.log (Real.log y) := by linarith
  have hVKd : VKd y = (Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ) := by
    rw [VKd_def]
  have hVKdpos : 0 < VKd y := by
    rw [hVKd]
    exact mul_pos (Real.rpow_pos_of_pos hℓ0 _) (Real.rpow_pos_of_pos hL0 _)
  have hxpos : 0 < c₀ / VKd y := div_pos hc₀ hVKdpos
  have hLle : Real.log (Real.log y) ≤ Real.log y := Real.log_le_self hℓ0.le
  have h23 : (Real.log (Real.log y)) ^ (2 / 3 : ℝ) ≤ (Real.log y) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hL0.le hLle (by norm_num)
  have hL13 : 0 ≤ (Real.log (Real.log y)) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hL0.le _
  have hsplit : Real.log (Real.log y)
      = (Real.log (Real.log y)) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ) := by
    have hs := Real.rpow_add hL0 (2 / 3 : ℝ) (1 / 3 : ℝ)
    rw [show (2 / 3 : ℝ) + 1 / 3 = 1 by norm_num, Real.rpow_one] at hs
    exact hs
  -- (1) `x·L ≤ c₀`
  have h1 : (c₀ / VKd y) * Real.log (Real.log y) ≤ c₀ := by
    have hLVK : Real.log (Real.log y) ≤ VKd y := by
      rw [hVKd]
      conv_lhs => rw [hsplit]
      exact mul_le_mul_of_nonneg_right h23 hL13
    calc (c₀ / VKd y) * Real.log (Real.log y) = c₀ * (Real.log (Real.log y) / VKd y) := by ring
      _ ≤ c₀ * (VKd y / VKd y) := by
          apply mul_le_mul_of_nonneg_left _ hc₀.le
          exact div_le_div_of_nonneg_right hLVK hVKdpos.le
      _ = c₀ := by field_simp
  -- (2) `1 ≤ VKd y`
  have h2 : 1 ≤ VKd y := by
    rw [hVKd]
    have h1' : (1 : ℝ) ≤ (Real.log y) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have h2' : (1 : ℝ) ≤ (Real.log (Real.log y)) ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow hL (by norm_num)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ) :=
          mul_le_mul h1' h2' (by norm_num) (Real.rpow_nonneg hℓ0.le _)
  -- (3) `log(2/x) ≤ (log(2/c₀)+1)·L`
  have h3 : Real.log (2 / (c₀ / VKd y))
      ≤ (Real.log (2 / c₀) + 1) * Real.log (Real.log y) := by
    have h2x : 2 / (c₀ / VKd y) = (2 / c₀) * VKd y := by
      field_simp
    rw [h2x, Real.log_mul (by positivity) (ne_of_gt hVKdpos), hVKd,
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hℓ0, Real.log_rpow hL0]
    have hlogL : Real.log (Real.log (Real.log y)) ≤ Real.log (Real.log y) := Real.log_le_self hL0.le
    have hlog2c0 : 0 ≤ Real.log (2 / c₀) := Real.log_nonneg (by rw [one_le_div hc₀]; linarith)
    nlinarith [hlogL, hL, hlog2c0]
  -- (4) the rpow identity
  have h4 : (c₀ / VKd y) ^ (3 / 2 : ℝ) * (Real.log (Real.log y)) ^ (1 / 2 : ℝ)
      = c₀ ^ (3 / 2 : ℝ) / Real.log y := by
    have hcube : (c₀ / VKd y) ^ 3 * Real.log (Real.log y) = c₀ ^ 3 / (Real.log y) ^ 2 := by
      have hu : ((Real.log y) ^ (2 / 3 : ℝ)) ^ 3 = (Real.log y) ^ 2 := by
        rw [← Real.rpow_natCast ((Real.log y) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hℓ0.le]
        norm_num
      have hv : ((Real.log (Real.log y)) ^ (1 / 3 : ℝ)) ^ 3 = Real.log (Real.log y) := by
        rw [← Real.rpow_natCast ((Real.log (Real.log y)) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hL0.le]
        norm_num
      have hw : ((Real.log y) ^ (2 / 3 : ℝ) * (Real.log (Real.log y)) ^ (1 / 3 : ℝ)) ^ 3
          = (Real.log y) ^ 2 * Real.log (Real.log y) := by
        rw [mul_pow, hu, hv]
      rw [hVKd, div_pow, hw]
      field_simp
      try ring
    have hA : (c₀ / VKd y) ^ (3 / 2 : ℝ) = ((c₀ / VKd y) ^ 3) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast (c₀ / VKd y) 3, ← Real.rpow_mul hxpos.le]
      norm_num
    have hB : ((c₀ / VKd y) ^ 3) ^ (1 / 2 : ℝ) * (Real.log (Real.log y)) ^ (1 / 2 : ℝ)
        = ((c₀ / VKd y) ^ 3 * Real.log (Real.log y)) ^ (1 / 2 : ℝ) :=
      (Real.mul_rpow (by positivity) (by positivity)).symm
    have hc3 : c₀ ^ 3 = (c₀ ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (c₀ ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hc₀.le]
      norm_num
    have hsq : c₀ ^ 3 / (Real.log y) ^ 2 = (c₀ ^ (3 / 2 : ℝ) / Real.log y) ^ 2 := by
      rw [div_pow, hc3]
    rw [hA, hB, hcube, hsq]
    rw [← Real.rpow_natCast (c₀ ^ (3 / 2 : ℝ) / Real.log y) 2,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ c₀ ^ (3 / 2 : ℝ) / Real.log y)]
    rw [show (((2 : ℕ) : ℝ) * (1 / 2)) = 1 by norm_num, Real.rpow_one]
  exact ⟨h1, h2, h3, h4⟩

/-- Distributing `5/4` over a sum of four products. -/
lemma five_four_sum_identity {Y A1 A2 A3 A4 : ℝ} :
    Y * ((5 / 4) * (A1 + A2 + A3 + A4))
      = (5 / 4) * (Y * A1) + (5 / 4) * (Y * A2) + (5 / 4) * (Y * A3) + (5 / 4) * (Y * A4) := by
  ring

/-- `X/(π Q) ≤ 1/400` when `X ≤ 3Q/400` and `Q > 0` (using `π > 3`). -/
lemma div_pi_le_400 {X Q : ℝ} (hQ : 0 < Q) (hX : X ≤ 3 * Q / 400) :
    X / (Real.pi * Q) ≤ 1 / 400 := by
  have hπ : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  rw [div_le_iff₀ (by positivity)]
  have h2 : 3 * Q / 400 ≤ (1 / 400) * (Real.pi * Q) := by
    have he : (1 / 400) * (Real.pi * Q) = Real.pi * Q / 400 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hπ hQ.le) (by norm_num)
  linarith

/-- **Numeric core of the Vinogradov–Korobov zero-free region** (piecewise form).

For all `A, B > 0` and `C₀ ≥ 0` there are constants `T₁ ≥ 4` and `c₀, c₁ > 0` with `c₁ ≤ c₀/24`
such that for every `t` with `T₁ ≤ |t|` there is an interval `[a,b]` of admissible disc radii with
`0 < a < b ≤ 1/8` and `2·(c₀/VKd(|t|+3)) < a`, on which the four estimates

* `(2x/R)² ≤ 1/100` (the zero sits well inside the disc),
* `(3/4)·(c₁/c₀) ≤ 1/100` (the zero is much closer to the line `Re = 1` than the centre),
* `(3C₀/4)·(2x) ≤ 1/100` (the pole term is negligible),
* `(2x/(πR))·(ArcCost A B (1+x) |t| R + ArcCost A B (1+x) (2|t|) R / 4) ≤ 1/100`
  (the circle-integral cost is negligible),

hold for every `R ∈ [a,b]`, where `x := c₀/VKd(|t|+3)` and
`ArcCost A B σ τ R = 8 log(2/(σ-1)) + 4 log A + 8 B R^{3/2}(log(|τ|+3)+1)
  + 8(log(log(|τ|+3)+1)+1) + 8` is `Work.BMF.ArcCost` in
`Submission/Work/BMF/zeta_arc_cost_def.lean` (needs that import).

Route: with `ℓ = log(|t|+3)`, `L = log ℓ`, take `x = c₀ ℓ^{-2/3}L^{-1/3}` and the interval
`[a,b] = [c_λ xL, 2c_λ xL]` with `c_λ` large. Then `(2x/R)² ≤ (2/(c_λL))²`, `B·R^{3/2}/R·(2x) =
2B c₀^{3/2}c_λ^{1/2}`, and `(2x/R)·8 log(2/x) ≤ (16/(π c_λ))(2/3)`, so choosing `c₀` small
(depending on `A, B`) and then `c_λ` large and `T₁` large makes all four `≤ 1/100`. -/
theorem zeta_vk_arith (A B C₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC₀ : 0 ≤ C₀) :
    ∃ T₁ c₁ c₀ : ℝ, 4 ≤ T₁ ∧ 0 < c₁ ∧ 0 < c₀ ∧ c₁ ≤ c₀ / 24 ∧
      ∀ t : ℝ, T₁ ≤ |t| →
        ∃ a b : ℝ, 0 < a ∧ a < b ∧ b ≤ 1 / 8 ∧
          2 * (c₀ / VKd (|t| + 3)) < a ∧
          ∀ R : ℝ, a ≤ R → R ≤ b →
            (2 * (c₀ / VKd (|t| + 3)) / R) ^ 2 ≤ 1 / 100 ∧
            (3 / 4) * (c₁ / c₀) ≤ 1 / 100 ∧
            (3 * C₀ / 4) * (2 * (c₀ / VKd (|t| + 3))) ≤ 1 / 100 ∧
            (2 * (c₀ / VKd (|t| + 3)) / (Real.pi * R)) *
              (ArcCost A B (1 + c₀ / VKd (|t| + 3)) |t| R
                + ArcCost A B (1 + c₀ / VKd (|t| + 3)) (2 * |t|) R / 4) ≤ 1 / 100
:= by
  obtain ⟨U, hU1, hUdef⟩ : ∃ U : ℝ, 1 ≤ U ∧ U = 1 + A + B + C₀ :=
    ⟨1 + A + B + C₀, by linarith, rfl⟩
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hAU : A ≤ U := by rw [hUdef]; linarith
  have hBU : B ≤ U := by rw [hUdef]; linarith
  have hCU : C₀ ≤ U := by rw [hUdef]; linarith
  have hT1ge : (4 : ℝ) ≤ Real.exp 3 - 3 := by
    have h2 : (8 : ℝ) < Real.exp 3 := by
      have h := pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (3 : ℕ) ≠ 0)
      norm_num at h
      exact h
    linarith
  set c0 : ℝ := 1 / ((10 : ℝ)^22 * U^100) with hc0
  set cl : ℝ := (10 : ℝ)^20 * U^100 with hcl
  have hU100pos : (0 : ℝ) < U^100 := pow_pos hU0 100
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hclpos : 0 < cl := by rw [hcl]; positivity
  have hclc0 : cl * c0 = 1 / 100 := by
    rw [hcl, hc0]
    field_simp
    norm_num
  have hmul_le : ∀ Z : ℝ, Z ≤ U → Z * c0 ≤ 1 / ((10 : ℝ)^22) := by
    intro Z hZ
    rw [hc0, mul_one_div]
    have h1 : Z / ((10 : ℝ)^22 * U^100) ≤ U / ((10 : ℝ)^22 * U^100) :=
      div_le_div_of_nonneg_right hZ (by positivity)
    have heq : U / ((10 : ℝ)^22 * U^100) = 1 / ((10 : ℝ)^22 * U^99) := by
      field_simp
    have hge : ((10 : ℝ)^22) ≤ (10 : ℝ)^22 * U^99 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hU1)
    have h2 : 1 / ((10 : ℝ)^22 * U^99) ≤ 1 / ((10 : ℝ)^22) :=
      one_div_le_one_div_of_le (by positivity) hge
    rw [heq] at h1
    linarith
  have hclge : (10 : ℝ)^20 ≤ cl := by
    rw [hcl]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hU1)
  have hUle : U ≤ U^100 := by
    calc U = U * 1 := by ring
      _ ≤ U * U^99 := mul_le_mul_of_nonneg_left (one_le_pow₀ hU1) hU0.le
      _ = U^100 := by ring
  have hc0le1 : c0 ≤ 1 := by
    rw [hc0, div_le_one (by positivity : (0 : ℝ) < (10 : ℝ)^22 * U^100)]
    exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hU1)
  have hc0le2 : c0 ≤ 2 := by linarith
  set D : ℝ := Real.log (2 / c0) + 1 with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    have h : 1 ≤ 2 / c0 := by
      rw [le_div_iff₀ hc0pos]
      linarith
    linarith [Real.log_nonneg h]
  have hDle : D ≤ 300 * U := by
    rw [hD, hc0]
    have h2c0 : 2 / (1 / ((10 : ℝ)^22 * U^100)) = 2 * ((10 : ℝ)^22 * U^100) := by
      field_simp
    rw [h2c0]
    have hsplit : Real.log (2 * ((10 : ℝ)^22 * U^100))
        = Real.log 2 + (22 * Real.log 10 + 100 * Real.log U) := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hU100pos), Real.log_pow 10 22, Real.log_pow U 100]
      norm_num
    rw [hsplit]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hlog10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num); linarith
    have hlogU : Real.log U ≤ U := Real.log_le_self hU0.le
    nlinarith [hlog2, hlog10, hlogU, hU1]
  refine ⟨Real.exp 3 - 3, c0 / (10 : ℝ)^6, c0, hT1ge, ?_, hc0pos, ?_, ?_⟩
  · exact div_pos hc0pos (by norm_num)
  · exact div_le_div_of_nonneg_left hc0pos.le (by norm_num) (by norm_num)
  · intro t ht
    have ht4 : 4 ≤ |t| := le_trans hT1ge ht
    have hy3 : 3 ≤ |t| + 3 := by linarith [abs_nonneg t]
    have hyexp : Real.exp 3 ≤ |t| + 3 := by linarith
    set ℓ : ℝ := Real.log (|t| + 3) with hℓ
    have hℓ3 : 3 ≤ ℓ := by
      rw [hℓ]
      have h := Real.log_le_log (Real.exp_pos 3) hyexp
      rwa [Real.log_exp] at h
    set L : ℝ := Real.log ℓ with hL
    have hL1 : 1 ≤ L := by
      rw [hL]
      exact one_le_log hℓ3
    have hℓ1 : 1 ≤ ℓ := by linarith
    have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ1
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have hL' : Real.log (Real.log (|t| + 3)) = L := by rw [hL, hℓ]
    have hlog2ℓ : Real.log (2 * ℓ) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hℓpos), hL]
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      linarith
    set x : ℝ := c0 / VKd (|t| + 3) with hx
    have hVKdpos : 0 < VKd (|t| + 3) := VKd_pos hy3
    have hxpos : 0 < x := by rw [hx]; exact div_pos hc0pos hVKdpos
    obtain ⟨hxL0, hVKd1, hlog2x0, hrpow0⟩ :=
      vk_inputs_self (c₀ := c0) (y := |t| + 3) hc0pos hc0le2 hℓ3 (by rw [hL']; exact hL1)
    rw [← hx, hL'] at hxL0 hlog2x0
    rw [← hx, hL', ← hℓ] at hrpow0
    have hxL_le : x * L ≤ c0 := hxL0
    have hlog2x : Real.log (2 / x) ≤ D * L := by rw [hD]; exact hlog2x0
    have hrpow : x ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = c0 ^ (3 / 2 : ℝ) / ℓ := hrpow0
    refine ⟨cl * (x * L), 2 * (cl * (x * L)), ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_pos hclpos (mul_pos hxpos hLpos)
    · have := mul_pos hclpos (mul_pos hxpos hLpos); linarith
    · have h1 : cl * (x * L) ≤ cl * c0 := mul_le_mul_of_nonneg_left hxL_le hclpos.le
      have h2 : cl * c0 = 1 / 100 := hclc0
      linarith
    · have h1 : (2 : ℝ) < cl * L := by
        have h1020 : (2 : ℝ) < (10 : ℝ)^20 := by norm_num
        have h2 : (10 : ℝ)^20 ≤ cl * L := by
          calc (10 : ℝ)^20 = (10 : ℝ)^20 * 1 := by ring
            _ ≤ cl * 1 := mul_le_mul_of_nonneg_right hclge (by norm_num)
            _ ≤ cl * L := mul_le_mul_of_nonneg_left hL1 hclpos.le
        linarith
      rw [show cl * (x * L) = (cl * L) * x by ring]
      exact mul_lt_mul_of_pos_right h1 hxpos
    · intro R hRa hRb
      have hapos : 0 < cl * (x * L) := mul_pos hclpos (mul_pos hxpos hLpos)
      have hRpos : 0 < R := lt_of_lt_of_le hapos hRa
      have hxLpos : 0 < x * L := mul_pos hxpos hLpos
      have hcoef : 2 * x / R ≤ 2 / (cl * L) := by
        have h1 : 2 * x / R ≤ 2 * x / (cl * (x * L)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hRa
        have h2 : 2 * x / (cl * (x * L)) = 2 / (cl * L) := by
          field_simp
        linarith
      have hcoef2 : 2 * x / (Real.pi * R) ≤ 2 / (Real.pi * cl * L) := by
        have h1 : 2 * x / (Real.pi * R) ≤ 2 * x / (Real.pi * (cl * (x * L))) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hRa Real.pi_pos.le)
        have h2 : 2 * x / (Real.pi * (cl * (x * L))) = 2 / (Real.pi * cl * L) := by
          field_simp
        linarith
      have hclL : (10 : ℝ)^20 ≤ cl * L := by
        calc (10 : ℝ)^20 = (10 : ℝ)^20 * 1 := by ring
          _ ≤ cl * 1 := mul_le_mul_of_nonneg_right hclge (by norm_num)
          _ ≤ cl * L := mul_le_mul_of_nonneg_left hL1 hclpos.le
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- (1)
        have hnn : 0 ≤ 2 * x / R := by positivity
        have hsq : (2 * x / R)^2 ≤ (2 / (cl * L))^2 := pow_le_pow_left₀ hnn hcoef 2
        have hb0 : 0 ≤ 2 / (cl * L) := by positivity
        have hsmall : 2 / (cl * L) ≤ 1 / 10 := by
          have h2 : (2 : ℝ) / (10 : ℝ)^20 ≤ 1 / 10 := by norm_num
          have h3 : 2 / (cl * L) ≤ 2 / (10 : ℝ)^20 :=
            div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by positivity) hclL
          linarith
        nlinarith [hsq, hsmall, hb0]
      · -- (2)
        have hc1 : (c0 / (10 : ℝ)^6) / c0 = 1 / (10 : ℝ)^6 := by
          field_simp
        rw [hc1]
        norm_num
      · -- (3)
        have hxc0 : x ≤ c0 := by
          rw [hx, div_le_iff₀ hVKdpos]
          simpa using mul_le_mul_of_nonneg_left hVKd1 hc0pos.le
        have h1 : (3 * C₀ / 4) * (2 * x) ≤ (3 * C₀ / 4) * (2 * c0) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        have h2 : C₀ * c0 ≤ 1 / ((10 : ℝ)^22) := hmul_le C₀ hCU
        have h3 : (3 * C₀ / 4) * (2 * c0) = (3 / 2) * (C₀ * c0) := by ring
        have h4 : (3 / 2 : ℝ) * (1 / ((10 : ℝ)^22)) ≤ 1 / 100 := by norm_num
        linarith
      · -- (4)
        have hℓt : Real.log (|t| + 3) + 1 ≤ 2 * ℓ := by rw [hℓ]; linarith
        have hℓ2t : Real.log (2 * |t| + 3) + 1 ≤ 2 * ℓ := by
          have hpos1 : (0 : ℝ) < 2 * |t| + 3 := by linarith [abs_nonneg t]
          have hq : 4 * (2 * |t| + 3) ≤ (|t| + 3)^2 := by nlinarith [abs_nonneg t, ht4]
          have h1 : Real.log (4 * (2 * |t| + 3)) ≤ Real.log ((|t| + 3)^2) :=
            Real.log_le_log (by positivity) hq
          rw [Real.log_mul (by norm_num) (ne_of_gt hpos1), Real.log_pow] at h1
          rw [← hℓ] at h1
          have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
            rw [Real.le_log_iff_exp_le (by norm_num)]
            linarith [Real.exp_one_lt_three]
          calc Real.log (2 * |t| + 3) + 1 ≤ Real.log (2 * |t| + 3) + Real.log 4 := by linarith
            _ = Real.log 4 + Real.log (2 * |t| + 3) := by ring
            _ ≤ 2 * ℓ := h1
        have hArc1 := arcCost_le_self (A := A) (B := B) (U := U) (D := D) (x := x)
          (τ := |t|) (R := R) (ℓ := ℓ) (L := L) hA hAU hB hRpos hxpos hℓ1 hL1
          (by simpa using hℓt) hlog2ℓ hlog2x
        have hArc2 := arcCost_le_self (A := A) (B := B) (U := U) (D := D) (x := x)
          (τ := 2 * |t|) (R := R) (ℓ := ℓ) (L := L) hA hAU hB hRpos hxpos hℓ1 hL1
          (by simpa using hℓ2t) hlog2ℓ hlog2x
        have hX : ArcCost A B (1 + x) |t| R + ArcCost A B (1 + x) (2 * |t|) R / 4
            ≤ (5 / 4) * (8 * D * L + 4 * Real.log U + 8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ) + 40 * L) := by
          linarith [hArc1, hArc2]
        have hstep1 : (2 * x / (Real.pi * R)) *
              (ArcCost A B (1 + x) |t| R + ArcCost A B (1 + x) (2 * |t|) R / 4)
            ≤ (2 * x / (Real.pi * R)) *
              ((5 / 4) * (8 * D * L + 4 * Real.log U + 8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ) + 40 * L)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
        have hb1 : (2 * x / (Real.pi * R)) * (8 * D * L) ≤ 16 * D / (Real.pi * cl) := by
          have h1 : (2 * x / (Real.pi * R)) * (8 * D * L) ≤ (2 / (Real.pi * cl * L)) * (8 * D * L) :=
            mul_le_mul_of_nonneg_right hcoef2 (by nlinarith [hD0, hLpos])
          have h2 : (2 / (Real.pi * cl * L)) * (8 * D * L) = 16 * D / (Real.pi * cl) := by
            field_simp
            try ring
          linarith
        have hb2 : (2 * x / (Real.pi * R)) * (4 * Real.log U) ≤ 8 * Real.log U / (Real.pi * cl) := by
          have hlogUnn : 0 ≤ Real.log U := Real.log_nonneg hU1
          have h1 : (2 * x / (Real.pi * R)) * (4 * Real.log U)
              ≤ (2 / (Real.pi * cl * L)) * (4 * Real.log U) :=
            mul_le_mul_of_nonneg_right hcoef2 (by linarith)
          have h2 : (2 / (Real.pi * cl * L)) * (4 * Real.log U) ≤ (2 / (Real.pi * cl)) * (4 * Real.log U) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (by simpa using mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ Real.pi * cl))
          have h3 : (2 / (Real.pi * cl)) * (4 * Real.log U) = 8 * Real.log U / (Real.pi * cl) := by ring
          linarith
        have hb3 : (2 * x / (Real.pi * R)) * (8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ))
            ≤ (32 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)) := by
          have hR32 : R ^ (3 / 2 : ℝ) = R * R ^ (1 / 2 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hRpos, Real.rpow_one]
          have heq : (2 * x / (Real.pi * R)) * (8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ))
              = (32 * B / Real.pi) * (x * R ^ (1 / 2 : ℝ) * ℓ) := by
            rw [hR32]
            field_simp
            try ring
          have hle : x * R ^ (1 / 2 : ℝ) * ℓ ≤ (2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ) := by
            have hR12 : R ^ (1 / 2 : ℝ) ≤ (2 * (cl * (x * L))) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hRpos.le hRb (by norm_num)
            have hstep : x * R ^ (1 / 2 : ℝ) * ℓ ≤ x * (2 * (cl * (x * L))) ^ (1 / 2 : ℝ) * ℓ := by
              have hh := mul_le_mul_of_nonneg_left hR12 hxpos.le
              have hh2 := mul_le_mul_of_nonneg_right hh hℓpos.le
              linarith
            have hrp : (2 * (cl * (x * L))) ^ (1 / 2 : ℝ)
                = (2 * cl) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) := by
              rw [show 2 * (cl * (x * L)) = (2 * cl) * (x * L) by ring,
                Real.mul_rpow (by positivity) (by positivity),
                Real.mul_rpow hxpos.le hLpos.le]
              ring
            have hx32 : x * ((2 * cl) ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ))
                = (2 * cl) ^ (1 / 2 : ℝ) * (x ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by
              have hx' : x * x ^ (1 / 2 : ℝ) = x ^ (3 / 2 : ℝ) := by
                have hh := Real.rpow_add hxpos (1 : ℝ) (1 / 2 : ℝ)
                rw [Real.rpow_one] at hh
                rw [← hh]
                norm_num
              rw [← hx']
              ring
            calc x * R ^ (1 / 2 : ℝ) * ℓ
                ≤ x * (2 * (cl * (x * L))) ^ (1 / 2 : ℝ) * ℓ := hstep
              _ = ((2 * cl) ^ (1 / 2 : ℝ) * (x ^ (3 / 2 : ℝ) * L ^ (1 / 2 : ℝ))) * ℓ := by rw [hrp, hx32]
              _ = (2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ) := by
                  rw [hrpow]
                  field_simp
          rw [heq]
          exact mul_le_mul_of_nonneg_left hle (by positivity)
        have hb4 : (2 * x / (Real.pi * R)) * (40 * L) ≤ 80 / (Real.pi * cl) := by
          have h1 : (2 * x / (Real.pi * R)) * (40 * L) ≤ (2 / (Real.pi * cl * L)) * (40 * L) :=
            mul_le_mul_of_nonneg_right hcoef2 (by positivity)
          have h2 : (2 / (Real.pi * cl * L)) * (40 * L) = 80 / (Real.pi * cl) := by
            field_simp
            try ring
          linarith
        have hnum1 : 20 * D / (Real.pi * cl) ≤ 1 / 400 := by
          have h1 : 20 * D ≤ 6000 * U^100 := by linarith [hDle, hUle, hU0]
          have h2 : 20 * D / (Real.pi * cl) ≤ 6000 * U^100 / (Real.pi * cl) :=
            div_le_div_of_nonneg_right h1 (by positivity)
          have h3 : 6000 * U^100 / (Real.pi * cl) = 6000 / (Real.pi * (10 : ℝ)^20) := by
            rw [hcl]
            field_simp
            try ring
          rw [h3] at h2
          have h4 : 6000 / (Real.pi * (10 : ℝ)^20) ≤ 1 / 400 :=
            div_pi_le_400 (by positivity) (by norm_num)
          linarith
        have hnum2 : 10 * Real.log U / (Real.pi * cl) ≤ 1 / 400 := by
          have hlogUnn : 0 ≤ Real.log U := Real.log_nonneg hU1
          have h1 : Real.log U ≤ U^100 := le_trans (Real.log_le_self hU0.le) hUle
          have h2 : 10 * Real.log U / (Real.pi * cl) ≤ 10 * U^100 / (Real.pi * cl) :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
          have h3 : 10 * U^100 / (Real.pi * cl) = 10 / (Real.pi * (10 : ℝ)^20) := by
            rw [hcl]
            field_simp
            try ring
          rw [h3] at h2
          have h4 : (10 : ℝ) / (Real.pi * (10 : ℝ)^20) ≤ 1 / 400 :=
            div_pi_le_400 (by positivity) (by norm_num)
          linarith
        have hnum3 : (40 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)) ≤ 1 / 400 := by
          have h1 : (2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ) ≤ c0 / 7 := by
            have heq1 : c0 ^ (3 / 2 : ℝ) = (c0^3) ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast c0 3, ← Real.rpow_mul hc0pos.le]
              norm_num
            have heq2 : (2 * cl) ^ (1 / 2 : ℝ) * (c0^3) ^ (1 / 2 : ℝ)
                = (2 * cl * c0^3) ^ (1 / 2 : ℝ) :=
              (Real.mul_rpow (x := 2 * cl) (y := c0^3) (z := (1 / 2 : ℝ))
                (by positivity) (by positivity)).symm
            have heq3 : 2 * cl * c0^3 = c0^2 / 50 := by
              have hcl' : cl = 1 / (100 * c0) := by
                rw [eq_div_iff (by positivity : (100 : ℝ) * c0 ≠ 0)]
                linarith [hclc0]
              rw [hcl']
              field_simp
              try ring
            have h4 : (c0^2 / 50) ^ (1 / 2 : ℝ) ≤ c0 / 7 := by
              have h5 : c0^2 / 50 ≤ (c0 / 7)^2 := by
                rw [show (c0 / 7)^2 = c0^2 / 49 by ring]
                exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
              calc (c0^2 / 50) ^ (1 / 2 : ℝ) = √(c0^2 / 50) := by rw [Real.sqrt_eq_rpow]
                _ ≤ √((c0 / 7)^2) := Real.sqrt_le_sqrt h5
                _ = c0 / 7 := Real.sqrt_sq (by positivity)
            calc (2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)
                = (2 * cl) ^ (1 / 2 : ℝ) * (c0^3) ^ (1 / 2 : ℝ) := by rw [heq1]
              _ = (2 * cl * c0^3) ^ (1 / 2 : ℝ) := heq2
              _ = (c0^2 / 50) ^ (1 / 2 : ℝ) := by rw [heq3]
              _ ≤ c0 / 7 := h4
          have h2 : (40 * B / Real.pi) * (c0 / 7) ≤ 1 / 400 := by
            have h5 : B * c0 ≤ 1 / ((10 : ℝ)^22) := hmul_le B hBU
            have h6 : (40 * B / Real.pi) * (c0 / 7) = (40 / 7) * (B * c0) / Real.pi := by ring
            rw [h6]
            have h7 : (40 / 7) * (B * c0) ≤ (40 / 7) * (1 / ((10 : ℝ)^22)) :=
              mul_le_mul_of_nonneg_left h5 (by norm_num)
            have h8 : (40 / 7) * (B * c0) / Real.pi ≤ (40 / 7) * (1 / ((10 : ℝ)^22)) / Real.pi :=
              div_le_div_of_nonneg_right h7 Real.pi_pos.le
            have h9 : (40 / 7) * (1 / ((10 : ℝ)^22)) / Real.pi ≤ 1 / 400 := by
              have he : (40 / 7) * (1 / ((10 : ℝ)^22)) / Real.pi
                  = (40 / 7) / (Real.pi * (10 : ℝ)^22) := by
                field_simp
                try ring
              rw [he]
              exact div_pi_le_400 (by positivity) (by norm_num)
            linarith
          exact le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        have hnum4 : 100 / (Real.pi * cl) ≤ 1 / 400 := by
          have h1 : 100 / (Real.pi * cl) ≤ 100 / (Real.pi * (10 : ℝ)^20) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (by have := mul_le_mul_of_nonneg_left hclge (le_of_lt Real.pi_pos)
                  simpa [mul_comm] using this)
          have h2 : 100 / (Real.pi * (10 : ℝ)^20) ≤ 1 / 400 :=
            div_pi_le_400 (by positivity) (by norm_num)
          linarith
        have hsum1 : (5 / 4) * ((2 * x / (Real.pi * R)) * (8 * D * L)) ≤ 20 * D / (Real.pi * cl) := by
          have := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0 : ℝ) ≤ 5 / 4)
          have e : (5 / 4) * (16 * D / (Real.pi * cl)) = 20 * D / (Real.pi * cl) := by ring
          linarith [e]
        have hsum2 : (5 / 4) * ((2 * x / (Real.pi * R)) * (4 * Real.log U))
            ≤ 10 * Real.log U / (Real.pi * cl) := by
          have := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ 5 / 4)
          have e : (5 / 4) * (8 * Real.log U / (Real.pi * cl)) = 10 * Real.log U / (Real.pi * cl) := by ring
          linarith [e]
        have hsum3 : (5 / 4) * ((2 * x / (Real.pi * R)) * (8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ)))
            ≤ (40 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)) := by
          have := mul_le_mul_of_nonneg_left hb3 (by norm_num : (0 : ℝ) ≤ 5 / 4)
          have e : (5 / 4) * ((32 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)))
              = (40 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)) := by ring
          linarith [e]
        have hsum4 : (5 / 4) * ((2 * x / (Real.pi * R)) * (40 * L)) ≤ 100 / (Real.pi * cl) := by
          have := mul_le_mul_of_nonneg_left hb4 (by norm_num : (0 : ℝ) ≤ 5 / 4)
          have e : (5 / 4) * (80 / (Real.pi * cl)) = 100 / (Real.pi * cl) := by ring
          linarith [e]
        calc (2 * x / (Real.pi * R)) *
              (ArcCost A B (1 + x) |t| R + ArcCost A B (1 + x) (2 * |t|) R / 4)
            ≤ (2 * x / (Real.pi * R)) *
              ((5 / 4) * (8 * D * L + 4 * Real.log U + 8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ) + 40 * L)) := hstep1
          _ = (5 / 4) * ((2 * x / (Real.pi * R)) * (8 * D * L))
              + (5 / 4) * ((2 * x / (Real.pi * R)) * (4 * Real.log U))
              + (5 / 4) * ((2 * x / (Real.pi * R)) * (8 * B * R ^ (3 / 2 : ℝ) * (2 * ℓ)))
              + (5 / 4) * ((2 * x / (Real.pi * R)) * (40 * L)) :=
              five_four_sum_identity
          _ ≤ 20 * D / (Real.pi * cl) + 10 * Real.log U / (Real.pi * cl)
              + (40 * B / Real.pi) * ((2 * cl) ^ (1 / 2 : ℝ) * c0 ^ (3 / 2 : ℝ)) + 100 / (Real.pi * cl) := by
              linarith [hsum1, hsum2, hsum3, hsum4]
          _ ≤ 1 / 100 := by linarith [hnum1, hnum2, hnum3, hnum4]

end Work.BMF
