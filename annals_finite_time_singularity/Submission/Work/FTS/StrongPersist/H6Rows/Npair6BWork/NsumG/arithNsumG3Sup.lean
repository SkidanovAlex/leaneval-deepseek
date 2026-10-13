import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG

set_option maxHeartbeats 1600000

/-- Product monotonicity for four nonnegative factors. -/
private lemma four_le {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) :
    a1 * a2 * a3 * a4 ≤ b1 * b2 * b3 * b4 := by
  have h12 : a1 * a2 ≤ b1 * b2 := mul_le_mul h1 h2 ha2 hb1
  have h34 : a3 * a4 ≤ b3 * b4 := mul_le_mul h3 h4 ha4 hb3
  have h0 : 0 ≤ a3 * a4 := mul_nonneg ha3 ha4
  have hb : 0 ≤ b1 * b2 := mul_nonneg hb1 hb2
  calc a1 * a2 * a3 * a4 = (a1 * a2) * (a3 * a4) := by ring
    _ ≤ (b1 * b2) * (b3 * b4) := mul_le_mul h12 h34 h0 hb
    _ = b1 * b2 * b3 * b4 := by ring

/-- **The coarse `α^{-10}`-arithmetic of the level-six `N`-row (sup-price variant).**

From the sharp `α^{-3}`-bound `hX` on `X` and the price bounds
`KQ ≤ kq·α`, `K0 ≤ k0·α^{-1/2}(1+|Ce|)(1+M)`, `K4 ≤ k4(1+|Ce|)M`, `K6 ≤ k6(1+|Ce|)H`
with `0 < α ≤ 1` and all the small parameters nonnegative, one gets the
`α^{-10}(1+|Ce|+|Cs|)⁴(1+M)⁴(1+S)`-form of the row.  The losses are
`α^{-3} ↦ α^{-3}·α^{-7} = α^{-10}` (only the `α^{-1/2}` of `K0` needs a fractional
power, and `α^{-1/2} ≤ α^{-7}`), `1+|Ce| ↦ (1+|Ce|+|Cs|)⁴` (and `≤ D⁴` absorbs the
`α^{-7}·D`-factor of the pointwise price), `1+M ↦ (1+M)⁴`, and
`(1+H)² ≤ 16(1+S)` for `S = H²` (the number `16` is the `15 + 15H² - 2H > 0` room). -/
theorem arithNsumG3Sup {X α M Ce Cs S H C0 kq k0 k4 k6 KQ K0 K4 K6 : ℝ}
    (hX : X ≤ C0 * α ^ (-(3 : ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H))
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 ≤ C0)
    (hSH : S = H ^ 2) (hH0 : 0 ≤ H) (hS0 : 0 ≤ S)
    (hkq : 0 ≤ kq) (hk0 : 0 ≤ k0) (hk4 : 0 ≤ k4) (hk6 : 0 ≤ k6)
    (hK0 : 0 ≤ K0) (hK4 : 0 ≤ K4) (hK6 : 0 ≤ K6) (hM : 0 ≤ M)
    (hKQ : KQ ≤ kq * α)
    (hp0 : K0 ≤ k0 * α ^ (-(1 / 2 : ℝ)) * (1 + |Ce|) * (1 + M))
    (hp4 : K4 ≤ k4 * (1 + |Ce|) * M)
    (hp6 : K6 ≤ k6 * (1 + |Ce|) * H) :
    X ≤ (16 * (1 + kq) * (1 + k0 + k4 + k6) * C0) * α ^ (-(10 : ℝ))
          * (1 + |Ce| + |Cs|) ^ 4 * (1 + M) ^ 4 * (1 + S) := by
  have hα3 : 0 ≤ α ^ (-(3:ℝ)) := Real.rpow_nonneg hα0.le _
  have hα7 : 0 ≤ α ^ (-(7:ℝ)) := Real.rpow_nonneg hα0.le _
  have hα10 : 0 ≤ α ^ (-(10:ℝ)) := Real.rpow_nonneg hα0.le _
  have h7ge1 : 1 ≤ α ^ (-(7:ℝ)) := by
    rw [Real.rpow_neg hα0.le, ← Real.inv_rpow hα0.le]
    exact Real.one_le_rpow ((one_le_inv₀ hα0).mpr hα1) (by norm_num : (0:ℝ) ≤ 7)
  have hpow : α ^ (-(3:ℝ)) * α ^ (-(7:ℝ)) = α ^ (-(10:ℝ)) := by
    rw [← Real.rpow_add hα0]; norm_num
  have hhalf : α ^ (-(1/2:ℝ)) ≤ α ^ (-(7:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have one_le_prod : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    have h := mul_le_mul ha hb (zero_le_one) (le_trans zero_le_one ha)
    simpa using h
  set D : ℝ := 1 + |Ce| + |Cs| with hDdef
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith [abs_nonneg Ce, abs_nonneg Cs]
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hCeD : 1 + |Ce| ≤ D := by rw [hDdef]; linarith [abs_nonneg Cs]
  have h1M0 : 0 ≤ 1 + M := by linarith
  have h1H0 : 0 ≤ 1 + H := by linarith
  have h1M1 : 1 ≤ 1 + M := by linarith
  have h1H1 : 1 ≤ 1 + H := by linarith
  have hKQle : KQ ≤ kq := by
    calc KQ ≤ kq * α := hKQ
      _ ≤ kq * 1 := mul_le_mul_of_nonneg_left hα1 hkq
      _ = kq := by ring
  have h1KQ : 1 + KQ ≤ 1 + kq := by linarith
  set E : ℝ := α ^ (-(7:ℝ)) * D * (1 + M) * (1 + H) with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hα7 hD0) h1M0) h1H0
  have hE1 : 1 ≤ E := by
    rw [hEdef]
    have h := one_le_prod (α ^ (-(7:ℝ))) (D * (1 + M) * (1 + H)) h7ge1
      (one_le_prod (D * (1 + M)) (1 + H)
        (one_le_prod D (1 + M) hD1 h1M1) h1H1)
    simpa only [mul_assoc] using h
  have hK0b : K0 ≤ k0 * E := by
    have h1 : α ^ (-(1/2:ℝ)) * (1 + |Ce|) * (1 + M) ≤ E := by
      rw [hEdef]
      have ha : α ^ (-(1/2:ℝ)) * (1 + |Ce|) ≤ α ^ (-(7:ℝ)) * D :=
        mul_le_mul hhalf hCeD (by positivity) hα7
      have hb : α ^ (-(1/2:ℝ)) * (1 + |Ce|) * (1 + M) ≤ α ^ (-(7:ℝ)) * D * (1 + M) :=
        mul_le_mul_of_nonneg_right ha h1M0
      exact le_trans hb (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hα7 hD0) h1M0) h1H1)
    calc K0 ≤ k0 * α ^ (-(1/2:ℝ)) * (1 + |Ce|) * (1 + M) := hp0
      _ = k0 * (α ^ (-(1/2:ℝ)) * (1 + |Ce|) * (1 + M)) := by ring
      _ ≤ k0 * E := mul_le_mul_of_nonneg_left h1 hk0
  have hK4b : K4 ≤ k4 * E := by
    have h1 : (1 + |Ce|) * M ≤ E := by
      rw [hEdef]
      have s1 : (1 + |Ce|) * M ≤ D * M := mul_le_mul_of_nonneg_right hCeD hM
      have s2 : D * M ≤ D * (1 + M) := mul_le_mul_of_nonneg_left (by linarith) hD0
      have s3 : D * (1 + M) ≤ α ^ (-(7:ℝ)) * D * (1 + M) := by
        have h := mul_le_mul_of_nonneg_right h7ge1 (mul_nonneg hD0 h1M0)
        calc D * (1 + M) = 1 * (D * (1 + M)) := by ring
          _ ≤ α ^ (-(7:ℝ)) * (D * (1 + M)) := h
          _ = α ^ (-(7:ℝ)) * D * (1 + M) := by ring
      have s4 : α ^ (-(7:ℝ)) * D * (1 + M) ≤ α ^ (-(7:ℝ)) * D * (1 + M) * (1 + H) :=
        le_mul_of_one_le_right (mul_nonneg (mul_nonneg hα7 hD0) h1M0) h1H1
      linarith
    calc K4 ≤ k4 * (1 + |Ce|) * M := hp4
      _ = k4 * ((1 + |Ce|) * M) := by ring
      _ ≤ k4 * E := mul_le_mul_of_nonneg_left h1 hk4
  have hK6b : K6 ≤ k6 * E := by
    have h1 : (1 + |Ce|) * H ≤ E := by
      rw [hEdef]
      have s1 : (1 + |Ce|) * H ≤ D * H := mul_le_mul_of_nonneg_right hCeD hH0
      have s2 : D * H ≤ D * (1 + H) := mul_le_mul_of_nonneg_left (by linarith) hD0
      have s3 : D * (1 + H) ≤ α ^ (-(7:ℝ)) * D * (1 + H) := by
        have h := mul_le_mul_of_nonneg_right h7ge1 (mul_nonneg hD0 h1H0)
        calc D * (1 + H) = 1 * (D * (1 + H)) := by ring
          _ ≤ α ^ (-(7:ℝ)) * (D * (1 + H)) := h
          _ = α ^ (-(7:ℝ)) * D * (1 + H) := by ring
      have s4 : α ^ (-(7:ℝ)) * D * (1 + H) ≤ α ^ (-(7:ℝ)) * D * (1 + M) * (1 + H) := by
        have h := mul_le_mul_of_nonneg_right h1M1 (mul_nonneg (mul_nonneg hα7 hD0) h1H0)
        calc α ^ (-(7:ℝ)) * D * (1 + H) = 1 * (α ^ (-(7:ℝ)) * D * (1 + H)) := by ring
          _ ≤ (1 + M) * (α ^ (-(7:ℝ)) * D * (1 + H)) := h
          _ = α ^ (-(7:ℝ)) * D * (1 + M) * (1 + H) := by ring
      linarith
    calc K6 ≤ k6 * (1 + |Ce|) * H := hp6
      _ = k6 * ((1 + |Ce|) * H) := by ring
      _ ≤ k6 * E := mul_le_mul_of_nonneg_left h1 hk6
  have hKsum : 1 + K0 + K4 + K6 ≤ (1 + k0 + k4 + k6) * E := by
    have hsum : K0 + K4 + K6 ≤ (k0 + k4 + k6) * E := by
      have h := add_le_add (add_le_add hK0b hK4b) hK6b
      linarith
    linarith [hsum, hE1]
  have hpaira : α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6)
      ≤ (1 + k0 + k4 + k6) * D * (1+M) * (1+H) * α ^ (-(10:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hKsum hα3
    have heq : α ^ (-(3:ℝ)) * ((1 + k0 + k4 + k6) * E)
        = (1 + k0 + k4 + k6) * D * (1+M) * (1+H) * α ^ (-(10:ℝ)) := by
      rw [hEdef, ← hpow]; ring
    rw [heq] at h
    exact h
  have hP0 : 0 ≤ C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hα3) (by linarith)) h1M0) h1H0
  have hPbound : C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)
      ≤ C0 * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2 := by
    have hstep := mul_le_mul_of_nonneg_right hpaira (mul_nonneg h1M0 h1H0)
    have hstep2 := mul_le_mul_of_nonneg_left hstep hC0
    calc C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)
        = C0 * (α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * ((1 + M) * (1 + H))) := by ring
      _ ≤ C0 * ((1 + k0 + k4 + k6) * D * (1 + M) * (1 + H) * α ^ (-(10:ℝ))
            * ((1 + M) * (1 + H))) := hstep2
      _ = C0 * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2 := by ring
  have hZ : C0 * α ^ (-(3:ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)
      ≤ C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2 := by
    have hre : C0 * α ^ (-(3:ℝ)) * (1 + KQ) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)
        = (1 + KQ) * (C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)) := by ring
    rw [hre]
    calc (1 + KQ) * (C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H))
        ≤ (1 + kq) * (C0 * α ^ (-(3:ℝ)) * (1 + K0 + K4 + K6) * (1 + M) * (1 + H)) :=
          mul_le_mul_of_nonneg_right h1KQ hP0
      _ ≤ (1 + kq) * (C0 * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2) :=
          mul_le_mul_of_nonneg_left hPbound (by linarith)
      _ = C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2 := by ring
  have hHsq : (1 + H)^2 ≤ 16 * (1 + S) := by nlinarith [sq_nonneg (H - 1), sq_nonneg H]
  have hD4 : D ≤ D^4 := by
    have h := pow_le_pow_right₀ hD1 (by norm_num : (1:ℕ) ≤ 4)
    simpa using h
  have hM4 : (1 + M)^2 ≤ (1 + M)^4 := by
    have h := pow_le_pow_right₀ h1M1 (by norm_num : (2:ℕ) ≤ 4)
    simpa using h
  have hK0c : 0 ≤ C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0 (by linarith)) (by linarith)) hα10
  have hstage2 : C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D
        * (1 + M)^2 * (1 + H)^2
      ≤ (16 * (1 + kq) * (1 + k0 + k4 + k6) * C0) * α ^ (-(10:ℝ)) * D^4 * (1 + M)^4
          * (1 + S) := by
    calc C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ)) * D * (1 + M)^2 * (1 + H)^2
        = (C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ))) * D * (1 + M)^2
            * (1 + H)^2 := by ring
      _ ≤ (C0 * (1 + kq) * (1 + k0 + k4 + k6) * α ^ (-(10:ℝ))) * D^4 * (1 + M)^4
            * (16 * (1 + S)) :=
          four_le (le_refl _) hD4 hM4 hHsq hD0 (sq_nonneg _) (sq_nonneg _) hK0c
            (pow_nonneg hD0 4) (pow_nonneg h1M0 4)
      _ = (16 * (1 + kq) * (1 + k0 + k4 + k6) * C0) * α ^ (-(10:ℝ)) * D^4 * (1 + M)^4
            * (1 + S) := by ring
  exact le_trans hX (le_trans hZ hstage2)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG
