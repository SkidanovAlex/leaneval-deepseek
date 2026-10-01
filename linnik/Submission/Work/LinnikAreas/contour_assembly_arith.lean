import Mathlib

/-!
# `contour_assembly_arith`

Arithmetic core of the contour assembly for Linnik's theorem (Heath-Brown 1992).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.LinnikAreas

/-- For `T ≥ 1` and `0 ≤ s ≤ 2`, `(1+T)^s / T^2 ≤ 2^s`. -/
theorem aux_rpow_inv_sq_le {T s : ℝ} (hT : 1 ≤ T) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    (1 + T) ^ s / T ^ 2 ≤ 2 ^ s := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hT2pos : (0:ℝ) < T^2 := by positivity
  rw [div_le_iff₀ hT2pos]
  have h2T : (1:ℝ) + T ≤ 2 * T := by linarith
  have hnum : (1+T)^s ≤ (2*T)^s := Real.rpow_le_rpow (by positivity) h2T hs0
  have hsplit : (2*T)^s = 2^s * T^s := Real.mul_rpow (by norm_num) (le_of_lt hTpos)
  rw [hsplit] at hnum
  have hTexp : T^s ≤ T^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hT hs2
  calc (1+T)^s ≤ 2^s * T^s := hnum
    _ ≤ 2^s * T^2 := by
        rw [← Real.rpow_natCast T 2]
        exact mul_le_mul_of_nonneg_left hTexp (Real.rpow_nonneg (by norm_num) s)

/-- For `y ≥ 1`, `log y ≤ 4 y^{1/4}`. -/
theorem aux_log_le_four {y : ℝ} (hy : 1 ≤ y) : Real.log y ≤ 4 * y ^ ((1:ℝ)/4) := by
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  calc Real.log y ≤ y ^ ((1:ℝ)/4) / (1/4) := Real.log_le_rpow_div hy0 (by norm_num)
    _ = 4 * y ^ ((1:ℝ)/4) := by ring

/-- For `0 < x`, `3/4 ≤ β < 1`, we have `x^{1-β} ≤ x + x^{5/8-β}`. -/
theorem aux_beta {β x : ℝ} (hβ1 : 3/4 ≤ β) (hβ2 : β < 1) (hx : 0 < x) :
    x^((1-β:ℝ)) ≤ x + x^((5/8-β:ℝ)) := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · have hle : x^((1-β:ℝ)) ≤ x^((5/8-β:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx (le_of_lt hx1) (by linarith)
    linarith [Real.rpow_nonneg (le_of_lt hx) (5/8-β)]
  · have hxge : (1:ℝ) ≤ x := hx1
    have h : x^((1-β:ℝ)) ≤ x := by
      have : x^((1-β:ℝ)) ≤ x^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hxge (by linarith)
      rwa [Real.rpow_one] at this
    linarith [Real.rpow_nonneg (le_of_lt hx) (5/8-β)]

/-- Pure arithmetic assembly: given the term-wise bounds, combine them. -/
private lemma core_arith {KV KH K a b c d e f g n mR P Q : ℝ}
    (hKV : 0 < KV) (hKH : 0 < KH) (hK : KV + 70*KH ≤ K)
    (hP : P = a*b) (hQ : Q = n*d*mR)
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hcad : c*a*d ≤ Q) (hcab : c*a*b ≤ 2*P)
    (hcfd : c*f*d ≤ 2*Q) (hcgd : c*g*d ≤ 8*Q)
    (hcfb : c*f*b ≤ 16*P) (hcgb : c*g*b ≤ 16*P)
    (hce : c*(f+g)*e ≤ c*(f+g)*(d+b)) :
    KV*P + KH*(c*(a*(d+b) + (f+g)*(d+e))) ≤ K*(P+Q) := by
  nlinarith [hKV, hKH, hK, hP, hQ, hP0, hQ0, hcad, hcab, hcfd, hcgd, hcfb, hcgb, hce]

theorem contour_assembly_arith (KV KH : ℝ) (hKV : 0 < KV) (hKH : 0 < KH) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ} [NeZero N] {β x T : ℝ},
      3 / 4 ≤ β → β < 1 → 0 < x → 1 ≤ T →
      KV * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ)))
        + KH * ((1 + T) ^ ((11 : ℝ) / 16) / T ^ 2 *
            ((N : ℝ) ^ ((1 : ℝ) / 4) * (x + x ^ ((5 / 8 - β : ℝ)))
              + (Real.log (2 * N) + Real.log (2 + T)) * (x + x ^ ((1 - β : ℝ)))))
        ≤ K * ((N : ℝ) ^ ((1 : ℝ) / 4) * x ^ ((5 / 8 - β : ℝ))
                + (N : ℝ) * x * (1 + T) ^ ((23 : ℝ) / 16) / T ^ 2) := by
  refine ⟨KV + 100*KH + 1, by linarith, ?_⟩
  intro N _ β x T hβ1 hβ2 hx hT
  have hK70 : KV + 70*KH ≤ KV + 100*KH + 1 := by linarith only [hKH]
  set Q : ℝ := (N:ℝ)*x*(1+T)^((23:ℝ)/16)/T^2 with hQ
  set a : ℝ := (N:ℝ)^((1:ℝ)/4) with ha
  set b : ℝ := x^((5/8-β:ℝ)) with hb
  set c : ℝ := (1+T)^((11:ℝ)/16)/T^2 with hc
  set d : ℝ := x with hd
  set e : ℝ := x^((1-β:ℝ)) with he
  set f : ℝ := Real.log (2*N) with hf
  set g : ℝ := Real.log (2+T) with hg
  set n : ℝ := (N:ℝ) with hn
  set P : ℝ := a*b with hP
  set mR : ℝ := (1+T)^((23:ℝ)/16)/T^2 with hm
  set W : ℝ := (1+T)^((3:ℝ)/4) with hW
  have hN1 : (1:ℕ) ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact hN1r
  have hn0 : (0:ℝ) ≤ n := le_trans zero_le_one hn1
  have h1Tpos : (0:ℝ) < 1+T := by linarith
  have ha1 : (1:ℝ) ≤ a := by rw [ha]; exact Real.one_le_rpow hn1 (by norm_num)
  have ha0 : (0:ℝ) ≤ a := le_trans zero_le_one ha1
  have hb0 : (0:ℝ) ≤ b := by rw [hb]; exact Real.rpow_nonneg (le_of_lt hx) _
  have hc0 : (0:ℝ) ≤ c := by
    rw [hc]; exact div_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
  have hd0 : (0:ℝ) < d := hx
  have hf0 : (0:ℝ) ≤ f := by rw [hf]; apply Real.log_nonneg; linarith [hn1]
  have hg0 : (0:ℝ) ≤ g := by rw [hg]; apply Real.log_nonneg; linarith
  have hW1 : (1:ℝ) ≤ W := by rw [hW]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hP0 : (0:ℝ) ≤ P := by rw [hP]; exact mul_nonneg ha0 hb0
  have hQ0 : (0:ℝ) ≤ Q := by
    rw [hQ]
    exact div_nonneg (mul_nonneg (mul_nonneg hn0 (le_of_lt hx))
      (Real.rpow_nonneg (by linarith) _)) (by positivity)
  have hQm : Q = n*d*mR := by rw [hQ, hm]; ring
  have ha_le_nW : a ≤ n*W := by
    rw [ha, hW]
    have h1 : n^((1:ℝ)/4) ≤ n := Real.rpow_le_self_of_one_le hn1 (by norm_num)
    have h2 : n*1 ≤ n*((1+T)^((3:ℝ)/4)) :=
      mul_le_mul_of_nonneg_left (Real.one_le_rpow (by linarith) (by norm_num)) hn0
    linarith
  have hmW : mR = c*W := by
    rw [hm, hc, hW, show (23:ℝ)/16 = (11:ℝ)/16 + 3/4 by norm_num, Real.rpow_add h1Tpos]
    ring
  have hc2 : c ≤ 2 := by
    rw [hc]
    calc (1+T)^((11:ℝ)/16)/T^2 ≤ (2:ℝ)^((11:ℝ)/16) :=
          aux_rpow_inv_sq_le hT (by norm_num) (by norm_num)
      _ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hc_a_le : c*a ≤ n*mR := by
    calc c*a ≤ c*(n*W) := mul_le_mul_of_nonneg_left ha_le_nW hc0
      _ = n*(c*W) := by ring
      _ = n*mR := by rw [← hmW]
  have hcad : c*a*d ≤ Q := by
    rw [hQm]
    calc c*a*d ≤ (n*mR)*d := mul_le_mul_of_nonneg_right hc_a_le (le_of_lt hd0)
      _ = n*d*mR := by ring
  have hcab : c*a*b ≤ 2*P := by
    rw [hP]
    calc c*a*b ≤ (2*a)*b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 ha0) hb0
      _ = 2*(a*b) := by ring
  have hf_le_2n : f ≤ 2*n := by rw [hf]; exact Real.log_le_self (by positivity)
  have hf_le_8a : f ≤ 8*a := by
    rw [hf, ha]
    have hy1 : (1:ℝ) ≤ 2*n := by linarith only [hn1]
    have h1 := aux_log_le_four hy1
    have h2 : (2*n)^((1:ℝ)/4) = 2^((1:ℝ)/4)*n^((1:ℝ)/4) :=
      Real.mul_rpow (by norm_num) hn0
    rw [h2] at h1
    have h4 : (2:ℝ)^((1:ℝ)/4) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have h5 : (0:ℝ) ≤ n^((1:ℝ)/4) := Real.rpow_nonneg hn0 _
    have h6 : 4*(2^((1:ℝ)/4)*n^((1:ℝ)/4)) ≤ 8*n^((1:ℝ)/4) := by
      have hh := mul_le_mul_of_nonneg_right h4 h5
      linarith only [hh]
    linarith only [h1, h6]
  have hg_le_8nW : g ≤ 8*n*W := by
    rw [hg, hW]
    have hA : Real.log (2+T) ≤ 4*(2+T)^((1:ℝ)/4) := aux_log_le_four (by linarith)
    have hB : (2+T)^((1:ℝ)/4) ≤ (2*(1+T))^((1:ℝ)/4) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hC : (2*(1+T))^((1:ℝ)/4) = 2^((1:ℝ)/4)*(1+T)^((1:ℝ)/4) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hD : (1+T)^((1:ℝ)/4) ≤ (1+T)^((3:ℝ)/4) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hE : (2:ℝ)^((1:ℝ)/4) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hpos1 : (0:ℝ) ≤ (1+T)^((1:ℝ)/4) := Real.rpow_nonneg (by linarith) _
    have hstep : 4*(2*(1+T))^((1:ℝ)/4) ≤ 8*(1+T)^((3:ℝ)/4) := by
      rw [hC]
      have hh : 2^((1:ℝ)/4)*(1+T)^((1:ℝ)/4) ≤ 2*(1+T)^((3:ℝ)/4) :=
        mul_le_mul hE hD hpos1 (by norm_num)
      linarith only [hh]
    have hWnn : (0:ℝ) ≤ (1+T)^((3:ℝ)/4) := Real.rpow_nonneg (by linarith) _
    have hNW : (1+T)^((3:ℝ)/4) ≤ n*(1+T)^((3:ℝ)/4) := by
      calc (1+T)^((3:ℝ)/4) = 1*(1+T)^((3:ℝ)/4) := by ring
        _ ≤ n*(1+T)^((3:ℝ)/4) := mul_le_mul_of_nonneg_right hn1 hWnn
    calc Real.log (2+T) ≤ 4*(2+T)^((1:ℝ)/4) := hA
      _ ≤ 4*(2*(1+T))^((1:ℝ)/4) := by linarith only [hB]
      _ ≤ 8*(1+T)^((3:ℝ)/4) := hstep
      _ ≤ 8*(n*(1+T)^((3:ℝ)/4)) := by linarith only [hNW]
      _ = 8*n*(1+T)^((3:ℝ)/4) := by ring
  have hcg_le : c*g ≤ 16 := by
    have hA : Real.log (2+T) ≤ 4*(2+T)^((1:ℝ)/4) := aux_log_le_four (by linarith)
    have hB : (2+T)^((1:ℝ)/4) ≤ (2*(1+T))^((1:ℝ)/4) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hC : (2*(1+T))^((1:ℝ)/4) = 2^((1:ℝ)/4)*(1+T)^((1:ℝ)/4) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hsplit : (1+T)^((11:ℝ)/16)*(1+T)^((1:ℝ)/4) = (1+T)^((15:ℝ)/16) := by
      rw [← Real.rpow_add h1Tpos]; norm_num
    have hD : (1+T)^((15:ℝ)/16)/T^2 ≤ (2:ℝ)^((15:ℝ)/16) :=
      aux_rpow_inv_sq_le hT (by norm_num) (by norm_num)
    have hF : (4:ℝ)*2^((1:ℝ)/4)*2^((15:ℝ)/16) ≤ 16 := by
      have h4 : (2:ℝ)^((1:ℝ)/4) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      have h5 : (2:ℝ)^((15:ℝ)/16) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      have h6 : (2:ℝ)^((1:ℝ)/4)*(2:ℝ)^((15:ℝ)/16) ≤ 4 := by
        calc (2:ℝ)^((1:ℝ)/4)*(2:ℝ)^((15:ℝ)/16) ≤ 2*2 :=
              mul_le_mul h4 h5 (Real.rpow_nonneg (by norm_num) _) (by norm_num)
          _ = 4 := by norm_num
      nlinarith only [h6]
    calc c*g = ((1+T)^((11:ℝ)/16)/T^2)*Real.log (2+T) := by rw [hc, hg]
      _ ≤ ((1+T)^((11:ℝ)/16)/T^2)*(4*(2+T)^((1:ℝ)/4)) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ ((1+T)^((11:ℝ)/16)/T^2)*(4*(2*(1+T))^((1:ℝ)/4)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hB]) (by positivity)
      _ = 4*2^((1:ℝ)/4) * ((1+T)^((11:ℝ)/16)*(1+T)^((1:ℝ)/4)/T^2) := by rw [hC]; ring
      _ = 4*2^((1:ℝ)/4) * ((1+T)^((15:ℝ)/16)/T^2) := by rw [hsplit]
      _ ≤ 4*2^((1:ℝ)/4) * 2^((15:ℝ)/16) :=
          mul_le_mul_of_nonneg_left hD (by positivity)
      _ ≤ 16 := hF
  have hcg_le16a : c*g ≤ 16*a := by
    have h16a : (16:ℝ) ≤ 16*a := by nlinarith only [ha1]
    linarith only [hcg_le, h16a]
  have hcf_le : c*f ≤ 16*a := by
    have h1 : c*f ≤ 2*f := mul_le_mul_of_nonneg_right hc2 hf0
    have h2 : 2*f ≤ 16*a := by linarith only [hf_le_8a]
    linarith only [h1, h2]
  have hcgb : c*g*b ≤ 16*P := by
    rw [hP]
    calc c*g*b ≤ (16*a)*b := mul_le_mul_of_nonneg_right hcg_le16a hb0
      _ = 16*(a*b) := by ring
  have hcfb : c*f*b ≤ 16*P := by
    rw [hP]
    calc c*f*b ≤ (16*a)*b := mul_le_mul_of_nonneg_right hcf_le hb0
      _ = 16*(a*b) := by ring
  have hf_le_2nW : f ≤ 2*n*W := by
    have hh : 2*n*1 ≤ 2*n*W := mul_le_mul_of_nonneg_left hW1 (by positivity)
    linarith only [hf_le_2n, hh]
  have hcfd : c*f*d ≤ 2*Q := by
    rw [hQm]
    have h1 : c*f ≤ 2*(n*mR) := by
      calc c*f ≤ c*(2*n*W) := mul_le_mul_of_nonneg_left hf_le_2nW hc0
        _ = 2*(n*(c*W)) := by ring
        _ = 2*(n*mR) := by rw [← hmW]
    calc c*f*d ≤ (2*(n*mR))*d := mul_le_mul_of_nonneg_right h1 (le_of_lt hd0)
      _ = 2*(n*d*mR) := by ring
  have hcgd : c*g*d ≤ 8*Q := by
    rw [hQm]
    have h1 : c*g ≤ 8*(n*mR) := by
      calc c*g ≤ c*(8*n*W) := mul_le_mul_of_nonneg_left hg_le_8nW hc0
        _ = 8*(n*(c*W)) := by ring
        _ = 8*(n*mR) := by rw [← hmW]
    calc c*g*d ≤ (8*(n*mR))*d := mul_le_mul_of_nonneg_right h1 (le_of_lt hd0)
      _ = 8*(n*d*mR) := by ring
  have he_le : e ≤ d + b := by
    rw [he, hb]; exact aux_beta hβ1 hβ2 hx
  have hfg0 : (0:ℝ) ≤ f + g := by linarith only [hf0, hg0]
  have hce : c*(f+g)*e ≤ c*(f+g)*(d+b) :=
    mul_le_mul_of_nonneg_left he_le (mul_nonneg hc0 hfg0)
  exact core_arith (KV := KV) (KH := KH) (K := KV + 100*KH + 1)
    (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)
    (n := n) (mR := mR) (P := P) (Q := Q)
    hKV hKH hK70 hP hQm hP0 hQ0 hcad hcab hcfd hcgd hcfb hcgb hce

end Work.LinnikAreas
