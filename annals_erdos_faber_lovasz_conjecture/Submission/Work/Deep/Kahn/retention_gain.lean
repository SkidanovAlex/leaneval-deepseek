import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.NibbleRoundDefs

/-!
# The per-round gain of the retention factors

This module proves the elementary scalar estimate that drives the iteration of the nibble for
Kahn's theorem: in the regime of one round,

* `Λ ≥ (1+ε) D` (the lists are slack by a factor `1+ε`),
* `16 C ≤ (1+ε) K` (Kang--Kelly--Kühn--Methuku--Osthus, arXiv:2109.11438, with `p = 1/K`),
* `2 (2 C - 1) ≤ ε K` (the "small `ε`" side condition, `K ≫ C/ε`),

the two retention factors

`retention Λ C D K = (1 - 1/(KΛ)) ^ (C D)`  and  `retentionU Λ C D K = (1 - 1/(KΛ)) ^ (D (C-1))`

satisfy, writing `s = retention` and `u = retentionU` and `den = (1 - 1/K) u + (1/K) (1 - s)`:

1. `1 + ε/(4K) ≤ s / den` — the list-retention factor beats the new colour-degree-retention
   factor by `1 + ε/(4K)`; this is the per-round improvement of the ratio `Λ / D`;
2. `1/2 ≤ s`;
3. `225/256 ≤ den`;
4. `den ≤ 1 - 1/(2K)`.

## The estimates behind the four clauses

Write `p = 1/K`, `q = 1/(KΛ)`, `x = 1 - q`, `δ = D q` and `t = C δ`.  The two exponents differ
by `D`, so `s = u x^D`, and Bernoulli's inequality (`one_add_mul_le_pow`) gives

* `x^D ≥ 1 - δ`, `s ≥ 1 - t`, `u ≥ 1 - (C-1) δ`,
* `δ ≤ p/(1+ε)`, `t ≤ C p/(1+ε) ≤ 1/16` (from `16 C ≤ (1+ε) K`),
* `t ≤ C p/(1+ε) ≤ ε/(3(1+ε))` (from `2(2C-1) ≤ ε K` and `K ≥ 16`, whence `p ≤ ε/6`).

Clauses (2)--(4) are then immediate; and clause (1) follows from the two estimates

* `(1-p) u ≤ (1 - pε/(1+ε)) s`, whose content is the identity
  `(1 - pε/(1+ε)) (1 - p/(1+ε)) = 1 - p + p²ε/(1+ε)²` together with `δ ≤ p/(1+ε)`;
* `(1 + εp/4) (1-s) ≤ ε(3-ε)/(4(1+ε)) · s`, which reduces to `65(1+ε) ≤ 16(3-ε)(3+2ε)`,
  a consequence of `ε ≤ 1` (equivalently `128 ε² + 68 ε ≤ 316`),

after which the remaining algebra
`(1 + εp/4)(1 - pε/(1+ε)) + p ε(3-ε)/(4(1+ε)) ≤ 1` is the trivial identity
`1 - (...)= p²ε²/(4(1+ε)) ≥ 0`.
-/

set_option maxHeartbeats 1000000

namespace Work.Deep.Kahn

/-- The scalar core of `retention_gain`: an abstract version in the variables
`p = 1/K`, `q = 1/(KΛ)`, `s = retention`, `u = retentionU`, `dl = D q` and
`den = (1-p) u + p (1-s)`, with all the numerical consequences of the round's side conditions
passed in as hypotheses. -/
private lemma retention_gain_core {C K : ℕ} {ε p s u dl den : ℝ}
    (hp0 : 0 < p) (hp16 : p ≤ 1/16)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hs0 : 0 < s) (hsT : s ≤ 1) (hu0 : 0 < u) (huT : u ≤ 1)
    (hδ : dl ≤ p/(1+ε))
    (hden : den = (1-p)*u + p*(1-s))
    (hsB : 1 - (C:ℝ)*dl ≤ s) (hsu : u*(1-dl) ≤ s) (huB : 1 - ((C:ℝ)-1)*dl ≤ u)
    (ht16 : (C:ℝ)*dl ≤ 1/16) (hte : (C:ℝ)*dl ≤ ε/(3*(1+ε)))
    (hdl0 : 0 ≤ dl)
    (hβ : ε/(4*(K:ℝ)) = ε*p/4) (h2K : 1/(2*(K:ℝ)) = p/2) :
    (1 + ε/(4*(K:ℝ))) ≤ s/den ∧ (1/2:ℝ) ≤ s ∧ (225/256:ℝ) ≤ den ∧ den ≤ 1 - 1/(2*(K:ℝ)) := by
  have hε0e : (0:ℝ) < 1 + ε := by linarith
  -- (2) `1/2 ≤ s`
  have hs_half : (1/2:ℝ) ≤ s := by linarith [hsB, ht16]
  -- (4) `den ≤ 1 - 1/(2K)`
  have hden_le : den ≤ 1 - 1/(2*(K:ℝ)) := by
    have e1 : (1-p)*u ≤ 1-p := by
      have h : 0 ≤ 1-p := by linarith [hp16]
      have h' : (1-p)*u ≤ (1-p)*1 := mul_le_mul_of_nonneg_left huT h
      linarith [h']
    have e2 : p*(1-s) = p - p*s := by ring
    have e3 : p/2 ≤ p*s := by
      have h : p*(1/2) ≤ p*s := mul_le_mul_of_nonneg_left hs_half hp0.le
      linarith [h]
    rw [hden, h2K]
    linarith
  -- (3) `225/256 ≤ den`
  have hden_ge : (225/256:ℝ) ≤ den := by
    have ht' : ((C:ℝ)-1)*dl ≤ 1/16 := by
      have h1' : ((C:ℝ)-1) ≤ (C:ℝ) := by linarith
      have h2' : ((C:ℝ)-1)*dl ≤ (C:ℝ)*dl := mul_le_mul_of_nonneg_right h1' hdl0
      linarith
    have hu15 : (15/16:ℝ) ≤ u := by linarith [huB, ht']
    have hp15 : (15/16:ℝ) ≤ 1-p := by linarith [hp16]
    have hmul : (15/16)*(15/16) ≤ (1-p)*u :=
      mul_le_mul hp15 hu15 (by norm_num) (by linarith [hu0])
    have hpos : 0 ≤ p*(1-s) := mul_nonneg hp0.le (by linarith [hsT])
    have heq : (225/256:ℝ) = (15/16)*(15/16) := by norm_num
    rw [heq, hden]
    linarith
  -- the two estimates behind (1)
  have hA0 : 0 ≤ 1 - p*ε/(1+ε) := by
    have hpε : p*ε/(1+ε) ≤ 1 := by
      rw [div_le_iff₀ hε0e]
      nlinarith [hp16, hε0.le, hε1]
    linarith
  have key1 : (1-p) ≤ (1 - p*ε/(1+ε)) * (1 - dl) := by
    have h1' : 1 - p/(1+ε) ≤ 1 - dl := by linarith [hδ]
    have h3' : 1 - p + p*p*ε/((1+ε)*(1+ε)) = (1 - p*ε/(1+ε)) * (1 - p/(1+ε)) := by
      field_simp
      ring
    have h4' : 0 ≤ p*p*ε/((1+ε)*(1+ε)) := by
      apply div_nonneg _ (by positivity)
      nlinarith [mul_nonneg hp0.le (mul_nonneg hp0.le hε0.le)]
    have h2' : (1 - p*ε/(1+ε)) * (1 - p/(1+ε)) ≤ (1 - p*ε/(1+ε)) * (1 - dl) :=
      mul_le_mul_of_nonneg_left h1' hA0
    linarith
  have bound1 : (1-p)*u ≤ (1 - p*ε/(1+ε)) * s := by
    calc (1-p)*u ≤ ((1 - p*ε/(1+ε)) * (1 - dl)) * u := mul_le_mul_of_nonneg_right key1 hu0.le
      _ = (1 - p*ε/(1+ε)) * (u * (1-dl)) := by ring
      _ ≤ (1 - p*ε/(1+ε)) * s := mul_le_mul_of_nonneg_left hsu hA0
  have hcoef : 0 ≤ ε*(3-ε)/(4*(1+ε)) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg hε0.le (by linarith)
  have key2 : (65/64:ℝ)*((C:ℝ)*dl) ≤ ε*(3-ε)/(4*(1+ε)) * (1 - (C:ℝ)*dl) := by
    have stepA : (65/64:ℝ)*(ε/(3*(1+ε))) ≤ ε*(3-ε)/(4*(1+ε))*(1 - ε/(3*(1+ε))) := by
      have hcore : (65:ℝ)*(1+ε) ≤ 16*(3-ε)*(3+2*ε) := by
        have hε2 : ε*ε ≤ 1 := by nlinarith [hε0.le, hε1]
        nlinarith [hε2, hε1]
      have hc : 0 < (3*(1+ε))/ε := by positivity
      have hmul : ((65/64:ℝ)*(ε/(3*(1+ε))))*((3*(1+ε))/ε)
          ≤ (ε*(3-ε)/(4*(1+ε))*(1 - ε/(3*(1+ε))))*((3*(1+ε))/ε) := by
        have e1 : ((65/64:ℝ)*(ε/(3*(1+ε))))*((3*(1+ε))/ε) = 65/64 := by field_simp
        have e2 : (ε*(3-ε)/(4*(1+ε))*(1 - ε/(3*(1+ε))))*((3*(1+ε))/ε)
            = (3-ε)*(3+2*ε)/(4*(1+ε)) := by field_simp; ring
        rw [e1, e2]
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 64) (by positivity : (0:ℝ) < 4*(1+ε))]
        nlinarith [hcore]
      exact le_of_mul_le_mul_right hmul hc
    have hmono1 : (65/64:ℝ)*((C:ℝ)*dl) ≤ (65/64)*(ε/(3*(1+ε))) :=
      mul_le_mul_of_nonneg_left hte (by norm_num)
    have hmono2 : ε*(3-ε)/(4*(1+ε))*(1 - ε/(3*(1+ε))) ≤ ε*(3-ε)/(4*(1+ε))*(1 - (C:ℝ)*dl) :=
      mul_le_mul_of_nonneg_left (by linarith [hte]) hcoef
    linarith
  have bound2 : (1 + ε*p/4) * (1-s) ≤ ε*(3-ε)/(4*(1+ε)) * s := by
    have hβle : 1 + ε*p/4 ≤ 65/64 := by nlinarith [hp16, hε1, hε0.le, hp0.le]
    have h1s : 1 - s ≤ (C:ℝ)*dl := by linarith [hsB]
    have hst : 1 - (C:ℝ)*dl ≤ s := by linarith [hsB]
    have h0 : (1 + ε*p/4)*(1-s) ≤ (65/64)*((C:ℝ)*dl) := by
      have ha : (1 + ε*p/4)*(1-s) ≤ (65/64)*(1-s) :=
        mul_le_mul_of_nonneg_right hβle (by linarith [hsT])
      have hb : (65/64)*(1-s) ≤ (65/64)*((C:ℝ)*dl) := mul_le_mul_of_nonneg_left h1s (by norm_num)
      linarith
    calc (1 + ε*p/4)*(1-s) ≤ (65/64)*((C:ℝ)*dl) := h0
      _ ≤ ε*(3-ε)/(4*(1+ε))*(1 - (C:ℝ)*dl) := key2
      _ ≤ ε*(3-ε)/(4*(1+ε))*s := mul_le_mul_of_nonneg_left hst hcoef
  -- the bracket identity
  have hbr : (1 + ε*p/4)*(1 - p*ε/(1+ε)) + p*(ε*(3-ε)/(4*(1+ε))) ≤ 1 := by
    have key : 1 - ((1 + ε*p/4)*(1 - p*ε/(1+ε)) + p*(ε*(3-ε)/(4*(1+ε)))) = p*p*ε*ε/(4*(1+ε)) := by
      field_simp
      ring
    have hpp : 0 ≤ p*p*ε*ε := by
      nlinarith [mul_nonneg (mul_nonneg hp0.le hp0.le) (mul_nonneg hε0.le hε0.le)]
    have hpos : 0 ≤ p*p*ε*ε/(4*(1+ε)) := div_nonneg hpp (by positivity)
    linarith
  -- (1) `1 + ε/(4K) ≤ s / den`
  have hden_pos : 0 < den := by
    have h1 : 0 < (1-p)*u := mul_pos (by linarith [hp16]) hu0
    have h2 : 0 ≤ p*(1-s) := mul_nonneg hp0.le (by linarith [hsT])
    rw [hden]; linarith
  have main1 : (1 + ε/(4*(K:ℝ))) ≤ s/den := by
    have hgoal : (1 + ε*p/4) * den ≤ s := by
      have term1 : (1 + ε*p/4)*((1-p)*u) ≤ (1 + ε*p/4)*((1 - p*ε/(1+ε))*s) :=
        mul_le_mul_of_nonneg_left bound1 (by nlinarith [hp0.le, hε0.le])
      have term2 : (1 + ε*p/4)*(p*(1-s)) ≤ p*(ε*(3-ε)/(4*(1+ε))*s) := by
        have h := mul_le_mul_of_nonneg_left bound2 hp0.le
        have e : (1 + ε*p/4)*(p*(1-s)) = p*((1 + ε*p/4)*(1-s)) := by ring
        rw [e]
        exact h
      calc (1 + ε*p/4)*den = (1 + ε*p/4)*((1-p)*u) + (1 + ε*p/4)*(p*(1-s)) := by
              rw [hden]; ring
        _ ≤ (1 + ε*p/4)*((1 - p*ε/(1+ε))*s) + p*(ε*(3-ε)/(4*(1+ε))*s) := add_le_add term1 term2
        _ = s * ((1 + ε*p/4)*(1 - p*ε/(1+ε)) + p*(ε*(3-ε)/(4*(1+ε)))) := by ring
        _ ≤ s * 1 := mul_le_mul_of_nonneg_left hbr hs0.le
        _ = s := by ring
    rw [le_div_iff₀ hden_pos]
    simpa [hβ] using hgoal
  exact ⟨main1, hs_half, hden_ge, hden_le⟩

theorem retention_gain {C D Λ K : ℕ} {ε : ℝ}
    (hC : 2 ≤ C) (hK : 2 ≤ K) (hD : 1 ≤ D) (hΛ : 1 ≤ Λ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h1 : (1 + ε) * (D : ℝ) ≤ (Λ : ℝ))
    (h2 : (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ))
    (h3 : 2 * (2 * (C : ℝ) - 1) ≤ ε * (K : ℝ)) :
    (1 + ε / (4 * (K : ℝ))) ≤
        retention Λ C D K /
          ((1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K)) ∧
    (1 / 2 : ℝ) ≤ retention Λ C D K ∧
    (225 / 256 : ℝ) ≤
        (1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K) ∧
    (1 - 1 / (K : ℝ)) * retentionU Λ C D K + (1 / (K : ℝ)) * (1 - retention Λ C D K) ≤
        1 - 1 / (2 * (K : ℝ)) := by
  have hC2 : (2:ℝ) ≤ (C:ℝ) := by exact_mod_cast hC
  have hΛ1R : (1:ℝ) ≤ (Λ:ℝ) := by exact_mod_cast hΛ
  have hKpos : (0:ℝ) < (K:ℝ) := by positivity
  have hΛpos : (0:ℝ) < (Λ:ℝ) := by positivity
  have hε0e : (0:ℝ) < 1 + ε := by linarith
  have hC0 : (0:ℝ) ≤ (C:ℝ) := by positivity
  have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
  -- `K ≥ 16` and `ε K ≥ 6`
  have hK16 : (16:ℝ) ≤ (K:ℝ) := by
    have e2 : (1+ε) * (K:ℝ) ≤ 2 * (K:ℝ) := by nlinarith [hε1, hK0]
    have e3 : (32:ℝ) ≤ (16:ℝ) * (C:ℝ) := by linarith
    linarith [h2, e2, e3]
  have hK6 : (6:ℝ) ≤ ε * (K:ℝ) := by
    have e : (6:ℝ) ≤ 2 * (2*(C:ℝ) - 1) := by linarith
    linarith [h3, e]
  -- unfold the two retention factors and name the round's parameters
  simp only [retention, retentionU]
  set p : ℝ := 1 / (K:ℝ) with hp
  set q : ℝ := p / (Λ:ℝ) with hq
  set s : ℝ := (1 - q)^(C*D) with hs
  set u : ℝ := (1 - q)^(D*(C-1)) with hu
  set dl : ℝ := (D:ℝ)*q with hdl
  set den : ℝ := (1-p)*u + p*(1-s) with hden
  have hp0 : 0 < p := by rw [hp]; positivity
  have hdl0 : 0 ≤ dl := by rw [hdl]; positivity
  have hp16 : p ≤ 1/16 := by
    rw [hp, le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
    have : (1/(K:ℝ))*16 = 16/(K:ℝ) := by ring
    rw [this, div_le_iff₀ hKpos]
    linarith [hK16]
  have hq0 : 0 < q := by rw [hq]; positivity
  have hx0 : 0 < 1 - q := by
    have hqp : q ≤ p := by
      rw [hq, div_le_iff₀ hΛpos]
      nlinarith [hp0, hΛ1R]
    linarith [le_trans hqp hp16]
  have hx1 : 1 - q ≤ 1 := by linarith [hq0]
  -- `D q ≤ p/(1+ε)`
  have hδ : dl ≤ p/(1+ε) := by
    rw [hdl, hq, hp]
    field_simp
    linarith [h1]
  -- exponent bookkeeping
  have hcast1 : ((C*D : ℕ) : ℝ) * q = (C:ℝ)*dl := by push_cast; rw [hdl]; ring
  have hcast2 : ((D*(C-1) : ℕ) : ℝ) * q = ((C:ℝ)-1)*dl := by
    have hCsub : ((C - 1 : ℕ) : ℝ) = (C:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ C)]; norm_num
    push_cast
    rw [hCsub, hdl]
    ring
  have hu0 : 0 < u := by rw [hu]; positivity
  have hs0 : 0 < s := by rw [hs]; positivity
  -- Bernoulli: the retention factors are close to `1`
  have hsB : 1 - (C:ℝ)*dl ≤ s := by
    have h2' := one_add_mul_le_pow (a := -q) (by linarith : -2 ≤ -q) (C*D)
    have h2'' : 1 - ((C*D:ℕ):ℝ)*q ≤ (1-q)^(C*D) := by simpa [mul_neg, sub_eq_add_neg] using h2'
    rw [hcast1] at h2''
    rw [hs]
    exact h2''
  have huB : 1 - ((C:ℝ)-1)*dl ≤ u := by
    have h2' := one_add_mul_le_pow (a := -q) (by linarith : -2 ≤ -q) (D*(C-1))
    have h2'' : 1 - ((D*(C-1):ℕ):ℝ)*q ≤ (1-q)^(D*(C-1)) := by
      simpa [mul_neg, sub_eq_add_neg] using h2'
    rw [hcast2] at h2''
    rw [hu]
    exact h2''
  have hsT : s ≤ 1 := by rw [hs]; exact pow_le_one₀ hx0.le hx1
  have huT : u ≤ 1 := by rw [hu]; exact pow_le_one₀ hx0.le hx1
  have hexp : C*D = D*(C-1) + D := by
    have hC1 : C - 1 + 1 = C := by omega
    calc C*D = D*C := Nat.mul_comm C D
      _ = D*(C-1+1) := by rw [hC1]
      _ = D*(C-1) + D*1 := Nat.mul_add D (C-1) 1
      _ = D*(C-1) + D := by rw [Nat.mul_one]
  have hsw : s = u * (1-q)^D := by rw [hs, hu, hexp, pow_add]
  -- `u (1 - D q) ≤ s` (the two retentions differ by the factor `x^D`)
  have hsu : u*(1-dl) ≤ s := by
    have hwB : 1 - dl ≤ (1-q)^D := by
      rw [hdl]
      have h2' := one_add_mul_le_pow (a := -q) (by linarith : -2 ≤ -q) D
      simpa [mul_neg, sub_eq_add_neg] using h2'
    rw [hsw]
    exact mul_le_mul_of_nonneg_left hwB hu0.le
  -- `C · D q ≤ 1/16`  (from `16 C ≤ (1+ε) K`)
  have ht16 : (C:ℝ)*dl ≤ 1/16 := by
    have e1 : (C:ℝ)*dl ≤ (C:ℝ)*(p/(1+ε)) := mul_le_mul_of_nonneg_left hδ hC0
    have e2 : (C:ℝ)*p ≤ (1+ε)/16 := by
      have h : (C:ℝ)*p = (C:ℝ)/(K:ℝ) := by rw [hp]; ring
      rw [h, div_le_div_iff₀ hKpos (by norm_num : (0:ℝ) < 16)]
      nlinarith [h2]
    have e3 : (C:ℝ)*(p/(1+ε)) ≤ 1/16 := by
      calc (C:ℝ)*(p/(1+ε)) = (C:ℝ)*p/(1+ε) := by ring
        _ ≤ ((1+ε)/16)/(1+ε) := div_le_div_of_nonneg_right e2 hε0e.le
        _ = 1/16 := by field_simp
    linarith
  -- `C · D q ≤ ε/(3(1+ε))`  (from `2 (2C-1) ≤ ε K` and `K ≥ 16`)
  have hte : (C:ℝ)*dl ≤ ε/(3*(1+ε)) := by
    have hpe : p ≤ ε/6 := by
      rw [hp, le_div_iff₀ (by norm_num : (0:ℝ) < 6)]
      have : (1/(K:ℝ))*6 = 6/(K:ℝ) := by ring
      rw [this, div_le_iff₀ hKpos]
      linarith [hK6]
    have e1 : (C:ℝ)*dl ≤ (C:ℝ)*(p/(1+ε)) := mul_le_mul_of_nonneg_left hδ hC0
    have e2 : (C:ℝ)*p ≤ ε/3 := by
      have a : (C:ℝ)*p ≤ ε/4 + p/2 := by
        have key : (C:ℝ)*p - p/2 = (2*(C:ℝ)-1)/(2*(K:ℝ)) := by rw [hp]; field_simp
        have h3' : (2*(C:ℝ)-1)/(2*(K:ℝ)) ≤ ε/4 := by
          rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*(K:ℝ)) (by norm_num : (0:ℝ) < 4)]
          nlinarith [h3]
        linarith [key, h3']
      have b : p/2 ≤ ε/12 := by linarith [hpe]
      linarith
    have e3 : (C:ℝ)*(p/(1+ε)) ≤ ε/(3*(1+ε)) := by
      calc (C:ℝ)*(p/(1+ε)) = (C:ℝ)*p/(1+ε) := by ring
        _ ≤ (ε/3)/(1+ε) := div_le_div_of_nonneg_right e2 hε0e.le
        _ = ε/(3*(1+ε)) := by rw [div_div]
    linarith
  -- convert the two occurrences of `K` into `p`
  have hβ : ε/(4*(K:ℝ)) = ε*p/4 := by rw [hp]; ring
  have h2K : 1/(2*(K:ℝ)) = p/2 := by rw [hp]; ring
  exact retention_gain_core hp0 hp16 hε0 hε1 hs0 hsT hu0 huT hδ hden hsB hsu huB ht16 hte hdl0
    hβ h2K

end Work.Deep.Kahn
