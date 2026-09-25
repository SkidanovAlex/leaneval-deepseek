import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.R3.caC_ge

namespace Work.RHContract.A.RegionIII

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-! ## Pointwise bounds for a single `k = 2` summand

Write `ξ = caXi ε ≥ 10^8`, `w = ξ^{−1/4}`, `c = caC ε`.  The two elementary facts used
below are `(1 − w/2 − 6w²)/(ξ log ξ) ≤ c` (from `hA2` through `A.R3.caC_ge_real`) and, for
every prime `p > √ξ`,

* `c log p − 1/(2p(p−1)) ≥ −(w/4 + 4w²)/ξ`, and
* `c log p − 1/(2p(p−1)) ≥ 0` when `p(p−1) ≥ ξ(1+w)`. -/

/-- `1 ≤ (1 + u)(1 − u/2 − 6u²)` for `0 ≤ u ≤ 1/100`. -/
private lemma one_le_factor (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) :
    (1 : ℝ) ≤ (1 + u) * (1 - (1 / 2) * u - 6 * u ^ 2) := by
  nlinarith [hu0, hu, sq_nonneg u, sq_nonneg (u - 1 / 100), sq_nonneg (u + 1)]

/-- Pointwise lower bound `c log p − 1/(2p(p−1)) ≥ −(w/4 + 4w²)/ξ` for `p > √ξ`. -/
private lemma term_lower {ξ w c p : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ)
    (hw : w = ξ ^ (-(1 / 4 : ℝ))) (hw2 : w ^ 2 = ξ ^ (-(1 / 2 : ℝ)))
    (hc : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) ≤ c)
    (hp : Real.sqrt ξ < p) :
    -((w / 4 + 4 * w ^ 2) / ξ) ≤ c * Real.log p - 1 / (2 * p * (p - 1)) := by
  have hξ0 : 0 < ξ := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  have hξ1 : 1 < ξ := by linarith [show (1 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  have hw0 : 0 < w := by rw [hw]; exact Real.rpow_pos_of_pos hξ0 _
  have hw100 : w ≤ 1 / 100 := by rw [hw]; exact Work.RHContract.A.R3.rpow_neg_quarter_le hξ
  have hA : 0 < 1 - (1 / 2) * w - 6 * w ^ 2 := by nlinarith [hw0, hw100]
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  have hcpos : 0 < c := lt_of_lt_of_le (div_pos hA (mul_pos hξ0 hLpos)) hc
  have hlp : Real.log ξ / 2 < Real.log p := by
    have h1 : Real.log (Real.sqrt ξ) < Real.log p := Real.log_lt_log (Real.sqrt_pos.mpr hξ0) hp
    rw [Real.log_sqrt hξ0.le] at h1
    exact h1
  have hstep1 : (1 - (1 / 2) * w - 6 * w ^ 2) / (2 * ξ) ≤ c * Real.log p := by
    have h2 : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2)
        ≤ c * (Real.log ξ / 2) := mul_le_mul_of_nonneg_right hc (by linarith [hLpos])
    have h3 : c * (Real.log ξ / 2) ≤ c * Real.log p :=
      mul_le_mul_of_nonneg_left (le_of_lt hlp) hcpos.le
    have h4 : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2)
        = (1 - (1 / 2) * w - 6 * w ^ 2) / (2 * ξ) := by field_simp
    linarith [h2, h3, h4]
  have hsq : (Real.sqrt ξ) ^ 2 = ξ := Real.sq_sqrt hξ0.le
  have hpp : ξ - Real.sqrt ξ < p * (p - 1) := by
    have hfac : p * (p - 1) - (ξ - Real.sqrt ξ) = (p - Real.sqrt ξ) * (p + Real.sqrt ξ - 1) := by
      nlinarith [hsq]
    have h1 : 0 < p - Real.sqrt ξ := by linarith [hp]
    have h2 : 0 < p + Real.sqrt ξ - 1 := by nlinarith [hp, Real.sqrt_nonneg ξ]
    nlinarith [hfac, mul_pos h1 h2]
  have hpos1 : 0 < ξ - Real.sqrt ξ := by
    have hx1 : 1 ≤ Real.sqrt ξ := Real.one_le_sqrt.mpr hξ1.le
    nlinarith [hx1, hsq, Real.sqrt_nonneg ξ, hξ1]
  have hstep2 : 1 / (2 * p * (p - 1)) ≤ 1 / (2 * (ξ - Real.sqrt ξ)) := by
    apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (by linarith [hpos1])
    linarith [hpp]
  have h1s : 1 / Real.sqrt ξ = w ^ 2 := by
    rw [hw2, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hξ0.le (1 / 2 : ℝ)]
  have hstep3 : 1 / (2 * (ξ - Real.sqrt ξ)) ≤ 1 / (2 * ξ) * (1 + 2 * w ^ 2) := by
    have hsqrt2 : 2 ≤ Real.sqrt ξ := by
      rw [Real.le_sqrt (by norm_num) hξ0.le]; nlinarith
    rw [show (1 : ℝ) / (2 * ξ) * (1 + 2 * w ^ 2) = (1 + 2 * w ^ 2) / (2 * ξ) by ring]
    rw [div_le_div_iff₀ (by linarith [hpos1]) (by positivity : (0 : ℝ) < 2 * ξ)]
    have hkey2 : (1 + 2 * w ^ 2) * (2 * (ξ - Real.sqrt ξ)) = 2 * (ξ + Real.sqrt ξ - 2) := by
      rw [← h1s]; field_simp; nlinarith [hsq]
    rw [hkey2]
    linarith [hsqrt2]
  have hkey : (1 - (1 / 2) * w - 6 * w ^ 2) / (2 * ξ) - 1 / (2 * ξ) * (1 + 2 * w ^ 2)
      = -((w / 4 + 4 * w ^ 2) / ξ) := by field_simp; ring
  linarith [hstep1, hstep2, hstep3, hkey]

/-- Pointwise nonnegativity `c log p − 1/(2p(p−1)) ≥ 0` when `p(p−1) ≥ ξ(1+w)`, `p > √ξ`. -/
private lemma term_nonneg {ξ w c p : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ)
    (hw : w = ξ ^ (-(1 / 4 : ℝ))) (hw2 : w ^ 2 = ξ ^ (-(1 / 2 : ℝ)))
    (hc : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) ≤ c)
    (hp : Real.sqrt ξ < p) (hp2 : ξ * (1 + w) ≤ p * (p - 1)) :
    0 ≤ c * Real.log p - 1 / (2 * p * (p - 1)) := by
  have hξ0 : 0 < ξ := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  have hξ1 : 1 < ξ := by linarith [show (1 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  have hw0 : 0 < w := by rw [hw]; exact Real.rpow_pos_of_pos hξ0 _
  have hw100 : w ≤ 1 / 100 := by rw [hw]; exact Work.RHContract.A.R3.rpow_neg_quarter_le hξ
  have hA : 0 < 1 - (1 / 2) * w - 6 * w ^ 2 := by nlinarith [hw0, hw100]
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  have hcpos : 0 < c := lt_of_lt_of_le (div_pos hA (mul_pos hξ0 hLpos)) hc
  have hlp : Real.log ξ / 2 ≤ Real.log p := by
    have h1 : Real.log (Real.sqrt ξ) < Real.log p := Real.log_lt_log (Real.sqrt_pos.mpr hξ0) hp
    rw [Real.log_sqrt hξ0.le] at h1; exact h1.le
  have hfac : 1 ≤ (1 + w) * (1 - (1 / 2) * w - 6 * w ^ 2) := one_le_factor w hw0.le hw100
  have hstep : (1 : ℝ) ≤ 2 * p * (p - 1) * c * Real.log p := by
    have h4 : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2)
        ≤ c * Real.log p := by
      have h5 : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2)
          ≤ c * (Real.log ξ / 2) := mul_le_mul_of_nonneg_right hc (by linarith [hLpos])
      linarith [h5, mul_le_mul_of_nonneg_left hlp hcpos.le]
    have h3 : 2 * p * (p - 1) * ((1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2))
        ≤ 2 * p * (p - 1) * (c * Real.log p) :=
      mul_le_mul_of_nonneg_left h4 (by nlinarith [hp, hξ0])
    have h2 : 2 * p * (p - 1) * ((1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) * (Real.log ξ / 2))
        = p * (p - 1) * (1 - (1 / 2) * w - 6 * w ^ 2) / ξ := by field_simp
    have h6 : 1 ≤ p * (p - 1) * (1 - (1 / 2) * w - 6 * w ^ 2) / ξ := by
      have h7 : ξ * (1 + w) * (1 - (1 / 2) * w - 6 * w ^ 2)
          ≤ p * (p - 1) * (1 - (1 / 2) * w - 6 * w ^ 2) :=
        mul_le_mul_of_nonneg_right hp2 hA.le
      have h8 : ξ * ((1 + w) * (1 - (1 / 2) * w - 6 * w ^ 2))
          ≤ p * (p - 1) * (1 - (1 / 2) * w - 6 * w ^ 2) := by linarith [h7]
      rw [le_div_iff₀ hξ0]; nlinarith [h8, hfac, hξ0, hA.le]
    linarith [h3, h2 ▸ h6]
  rw [sub_nonneg, div_le_iff₀ (by nlinarith [hp, hξ0] : (0 : ℝ) < 2 * p * (p - 1))]
  linarith [hstep]

/-! ## The two counting / numeric estimates -/

/-- At most `√ξ·w/2 + 4` primes `p > √ξ` can satisfy `p(p−1) < ξ(1+w)`. -/
private lemma card_bad_le {ξ w : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ) (hw0 : 0 ≤ w)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, 2 ≤ p)
    (hfloor : ∀ p ∈ S, ⌊Real.sqrt ξ⌋₊ < p) :
    ((S.filter (fun p : ℕ => (p : ℝ) * ((p : ℝ) - 1) < ξ * (1 + w))).card : ℝ)
      ≤ Real.sqrt ξ * w / 2 + 4 := by
  have hξ0 : 0 < ξ := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  set A : Finset ℕ := S.filter (fun p : ℕ => (p : ℝ) * ((p : ℝ) - 1) < ξ * (1 + w)) with hA
  set M : ℕ := ⌊Real.sqrt ξ * (1 + w / 2) + 1⌋₊ with hM
  have hsub : A ⊆ Finset.Icc (⌊Real.sqrt ξ⌋₊ + 1) M := by
    intro p hp
    rw [Finset.mem_Icc]
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hpbad⟩ := hp
    refine ⟨?_, ?_⟩
    · have := hfloor p hpS; omega
    · have hp2 : 2 ≤ p := hprime p hpS
      have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_trans (by norm_num) hp2)
      have hp1R : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith [hpR]
      have hsqi : ((p : ℝ) - 1) ^ 2 ≤ (p : ℝ) * ((p : ℝ) - 1) := by nlinarith [hp1R]
      have hlt : ((p : ℝ) - 1) ^ 2 < ξ * (1 + w) := lt_of_le_of_lt hsqi hpbad
      have hply : (p : ℝ) - 1 < Real.sqrt (ξ * (1 + w)) := by
        rw [Real.lt_sqrt (by linarith)]; exact hlt
      have h1w : Real.sqrt (1 + w) ≤ 1 + w / 2 := by
        rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith [hw0, sq_nonneg w]⟩
      rw [Real.sqrt_mul hξ0.le (1 + w)] at hply
      have hstep : (p : ℝ) - 1 < Real.sqrt ξ * (1 + w / 2) :=
        lt_of_lt_of_le hply (mul_le_mul_of_nonneg_left h1w (Real.sqrt_nonneg ξ))
      have hfin : (p : ℝ) ≤ Real.sqrt ξ * (1 + w / 2) + 1 := by linarith
      exact Nat.le_floor hfin
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_add_right] at hcard
  have hdM : ⌊Real.sqrt ξ⌋₊ ≤ M := by
    apply Nat.floor_mono; nlinarith [Real.sqrt_nonneg ξ, hw0]
  have hcast : ((M - ⌊Real.sqrt ξ⌋₊ : ℕ) : ℝ) = (M : ℝ) - (⌊Real.sqrt ξ⌋₊ : ℝ) :=
    Nat.cast_sub hdM
  have hAle : (A.card : ℝ) ≤ (M : ℝ) - (⌊Real.sqrt ξ⌋₊ : ℝ) := by
    rw [← hcast]; exact_mod_cast hcard
  have hMle : (M : ℝ) ≤ Real.sqrt ξ * (1 + w / 2) + 1 := Nat.floor_le (by positivity)
  have hdge : Real.sqrt ξ - 1 ≤ (⌊Real.sqrt ξ⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (Real.sqrt ξ); linarith
  calc (A.card : ℝ) ≤ (M : ℝ) - (⌊Real.sqrt ξ⌋₊ : ℝ) := hAle
    _ ≤ (Real.sqrt ξ * (1 + w / 2) + 1) - (Real.sqrt ξ - 1) := by linarith
    _ = Real.sqrt ξ * w / 2 + 2 := by ring
    _ ≤ Real.sqrt ξ * w / 2 + 4 := by linarith

/-- The numeric estimate `(w/4 + 4w²)/ξ · (√ξ·w/2 + 4) ≤ (1/200)·u(ξ)` for `ξ ≥ 10^8`,
`w = ξ^{−1/4}`. -/
private lemma numeric_bound {ξ w : ℝ} (hξ : (10 : ℝ) ^ 8 ≤ ξ) (hw : w = ξ ^ (-(1 / 4 : ℝ))) :
    (w / 4 + 4 * w ^ 2) / ξ * (Real.sqrt ξ * w / 2 + 4)
      ≤ (1 / 200) * (1 / (Real.sqrt ξ * Real.log ξ)) := by
  have hξ0 : 0 < ξ := by linarith [show (0 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  have hξ1 : 1 < ξ := by linarith [show (1 : ℝ) < (10 : ℝ) ^ 8 by norm_num]
  set y : ℝ := ξ ^ (1 / 4 : ℝ) with hy
  have hy100 : 100 ≤ y := by
    have h1 : ((10 : ℝ) ^ 8) ^ (1 / 4 : ℝ) ≤ ξ ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hξ (by norm_num)
    have h2 : ((10 : ℝ) ^ 8) ^ (1 / 4 : ℝ) = 100 := by
      rw [← Real.rpow_natCast (10 : ℝ) 8, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]; norm_num
    rw [hy]; linarith [h1, h2.le]
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hy4 : y ^ 4 = ξ := by
    rw [hy, ← Real.rpow_natCast (ξ ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul hξ0.le (1 / 4 : ℝ) (4 : ℕ)]
    norm_num
  have hysq : y ^ 2 = Real.sqrt ξ := by
    rw [hy, ← Real.rpow_natCast (ξ ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hξ0.le (1 / 4 : ℝ) (2 : ℕ),
      Real.sqrt_eq_rpow]
    norm_num
  have hwy : w = y⁻¹ := by rw [hw, hy, ← Real.rpow_neg hξ0.le (1 / 4 : ℝ)]
  have hlogξ : Real.log ξ = 4 * Real.log y := by rw [← hy4, Real.log_pow]; norm_num
  have hcore : 100 * (y + 16) * (y + 8) * Real.log y ≤ y ^ 4 := by
    have hlog : Real.log y ≤ 2 * Real.sqrt y := by
      have h := Real.log_le_rpow_div hy0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [Real.sqrt_eq_rpow]
      have hh : y ^ (1 / 2 : ℝ) / ((1 : ℝ) / 2) = 2 * y ^ (1 / 2 : ℝ) := by ring
      linarith [h, hh.le, hh.ge]
    have hlin : (y + 16) * (y + 8) ≤ 2 * y ^ 2 := by nlinarith
    have hsq : Real.sqrt y ≤ y / 10 := by rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
    have hsqy : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy0.le
    have h1 : 100 * (y + 16) * (y + 8) * Real.log y ≤ 100 * (2 * y ^ 2) * (2 * Real.sqrt y) := by
      have hA : 100 * (y + 16) * (y + 8) ≤ 100 * (2 * y ^ 2) := by
        have := mul_le_mul_of_nonneg_left hlin (by norm_num : (0 : ℝ) ≤ 100); linarith [this]
      have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1.le
      have : (100 * (y + 16) * (y + 8)) * Real.log y ≤ (100 * (2 * y ^ 2)) * (2 * Real.sqrt y) :=
        mul_le_mul hA hlog hlog0 (by positivity)
      linarith [this]
    have h2 : 100 * (2 * y ^ 2) * (2 * Real.sqrt y) ≤ y ^ 4 := by
      have h400 : 400 * Real.sqrt y ≤ y ^ 2 := by nlinarith [hsq, hy0, Real.sqrt_nonneg y]
      nlinarith [h400, hy0, hsqy, Real.sqrt_nonneg y]
    linarith [h1, h2]
  have hgoal : (w / 4 + 4 * w ^ 2) / ξ * (Real.sqrt ξ * w / 2 + 4)
      = (1 / (4 * y) + 4 / y ^ 2) / y ^ 4 * (y / 2 + 4) := by
    rw [hwy, ← hysq, ← hy4]; field_simp
  rw [hgoal]
  rw [show (1 / 200) * (1 / (Real.sqrt ξ * Real.log ξ))
      = (1 / 200) * (1 / (y ^ 2 * (4 * Real.log y))) by rw [← hysq, hlogξ]]
  rw [show (1 / 200) * (1 / (y ^ 2 * (4 * Real.log y))) = 1 / (200 * (y ^ 2 * (4 * Real.log y)))
      by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 200 * (y ^ 2 * (4 * Real.log y)))]
  rw [show (1 / (4 * y) + 4 / y ^ 2) / y ^ 4 * (y / 2 + 4) * (200 * (y ^ 2 * (4 * Real.log y)))
      = 100 * (y + 16) * (y + 8) * Real.log y / y ^ 4 by field_simp; ring]
  rw [div_le_one (by positivity : (0 : ℝ) < y ^ 4)]
  exact hcore

/-! ## The main theorem -/

/-- **`Margin.caNet2 ε ≥ −(1/200)·u(ξ)` in the region `ξ = caXi ε ≥ 10^8`**,
`u ξ = 1/(√ξ log ξ)` (no `RiemannHypothesis` needed: the envelope hypothesis `hA2` suffices).

`Margin.caNet2 ε = ∑_{√ξ < p ≤ ξ₂} (caC ε·log p − 1/(2p(p−1)))` with `ξ₂ = Margin.caXi2 ε`.
Every summand is bounded below by a *negative* constant times `1/ξ`, and the number of summands
is counted with `θ`.

* `caC ε = (1 − 3/√ξ)/(ψ ξ · log ψ ξ) ≥ caClo := (1 − 3/√ξ)/((ξ + E⁺ ξ)·log(ξ + E⁺ ξ))` with
  `E⁺ ξ = 0.45 ξ^{3/4} + 2`, because `ψ ξ ≤ ξ + 0.45 ξ^{3/4} + 2` follows from `hA2` at `t = ξ`
  (given `ξ ≥ 10^8 ≥ √ξ`).
* For `p` a prime with `√ξ < p ≤ ξ₂` one has `p ≥ p₀ := ⌊√ξ⌋₊ + 1`, and
  `p ↦ 1/(2p(p−1)) − caClo·log p` is decreasing, so every summand is `≥ −δ` with
  `δ := 1/(2p₀(p₀−1)) − caClo·log p₀` (at `ξ = 10^8`, `p₀ = 10001`: `δ = 2.5·10⁻¹¹`).
* The number of terms is `# {p prime : √ξ < p ≤ ξ₂} ≤ (θ(ξ₂) − θ(√ξ))/(log √ξ)`, and
  `ξ₂ ≤ √(2.5ξ) + 1` (`Work.RHContract.A.caXi2_le_sqrt`) gives
  `θ(ξ₂) ≤ θ(√(2.5ξ)+1) ≤ √(2.5ξ) + 1 + E⁺(√(2.5ξ)+1)`, while
  `θ(√ξ) ≥ ψ(√ξ) − 3ξ^{1/4} ≥ √ξ − E⁺(√ξ) − 3ξ^{1/4}`
  (`Chebyshev.psi_sub_theta_le_three_sqrt`).  This gives at `ξ = 10^8` a count `≤ 782`, so
  `caNet2 ε ≥ −δ·782 = −1.96·10⁻⁸ = −0.0036·u(ξ) ≥ −(1/200)·u(ξ)`; the bound is uniform for
  `ξ ≥ 10^8` (the counter worst case is near `ξ = 10^8`, where `δ·N/u ≈ 0.0036`). -/
theorem caNet2_lower_regionIII (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hA2 : ∀ t : ℝ, Real.sqrt (Work.RHPlan.caXi ε : ℝ) ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2) :
    -(1 / 200) * (1 / (Real.sqrt (Work.RHPlan.caXi ε : ℝ)
        * Real.log (Work.RHPlan.caXi ε : ℝ))) ≤ Work.RHContract.Margin.caNet2 ε := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ8 : (10 : ℝ) ^ 8 ≤ ξ := hξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by norm_num) hξ8
  have hξ1 : 1 < ξ := lt_of_lt_of_le (by norm_num) hξ8
  have hLpos : 0 < Real.log ξ := Real.log_pos hξ1
  set w : ℝ := ξ ^ (-(1 / 4 : ℝ)) with hwdef
  have hw0 : 0 < w := by rw [hwdef]; exact Real.rpow_pos_of_pos hξ0 _
  have hw0le : 0 ≤ w := hw0.le
  have hw2 : w ^ 2 = ξ ^ (-(1 / 2 : ℝ)) := by
    rw [hwdef, ← Real.rpow_natCast (ξ ^ (-(1 / 4 : ℝ))) 2,
      ← Real.rpow_mul hξ0.le (-(1 / 4 : ℝ)) (2 : ℕ)]
    norm_num
  have hsξ : Real.sqrt ξ ≤ ξ := by
    have h1 : Real.sqrt ξ ≤ Real.sqrt (ξ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hξ1])
    rwa [Real.sqrt_sq hξ0.le] at h1
  have hψξ : |Chebyshev.psi ξ - ξ| ≤ 0.45 * ξ ^ (3 / 4 : ℝ) + 2 := hA2 ξ hsξ
  have hc : (1 - (1 / 2) * w - 6 * w ^ 2) / (ξ * Real.log ξ) ≤ Work.RHContract.Margin.caC ε := by
    have hcr := Work.RHContract.A.R3.caC_ge_real ξ hξ8 hψξ
    have hnum : (1 - (1 / 2) * w - 6 * w ^ 2)
        = (1 - 1 / 2 * ξ ^ (-(1 / 4 : ℝ)) - 6 * ξ ^ (-(1 / 2 : ℝ))) := by
      rw [hwdef, hw2]
    have hden2 : Work.RHContract.Margin.caC ε
        = (1 - 3 / Real.sqrt ξ) / (Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
      unfold Work.RHContract.Margin.caC; rw [← hξdef]
    rw [hnum, hden2]; exact hcr
  set S : Finset ℕ := (Nat.primesLE (Work.RHContract.Margin.caXi2 ε)).filter
      (fun q : ℕ => ⌊Real.sqrt ξ⌋₊ < q) with hSdef
  have hSprime : ∀ p ∈ S, 2 ≤ p := by
    intro p hp; rw [hSdef, Finset.mem_filter] at hp
    exact Nat.two_le_of_mem_primesLE hp.1
  have hSfloor : ∀ p ∈ S, ⌊Real.sqrt ξ⌋₊ < p := by
    intro p hp; rw [hSdef, Finset.mem_filter] at hp; exact hp.2
  have hSsqrt : ∀ p ∈ S, Real.sqrt ξ < (p : ℝ) := by
    intro p hp
    have h1 := hSfloor p hp
    have h2 : (⌊Real.sqrt ξ⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt h1)
    have h3 : Real.sqrt ξ < (⌊Real.sqrt ξ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hgoal_eq : Work.RHContract.Margin.caNet2 ε
      = ∑ p ∈ S, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := by
    rw [hSdef]; unfold Work.RHContract.Margin.caNet2; rw [← hξdef]
  rw [hgoal_eq]
  set A : Finset ℕ := S.filter (fun p : ℕ => (p : ℝ) * ((p : ℝ) - 1) < ξ * (1 + w)) with hAdef
  set B : Finset ℕ := S.filter (fun p : ℕ => ¬ ((p : ℝ) * ((p : ℝ) - 1) < ξ * (1 + w)))
      with hBdef
  have hmemS : ∀ p ∈ A, p ∈ S := by
    intro p hp; rw [hAdef] at hp; exact (Finset.mem_filter.mp hp).1
  have hB : 0 ≤ ∑ p ∈ B, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
      - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := by
    apply Finset.sum_nonneg
    intro p hp
    rw [hBdef, Finset.mem_filter] at hp
    exact term_nonneg hξ8 hwdef hw2 hc (hSsqrt p hp.1) (le_of_not_gt hp.2)
  have hA : -((w / 4 + 4 * w ^ 2) / ξ) * (A.card : ℝ)
      ≤ ∑ p ∈ A, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := by
    have h := Finset.sum_le_sum (s := A) (f := fun _ : ℕ => -((w / 4 + 4 * w ^ 2) / ξ))
      (g := fun p : ℕ => Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
        - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)))
      (fun p hp => term_lower hξ8 hwdef hw2 hc (hSsqrt p (hmemS p hp)))
    rw [Finset.sum_const, nsmul_eq_mul] at h
    have h2 : -((w / 4 + 4 * w ^ 2) / ξ) * (A.card : ℝ)
        = (A.card : ℝ) * (-((w / 4 + 4 * w ^ 2) / ξ)) := by ring
    rw [h2]; exact h
  have hNB := card_bad_le hξ8 hw0le S hSprime hSfloor
  have hδ0 : 0 ≤ (w / 4 + 4 * w ^ 2) / ξ := by positivity
  have hmul : (w / 4 + 4 * w ^ 2) / ξ * (A.card : ℝ)
      ≤ (w / 4 + 4 * w ^ 2) / ξ * (Real.sqrt ξ * w / 2 + 4) :=
    mul_le_mul_of_nonneg_left hNB hδ0
  have hnum := numeric_bound hξ8 hwdef
  have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun p : ℕ => (p : ℝ) * ((p : ℝ) - 1) < ξ * (1 + w))
      (fun p : ℕ => Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
        - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)))
  rw [← hsplit]
  calc -(1 / 200) * (1 / (Real.sqrt ξ * Real.log ξ))
      = -((1 / 200) * (1 / (Real.sqrt ξ * Real.log ξ))) := by ring
    _ ≤ -((w / 4 + 4 * w ^ 2) / ξ * (Real.sqrt ξ * w / 2 + 4)) := by linarith [hnum]
    _ ≤ -((w / 4 + 4 * w ^ 2) / ξ * (A.card : ℝ)) := by linarith [hmul]
    _ = -((w / 4 + 4 * w ^ 2) / ξ) * (A.card : ℝ) := by ring
    _ ≤ ∑ p ∈ A, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := hA
    _ ≤ ∑ p ∈ A, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1)))
        + ∑ p ∈ B, (Work.RHContract.Margin.caC ε * Real.log (p : ℝ)
          - 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))) := by linarith [hB]

end

end Work.RHContract.A.RegionIII
