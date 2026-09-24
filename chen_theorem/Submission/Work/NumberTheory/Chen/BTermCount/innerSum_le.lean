import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.prime_sum_le_integral
import Submission.Work.NumberTheory.Chen.BTermCount.hasDerivAt_abelF
import Submission.Work.NumberTheory.Chen.BTermCount.innerIntegral_bound

open Finset MeasureTheory intervalIntegral
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-- `t ↦ t / log t` is non-decreasing for `t ≥ e`. -/
private lemma div_log_le_div_log {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla : 1 ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at h
  have hb1 : b ∈ Set.Ici (Real.exp 1) := le_trans ha hab
  have hlb : 1 ≤ Real.log b := le_trans hla (Real.log_le_log ha0 hab)
  have h1 : Real.log b / b ≤ Real.log a / a := Real.log_div_self_antitoneOn ha hb1 hab
  have h3 : 0 < Real.log b / b := div_pos (by linarith) hb0
  have key1 : a / Real.log a = 1 / (Real.log a / a) := by field_simp
  have key2 : b / Real.log b = 1 / (Real.log b / b) := by field_simp
  rw [key1, key2]
  exact one_div_le_one_div_of_le h3 h1

private lemma rpow_third_cube (a : ℝ) (ha : 0 ≤ a) : ((a^3 : ℝ))^((1:ℝ)/3) = a := by
  rw [← Real.rpow_natCast a 3]
  rw [← Real.rpow_mul ha]
  norm_num

private lemma rpow_third_pow (a : ℝ) (ha : 0 ≤ a) : (a^((1:ℝ)/3))^3 = a := by
  rw [← Real.rpow_natCast (a^((1:ℝ)/3)) 3]
  rw [← Real.rpow_mul ha]
  norm_num

/-- The inner (`q₂`) sum for a fixed first coordinate `q`. For `x ≥ 1000`, `0 < q`, `Y ≥ x^{1/3}`, `Y ≤ 2x^{1/3}`, `(q:ℝ)^3 ≤ x+2`, `B = sqrt((x+2)/q)` and `Y ≤ B`, the sum over primes `q₂ ∈ [Y,B]` of `π((x+2)/(q q₂))` is at most
`(1+δ₁)·[ (x+2)/(q·log(x+2)) · log(2−3β)/(1−β) + (x+2)/q · 1000/(x^{1/3} log(x+2)) + 24E(x+2)/(q log(x+2)) ]`,
where `β = log q/log(x+2)`.

Route: (i) each term is `π(t)` with `t = (x+2)/(q q₂) ≥ x^{1/3}−1` (because `q₂² ≤ (x+2)/q` gives `q₂ ≤ (x+2)/(q q₂)`, and `q₂ ≥ Y ≥ x^{1/3}`), so `hpi` applies, and `t/log t ≤ R/log R` for the real `R = (x+2)/(q q₂)`; (ii) Abel/Mertens `prime_sum_le_integral` with `A = Y−1`, `B` and weight `f(s) = (x+2)/(q log((x+2)/(q s)))`, whose derivative is `(x+2)/(q s log((x+2)/(q s))²) ≥ 0` (module `hasDerivAt_abelF`); (iii) the integral `∫_{Y−1}^{B} f(t)/(t log t) dt = ((x+2)/q)·∫_{Y−1}^{B} dt/(t log t log((x+2)/(q t)))` is bounded by the closed-form value plus the slack `1000/(x^{1/3} log(x+2))` of `innerIntegral_bound` (module `innerIntegral_bound`, whose hypotheses are `Real.exp 1 ≤ Y−1`, `(x+2)^{1/3}−3 ≤ Y−1` and `B ≤ √((x+2)/q)`); (iv) the Abel error is `2E(f(Y−1)+f(B)) ≤ 24E(x+2)/(q log(x+2))` since `f(Y−1), f(B) ≤ 6(x+2)/(q log(x+2))`. -/
theorem innerSum_le (x Y B q : ℕ) (δ₁ E L₀ : ℝ) (hδ₁ : 0 ≤ δ₁) (hE : 0 ≤ E)
    (hx : 1000 ≤ x) (hq : 0 < q) (hYge : (x : ℝ) ^ ((1:ℝ)/3) ≤ (Y : ℝ))
    (hY2 : (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3))
    (hq3 : (q : ℝ) ^ 3 ≤ (x : ℝ) + 2)
    (hB : B = ((x + 2) / q).sqrt) (hBy : Y ≤ B)
    (hpi : ∀ t : ℕ, (x : ℝ) ^ ((1:ℝ)/3) - 1 ≤ (t : ℝ) →
      ((Nat.primesLE t).card : ℝ) ≤ (1 + δ₁) * (t : ℝ) / Real.log (t : ℝ))
    (hmer : ∀ t : ℝ, (x : ℝ) ^ ((1:ℝ)/14) - 1 ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E) :
    ((∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
        (Nat.primesLE ((x + 2) / (q * q₂))).card : ℕ) : ℝ)
      ≤ (1 + δ₁) * (((x : ℝ) + 2) / ((q : ℝ) * Real.log ((x:ℝ) + 2)) *
            Real.log (2 - 3 * (Real.log (q : ℝ) / Real.log ((x:ℝ) + 2))) /
              (1 - Real.log (q : ℝ) / Real.log ((x:ℝ) + 2))
          + ((x : ℝ) + 2) / (q : ℝ) * (1000 / ((x : ℝ) ^ ((1:ℝ)/3) * Real.log ((x:ℝ) + 2)))
          + 24 * E * (((x : ℝ) + 2) / ((q : ℝ) * Real.log ((x:ℝ) + 2)))) := by
  have hx1000 : (1000:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hx1 : (1:ℝ) < (x:ℝ) := by linarith
  have hx0 : (0:ℝ) ≤ (x:ℝ) := by linarith
  set X : ℝ := (x:ℝ) + 2 with hXdef
  set qR : ℝ := (q:ℝ) with hqRdef
  set L : ℝ := Real.log X with hLdef
  have hX1 : (1:ℝ) < X := by rw [hXdef]; linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos hX1
  have hqR0 : 0 < qR := by rw [hqRdef]; exact_mod_cast hq
  have hqR1 : 1 ≤ qR := by rw [hqRdef]; exact_mod_cast hq
  have hqR3 : qR^3 ≤ X := hq3
  -- numeric preliminaries
  have hx13_10 : (10:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
    have h1000 : ((1000:ℝ)) ^ ((1:ℝ)/3) = 10 := by
      rw [show (1000:ℝ) = (10:ℝ)^3 by norm_num]
      exact rpow_third_cube 10 (by norm_num)
    rw [← h1000]
    exact Real.rpow_le_rpow (by norm_num) hx1000 (by norm_num)
  have hY10 : (10:ℝ) ≤ (Y:ℝ) := le_trans hx13_10 hYge
  have hYnat : 10 ≤ Y := by exact_mod_cast hY10
  have hY1n : 1 ≤ Y := by omega
  have hqRle : qR ≤ X^((1:ℝ)/3) := by
    have h1 : qR = (qR^3)^((1:ℝ)/3) := (rpow_third_cube qR hqR0.le).symm
    rw [h1]
    exact Real.rpow_le_rpow (by positivity) hqR3 (by norm_num)
  have hlogq_le : Real.log qR ≤ L/3 := by
    have h := Real.log_le_log (by positivity : (0:ℝ) < qR^3) hqR3
    rw [Real.log_pow] at h
    push_cast at h
    rw [hLdef]
    linarith
  -- B bounds
  have hBB : B * B ≤ (x + 2) / q := by rw [hB]; exact Nat.sqrt_le _
  have hBBR : (B:ℝ)^2 ≤ X/qR := by
    have h1 : (B:ℝ)*(B:ℝ) ≤ (((x+2)/q : ℕ) : ℝ) := by exact_mod_cast hBB
    have h2 : ((((x+2)/q : ℕ)) : ℝ) ≤ X/qR := by
      have h3 := Nat.cast_div_le (α := ℝ) (m := x + 2) (n := q)
      rw [hXdef, hqRdef]
      push_cast at h3 ⊢
      exact h3
    rw [pow_two]
    linarith
  have hBB2 : qR * (B:ℝ)^2 ≤ X := by
    have h := mul_le_mul_of_nonneg_left hBBR hqR0.le
    rwa [mul_div_cancel₀ X hqR0.ne'] at h
  have hABreal : (Y:ℝ) - 1 ≤ (B:ℝ) := by
    have h : ((Y:ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast hBy
    linarith
  have hAreal : (((Y-1:ℕ)) : ℝ) = (Y:ℝ) - 1 := by
    rw [Nat.cast_sub hY1n]; norm_num
  -- membership facts on the interval
  have hmem : ∀ t ∈ Set.Icc ((Y:ℝ)-1) ((B:ℝ)), 0 < t ∧ 1 < X/(qR*t) := by
    intro t ht
    have ht1 : (Y:ℝ)-1 ≤ t := ht.1
    have ht2 : t ≤ (B:ℝ) := ht.2
    have ht0 : 0 < t := by linarith
    have hB10 : (10:ℝ) ≤ (B:ℝ) := le_trans hY10 (by exact_mod_cast hBy)
    have hxg : (B:ℝ) ≤ X/(qR*(B:ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < qR*(B:ℝ))]
      rw [show (B:ℝ)*(qR*(B:ℝ)) = qR*(B:ℝ)^2 by ring]
      exact hBB2
    have hle : X/(qR*(B:ℝ)) ≤ X/(qR*t) := by
      apply div_le_div_of_nonneg_left hX0.le (by positivity : (0:ℝ) < qR*t)
      exact mul_le_mul_of_nonneg_left ht2 hqR0.le
    exact ⟨ht0, by linarith⟩
  -- ## Part 1: replace each `π` by the sharp bound and pull out `(1+δ₁)`
  have hsum_bound : ((∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
        (Nat.primesLE ((x + 2) / (q * q₂))).card : ℕ) : ℝ)
      ≤ (1 + δ₁) * (∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
          (X / (qR * Real.log (X / (qR * (q₂:ℝ))))) / (q₂:ℝ)) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q₂ hq₂
    rw [Finset.mem_filter, Finset.mem_Icc] at hq₂
    obtain ⟨⟨hYq₂, hq₂B⟩, hq₂p⟩ := hq₂
    have hq₂pos : 0 < q₂ := hq₂p.pos
    have hq₂posR : (0:ℝ) < (q₂:ℝ) := by exact_mod_cast hq₂pos
    have hq2sq : q₂ * q₂ ≤ (x + 2) / q := le_trans (Nat.mul_le_mul hq₂B hq₂B) hBB
    have hq2sq' : q * (q₂ * q₂) ≤ x + 2 :=
      le_trans (Nat.mul_le_mul_left q hq2sq) (Nat.mul_div_le (x+2) q)
    have htq2 : q₂ ≤ (x + 2) / (q * q₂) := by
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos hq hq₂pos)]
      calc q₂ * (q * q₂) = q * (q₂ * q₂) := by ring
        _ ≤ x + 2 := hq2sq'
    have ht10 : (10:ℝ) ≤ (((x+2)/(q*q₂) : ℕ) : ℝ) := by
      have h1 : ((q₂:ℝ)) ≤ (((x+2)/(q*q₂) : ℕ) : ℝ) := by exact_mod_cast htq2
      have h2 : (10:ℝ) ≤ (q₂:ℝ) := le_trans hY10 (by exact_mod_cast hYq₂)
      linarith
    have ht_ge : (x:ℝ)^((1:ℝ)/3) - 1 ≤ (((x+2)/(q*q₂) : ℕ) : ℝ) := by
      have h1 : (x:ℝ)^((1:ℝ)/3) ≤ (q₂:ℝ) := le_trans hYge (by exact_mod_cast hYq₂)
      have h2 : (q₂:ℝ) ≤ (((x+2)/(q*q₂) : ℕ) : ℝ) := by exact_mod_cast htq2
      linarith
    have hcard := hpi ((x+2)/(q*q₂)) ht_ge
    have hRt : (((x+2)/(q*q₂) : ℕ) : ℝ) ≤ X/(qR*(q₂:ℝ)) := by
      have h3 := Nat.cast_div_le (α := ℝ) (m := x+2) (n := q*q₂)
      rw [hXdef, hqRdef]
      push_cast at h3 ⊢
      linarith [h3]
    have htlog : (((x+2)/(q*q₂) : ℕ) : ℝ)/Real.log (((x+2)/(q*q₂) : ℕ) : ℝ)
        ≤ (X/(qR*(q₂:ℝ)))/Real.log (X/(qR*(q₂:ℝ))) :=
      div_log_le_div_log (le_trans Real.exp_one_lt_three.le (by linarith)) hRt
    have hR1 : 1 < X/(qR*(q₂:ℝ)) := by linarith [ht10, hRt]
    have hRR : (X/(qR*(q₂:ℝ)))/Real.log (X/(qR*(q₂:ℝ)))
        = (X / (qR * Real.log (X / (qR * (q₂:ℝ))))) / (q₂:ℝ) := by
      ring
    calc (((Nat.primesLE ((x + 2) / (q * q₂))).card : ℕ) : ℝ)
        ≤ (1 + δ₁) * ((((x+2)/(q*q₂) : ℕ) : ℝ)) / Real.log ((((x+2)/(q*q₂) : ℕ) : ℝ)) := hcard
      _ = (1 + δ₁) * ((((x+2)/(q*q₂) : ℕ) : ℝ) / Real.log ((((x+2)/(q*q₂) : ℕ) : ℝ))) := by
            rw [mul_div_assoc]
      _ ≤ (1 + δ₁) * ((X/(qR*(q₂:ℝ)))/Real.log (X/(qR*(q₂:ℝ)))) :=
            mul_le_mul_of_nonneg_left htlog (by linarith)
      _ = (1 + δ₁) * ((X / (qR * Real.log (X / (qR * (q₂:ℝ))))) / (q₂:ℝ)) := by rw [hRR]
  -- ## Part 2: Abel / Mertens partial summation
  have hAbel : (∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
        (X / (qR * Real.log (X / (qR * (q₂:ℝ))))) / (q₂:ℝ))
      ≤ (∫ t in ((Y:ℝ) - 1)..((B:ℝ)), (X / (qR * Real.log (X / (qR * t)))) / (t * Real.log t))
        + 2 * E * ((X / (qR * Real.log (X / (qR * ((Y:ℝ)-1)))))
            + (X / (qR * Real.log (X / (qR * (B:ℝ)))))) := by
    have hA2 : 2 ≤ Y - 1 := by omega
    have hABnat : Y - 1 ≤ B := by omega
    have hderiv : ∀ t ∈ Set.uIcc (((Y-1:ℕ)) : ℝ) ((B:ℝ)),
        HasDerivAt (fun t : ℝ => X / (qR * Real.log (X / (qR * t))))
          (X / (qR * t * (Real.log (X / (qR * t)))^2)) t := by
      intro t ht
      rw [hAreal, Set.uIcc_of_le hABreal] at ht
      obtain ⟨ht0, hXt⟩ := hmem t ht
      exact hasDerivAt_abelF hqR0 ht0 hXt
    have hfnn : ∀ t ∈ Set.Icc (((Y-1:ℕ)) : ℝ) ((B:ℝ)),
        0 ≤ X / (qR * Real.log (X / (qR * t))) := by
      intro t ht
      rw [hAreal] at ht
      obtain ⟨ht0, hXt⟩ := hmem t ht
      exact div_nonneg hX0.le (le_of_lt (mul_pos hqR0 (Real.log_pos hXt)))
    have hmono : (∀ t ∈ Set.Icc (((Y-1:ℕ)) : ℝ) ((B:ℝ)),
          0 ≤ X / (qR * t * (Real.log (X / (qR * t)))^2)) ∨
        (∀ t ∈ Set.Icc (((Y-1:ℕ)) : ℝ) ((B:ℝ)),
          X / (qR * t * (Real.log (X / (qR * t)))^2) ≤ 0) := by
      left
      intro t ht
      rw [hAreal] at ht
      obtain ⟨ht0, hXt⟩ := hmem t ht
      exact div_nonneg hX0.le
        (le_of_lt (mul_pos (mul_pos hqR0 ht0) (pow_pos (Real.log_pos hXt) 2)))
    have hfint : IntervalIntegrable
        (fun t : ℝ => X / (qR * t * (Real.log (X / (qR * t)))^2)) volume
        (((Y-1:ℕ)) : ℝ) ((B:ℝ)) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · apply ContinuousOn.mul
        · exact continuousOn_const.mul continuousOn_id
        · apply ContinuousOn.pow
          apply ContinuousOn.log
          · apply ContinuousOn.div continuousOn_const
            · exact continuousOn_const.mul continuousOn_id
            · intro t ht
              rw [hAreal, Set.uIcc_of_le hABreal] at ht
              exact ne_of_gt (mul_pos hqR0 (hmem t ht).1)
          · intro t ht
            rw [hAreal, Set.uIcc_of_le hABreal] at ht
            exact ne_of_gt (div_pos hX0 (mul_pos hqR0 (hmem t ht).1))
      · intro t ht
        rw [hAreal, Set.uIcc_of_le hABreal] at ht
        obtain ⟨ht0, hXt⟩ := hmem t ht
        exact ne_of_gt (mul_pos (mul_pos hqR0 ht0) (pow_pos (Real.log_pos hXt) 2))
    have hmer' : ∀ t : ℝ, (((Y-1:ℕ)) : ℝ) ≤ t →
        |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E := by
      intro t ht
      rw [hAreal] at ht
      apply hmer t
      have hx14 : (x:ℝ)^((1:ℝ)/14) ≤ (x:ℝ)^((1:ℝ)/3) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (x:ℝ)) (by norm_num)
      linarith
    have hmain := prime_sum_le_integral (A := Y - 1) (B := B)
      (f := fun t : ℝ => X / (qR * Real.log (X / (qR * t))))
      (g := fun t : ℝ => X / (qR * t * (Real.log (X / (qR * t)))^2))
      (L₀ := L₀) (E := E) hA2 hABnat hderiv hfint hfnn hmono hE hmer'
    have hIocIcc : Finset.Ioc (Y - 1) B = Finset.Icc Y B := by
      ext p; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIocIcc, hAreal] at hmain
    exact hmain
  -- ## Part 3: the inner integral
  have hInt : (∫ t in ((Y:ℝ) - 1)..((B:ℝ)),
        (X / (qR * Real.log (X / (qR * t)))) / (t * Real.log t))
      ≤ (X/qR) * (Real.log (2 - 3*(Real.log qR/L)) / ((1 - Real.log qR/L)*L)
          + 1000/((x:ℝ)^((1:ℝ)/3) * L)) := by
    have hcongr : Set.EqOn (fun t : ℝ => (X / (qR * Real.log (X/(qR*t)))) / (t * Real.log t))
        (fun t : ℝ => (X/qR) * (1 / (t * Real.log t * Real.log (X/(qR*t)))))
        (Set.uIcc ((Y:ℝ)-1) ((B:ℝ))) := by
      intro t ht
      rw [Set.uIcc_of_le hABreal] at ht
      obtain ⟨ht0, hXt⟩ := hmem t ht
      ring
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hexp : Real.exp 1 ≤ (Y:ℝ) - 1 := by
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      linarith
    have hA' : ((x:ℝ)+2)^((1:ℝ)/3) - 3 ≤ (Y:ℝ) - 1 := by
      have ha : 0 ≤ (x:ℝ)^((1:ℝ)/3) := Real.rpow_nonneg hx0 _
      have hxle : ((x:ℝ)+2)^((1:ℝ)/3) ≤ (x:ℝ)^((1:ℝ)/3) + 2 := by
        have h1 : X ≤ ((x:ℝ)^((1:ℝ)/3) + 2)^3 := by
          rw [hXdef]
          have ha3 : ((x:ℝ)^((1:ℝ)/3))^3 = (x:ℝ) := rpow_third_pow _ hx0
          have hexp : ((x:ℝ)^((1:ℝ)/3) + 2)^3
              = ((x:ℝ)^((1:ℝ)/3))^3 + 6*((x:ℝ)^((1:ℝ)/3))^2 + 12*(x:ℝ)^((1:ℝ)/3) + 8 := by
            ring
          rw [hexp, ha3]
          have h6 : 0 ≤ 6*((x:ℝ)^((1:ℝ)/3))^2 :=
            mul_nonneg (by norm_num) (sq_nonneg _)
          have h12 : 0 ≤ 12*(x:ℝ)^((1:ℝ)/3) := mul_nonneg (by norm_num) ha
          linarith
        calc ((x:ℝ)+2)^((1:ℝ)/3) ≤ (((x:ℝ)^((1:ℝ)/3)+2)^3)^((1:ℝ)/3) :=
              Real.rpow_le_rpow (by positivity) h1 (by norm_num)
          _ = (x:ℝ)^((1:ℝ)/3) + 2 := rpow_third_cube _ (by positivity)
      linarith [hYge]
    have hBsq : (B:ℝ) ≤ Real.sqrt (((x:ℝ)+2)/qR) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have h := hBBR
      rw [hXdef] at h
      exact h
    exact innerIntegral_bound (x:ℝ) qR ((Y:ℝ)-1) ((B:ℝ)) hx1 hqR0 hq3 hexp hA' hABreal hBsq
  -- ## Part 4: the Abel error term
  have hErr : 2 * E * ((X / (qR * Real.log (X / (qR * ((Y:ℝ)-1)))))
        + (X / (qR * Real.log (X / (qR * (B:ℝ))))))
      ≤ 24 * E * (X/(qR*L)) := by
    have hFt : ∀ t : ℝ, (Y:ℝ)-1 ≤ t → t ≤ (B:ℝ) →
        X / (qR * Real.log (X/(qR*t))) ≤ 6 * (X/(qR*L)) := by
      intro t ht1 ht2
      obtain ⟨ht0, hXt⟩ := hmem t ⟨ht1, ht2⟩
      have hq_sq : t ≤ Real.sqrt X := by
        rw [Real.le_sqrt ht0.le hX0.le]
        have h1 : t^2 ≤ (B:ℝ)^2 := pow_le_pow_left₀ ht0.le ht2 2
        have h2 : (B:ℝ)^2 ≤ X := by
          have h3 : (B:ℝ)^2 ≤ qR*(B:ℝ)^2 := le_mul_of_one_le_left (sq_nonneg _) hqR1
          linarith
        linarith
      have hlogt : Real.log t ≤ L/2 := by
        rw [hLdef, ← Real.log_sqrt hX0.le]
        exact Real.log_le_log ht0 hq_sq
      have hloglow : L/6 ≤ Real.log (X/(qR*t)) := by
        have hsplit : Real.log (X/(qR*t)) = L - Real.log qR - Real.log t := by
          rw [Real.log_div hX0.ne' (mul_ne_zero hqR0.ne' ht0.ne'),
            Real.log_mul hqR0.ne' ht0.ne', hLdef]
          ring
        rw [hsplit]
        linarith [hlogq_le, hlogt]
      have h2 : X/(qR * Real.log (X/(qR*t))) ≤ X/(qR*(L/6)) := by
        apply div_le_div_of_nonneg_left hX0.le (by positivity : (0:ℝ) < qR*(L/6))
        exact mul_le_mul_of_nonneg_left hloglow hqR0.le
      have h3 : X/(qR*(L/6)) = 6*(X/(qR*L)) := by ring
      linarith [h2, h3.le, h3.ge]
    have h1 := hFt ((Y:ℝ)-1) le_rfl hABreal
    have h2 := hFt (B:ℝ) hABreal le_rfl
    have hE2 : (0:ℝ) ≤ 2*E := by linarith
    calc 2 * E * ((X / (qR * Real.log (X / (qR * ((Y:ℝ)-1)))))
          + (X / (qR * Real.log (X / (qR * (B:ℝ))))))
        ≤ 2 * E * (6*(X/(qR*L)) + 6*(X/(qR*L))) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) hE2
      _ = 24 * E * (X/(qR*L)) := by ring
  -- ## Assembly
  calc ((∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
        (Nat.primesLE ((x + 2) / (q * q₂))).card : ℕ) : ℝ)
      ≤ (1 + δ₁) * (∑ q₂ ∈ (Finset.Icc Y B).filter Nat.Prime,
          (X / (qR * Real.log (X / (qR * (q₂:ℝ))))) / (q₂:ℝ)) := hsum_bound
    _ ≤ (1 + δ₁) * ((∫ t in ((Y:ℝ) - 1)..((B:ℝ)),
            (X / (qR * Real.log (X / (qR * t)))) / (t * Real.log t))
          + 2 * E * ((X / (qR * Real.log (X / (qR * ((Y:ℝ)-1)))))
            + (X / (qR * Real.log (X / (qR * (B:ℝ))))))) :=
          mul_le_mul_of_nonneg_left hAbel (by linarith)
    _ ≤ (1 + δ₁) * ((X/qR) * (Real.log (2 - 3*(Real.log qR/L)) / ((1 - Real.log qR/L)*L)
            + 1000/((x:ℝ)^((1:ℝ)/3) * L)) + 24*E*(X/(qR*L))) :=
          mul_le_mul_of_nonneg_left (by linarith [hInt, hErr]) (by linarith)
    _ = (1 + δ₁) * (X/(qR*L) * Real.log (2 - 3*(Real.log qR/L)) / (1 - Real.log qR/L)
          + X/qR * (1000/((x:ℝ)^((1:ℝ)/3)*L)) + 24*E*(X/(qR*L))) := by field_simp

end Work.NumberTheory.Chen.BTermCount
