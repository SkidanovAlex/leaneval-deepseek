import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-! ## Auxiliary elementary estimates

The goal `Dc c (x / e) ≤ (∏_{p | e} (p+1)/(√p+1)) · Dc c x` is an exponent comparison:
with `Dc c y = exp(-(c √(log y)))` it is equivalent to
`c (√(log x) - √(log (x/e))) ≤ log (∏_{p|e} (p+1)/(√p+1))`.

The right hand side is bounded below by `(1/6)·log e` for squarefree `e ≥ 2` (each local factor
is at least `(4/5)√p`), while the left hand side is at most `c √(log (2e))`, and
`√(log (2e)) ≤ (8/3) log e`.  Since `c ≤ 1/16` the two meet. -/

/-- For `p ≥ 0`: `(p+1)/(√p+1) ≥ (4/5)·√p` (equivalent to `(√p-2)^2 + 1 ≥ 0`). -/
lemma KMDcDivLe_factor_ge (p : ℝ) (hp : 0 ≤ p) :
    (4 / 5) * Real.sqrt p ≤ (p + 1) / (Real.sqrt p + 1) := by
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < Real.sqrt p + 1)]
  have hsq : Real.sqrt p * Real.sqrt p = p := by
    rw [← sq, Real.sq_sqrt hp]
  nlinarith [sq_nonneg (Real.sqrt p - 2)]

/-- For `p ≥ 1`: `(p+1)/(√p+1) ≥ 1`. -/
lemma KMDcDivLe_factor_one_le (p : ℝ) (hp : 1 ≤ p) :
    (1 : ℝ) ≤ (p + 1) / (Real.sqrt p + 1) := by
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < Real.sqrt p + 1)]
  have h1 : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr hp
  have hsq : Real.sqrt p * Real.sqrt p = p := by
    rw [← sq, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ p)]
  nlinarith

/-- The full local factor is at least `1`. -/
lemma KMDcDivLe_prod_one_le (e : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1) := by
  have h := Finset.prod_le_prod₀ (s := e.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
    (g := fun p : ℕ => ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
    (fun _ _ => by norm_num)
    (fun p hp => KMDcDivLe_factor_one_le (p : ℝ)
      (by exact_mod_cast (le_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)))
  simpa using h

/-- For squarefree `e`, `2 ^ (number of prime factors of e) ≤ e`. -/
lemma KMDcDivLe_two_pow_card_le (e : ℕ) (he : Squarefree e) :
    2 ^ e.primeFactors.card ≤ e := by
  calc 2 ^ e.primeFactors.card = ∏ p ∈ e.primeFactors, (2 : ℕ) :=
        (Finset.prod_const 2).symm
    _ ≤ ∏ p ∈ e.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ = e := Nat.prod_primeFactors_of_squarefree he

/-- For squarefree `e`, `log e` is the sum of `log p` over the prime factors. -/
lemma KMDcDivLe_log_e_eq (e : ℕ) (he : Squarefree e) :
    Real.log (e : ℝ) = ∑ p ∈ e.primeFactors, Real.log (p : ℝ) := by
  have hprod : (∏ p ∈ e.primeFactors, (p : ℝ)) = (e : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree he]
  rw [← hprod, Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.pos_of_mem_primeFactors hp).ne'

/-- `log (∏_{p | e} (p+1)/(√p+1)) ≥ (1/6) log e` for squarefree `e ≥ 2`. -/
lemma KMDcDivLe_logProdLower (e : ℕ) (he : Squarefree e) (_he2 : 2 ≤ e) :
    (1 / 6) * Real.log (e : ℝ)
      ≤ Real.log (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
  have hfne : ∀ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1) ≠ 0 := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
    have hs : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
    exact ne_of_gt (div_pos (by linarith) (by linarith))
  rw [Real.log_prod hfne]
  have hterm : ∀ p ∈ e.primeFactors,
      Real.log ((4 / 5 : ℝ) * Real.sqrt (p : ℝ))
        ≤ Real.log (((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
    exact Real.log_le_log (by positivity) (KMDcDivLe_factor_ge (p : ℝ) hp0.le)
  have hsum : ∑ p ∈ e.primeFactors, Real.log ((4 / 5 : ℝ) * Real.sqrt (p : ℝ))
      = (e.primeFactors.card : ℝ) * Real.log (4 / 5) + (1 / 2) * Real.log (e : ℝ) := by
    have h1 : ∀ p ∈ e.primeFactors, Real.log ((4 / 5 : ℝ) * Real.sqrt (p : ℝ))
        = Real.log (4 / 5) + Real.log (p : ℝ) / 2 := by
      intro p hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_mem_primeFactors hp
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr hp0)), Real.log_sqrt hp0.le]
    have h2 : ∑ p ∈ e.primeFactors, Real.log (p : ℝ) = Real.log (e : ℝ) :=
      (KMDcDivLe_log_e_eq e he).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.sum_div, h2,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have hcard : 3 * ((e.primeFactors.card : ℝ) * Real.log (5 / 4)) ≤ Real.log (e : ℝ) := by
    have h2ω : (2 : ℝ) ^ e.primeFactors.card ≤ (e : ℝ) := by
      exact_mod_cast KMDcDivLe_two_pow_card_le e he
    have hlog : Real.log ((2 : ℝ) ^ e.primeFactors.card) ≤ Real.log (e : ℝ) :=
      Real.log_le_log (by positivity) h2ω
    rw [Real.log_pow] at hlog
    have h54 : 3 * Real.log (5 / 4) ≤ Real.log 2 := by
      have h1 : Real.log ((5 / 4 : ℝ) ^ 3) ≤ Real.log 2 :=
        Real.log_le_log (by norm_num) (by norm_num)
      rwa [Real.log_pow] at h1
    calc 3 * ((e.primeFactors.card : ℝ) * Real.log (5 / 4))
        = (e.primeFactors.card : ℝ) * (3 * Real.log (5 / 4)) := by ring
      _ ≤ (e.primeFactors.card : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left h54 (by positivity)
      _ ≤ Real.log (e : ℝ) := hlog
  have hmain : (1 / 6) * Real.log (e : ℝ)
      ≤ (e.primeFactors.card : ℝ) * Real.log (4 / 5) + (1 / 2) * Real.log (e : ℝ) := by
    have hrel : Real.log (4 / 5 : ℝ) = -Real.log (5 / 4) := by
      rw [show (4 / 5 : ℝ) = (5 / 4)⁻¹ by norm_num, Real.log_inv]
    rw [hrel]
    linarith
  calc (1 / 6) * Real.log (e : ℝ)
      ≤ (e.primeFactors.card : ℝ) * Real.log (4 / 5) + (1 / 2) * Real.log (e : ℝ) := hmain
    _ = ∑ p ∈ e.primeFactors, Real.log ((4 / 5 : ℝ) * Real.sqrt (p : ℝ)) := hsum.symm
    _ ≤ ∑ p ∈ e.primeFactors, Real.log (((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) :=
        Finset.sum_le_sum hterm

/-- `√(log (2e)) ≤ (8/3) log e` for `e ≥ 2`. -/
lemma KMDcDivLe_sqrtLogBound (e : ℕ) (he2 : 2 ≤ e) :
    Real.sqrt (Real.log (2 * (e : ℝ))) ≤ (8 / 3 : ℝ) * Real.log (e : ℝ) := by
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have hloge : 0 < Real.log (e : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < e))
  have hlog2le : Real.log (2 : ℝ) ≤ Real.log (e : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast he2)
  have hsplit : Real.log (2 * (e : ℝ)) = Real.log 2 + Real.log (e : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt heR)
  have hstep1 : Real.log (2 * (e : ℝ)) ≤ 2 * Real.log (e : ℝ) := by
    rw [hsplit]; linarith
  have hstep3 : Real.sqrt (2 * Real.log (e : ℝ)) ≤ (8 / 3 : ℝ) * Real.log (e : ℝ) := by
    rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ (8 / 3 : ℝ) * Real.log (e : ℝ))]
    have h : (9 / 32 : ℝ) ≤ Real.log (e : ℝ) := by
      have := Real.log_two_gt_d9
      linarith
    have h2 : (2 : ℝ) ≤ (64 / 9) * Real.log (e : ℝ) := by linarith
    have h3 : (2 : ℝ) * Real.log (e : ℝ)
        ≤ ((64 / 9) * Real.log (e : ℝ)) * Real.log (e : ℝ) :=
      mul_le_mul_of_nonneg_right h2 hloge.le
    calc (2 : ℝ) * Real.log (e : ℝ)
        ≤ ((64 / 9) * Real.log (e : ℝ)) * Real.log (e : ℝ) := h3
      _ = ((8 / 3 : ℝ) * Real.log (e : ℝ)) ^ 2 := by ring
  calc Real.sqrt (Real.log (2 * (e : ℝ)))
      ≤ Real.sqrt (2 * Real.log (e : ℝ)) := Real.sqrt_le_sqrt hstep1
    _ ≤ (8 / 3 : ℝ) * Real.log (e : ℝ) := hstep3

/-- `√b - √a ≤ √(b-a)` for `0 ≤ a ≤ b`. -/
lemma KMDcDivLe_sqrt_sub_sqrt (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b - a) := by
  have hb : 0 ≤ b := le_trans ha hab
  have hba : 0 ≤ b - a := by linarith
  have hxa : 0 ≤ Real.sqrt b - Real.sqrt a := sub_nonneg.mpr (Real.sqrt_le_sqrt hab)
  rw [Real.le_sqrt hxa hba]
  have h1 : (Real.sqrt b - Real.sqrt a) ^ 2 = b + a - 2 * Real.sqrt (a * b) := by
    rw [sub_sq, Real.sq_sqrt hb, Real.sq_sqrt ha, Real.sqrt_mul ha b]
    ring
  rw [h1]
  have hle : a ≤ Real.sqrt (a * b) := by
    rw [Real.le_sqrt ha (by positivity : (0 : ℝ) ≤ a * b)]
    nlinarith
  linarith

/-- The exponent comparison behind `KMDcDivLe`. -/
theorem KMDcDivLe_key (c : ℝ) (hc : 0 < c) (hc16 : c ≤ 1 / 16) (x e : ℕ) (he : Squarefree e) :
    c * (Real.sqrt (Real.log (x : ℝ)) - Real.sqrt (Real.log ((x / e : ℕ) : ℝ)))
      ≤ Real.log (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) := by
  set m : ℕ := x / e with hm
  set A : ℝ := ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1) with hA
  by_cases he1 : e = 1
  · have hm1 : m = x := by rw [hm, he1, Nat.div_one]
    rw [hm1]
    have hpf : (1 : ℕ).primeFactors = ∅ := by simp
    rw [hA, he1, hpf]
    simp
  · have he0 : e ≠ 0 := fun h => by rw [h] at he; exact not_squarefree_zero he
    have he2 : 2 ≤ e := by omega
    have hepos : 0 < e := by omega
    have hA1 : (1 : ℝ) ≤ A := by rw [hA]; exact KMDcDivLe_prod_one_le e
    have hlogA : (1 / 6) * Real.log (e : ℝ) ≤ Real.log A := by
      rw [hA]; exact KMDcDivLe_logProdLower e he he2
    have hbound : c * Real.sqrt (Real.log (2 * (e : ℝ))) ≤ Real.log A := by
      have h1 : c * Real.sqrt (Real.log (2 * (e : ℝ)))
          ≤ (1 / 16) * Real.sqrt (Real.log (2 * (e : ℝ))) :=
        mul_le_mul_of_nonneg_right hc16 (Real.sqrt_nonneg _)
      have h2 : (1 / 16 : ℝ) * Real.sqrt (Real.log (2 * (e : ℝ)))
          ≤ (1 / 16 : ℝ) * ((8 / 3 : ℝ) * Real.log (e : ℝ)) :=
        mul_le_mul_of_nonneg_left (KMDcDivLe_sqrtLogBound e he2) (by norm_num)
      have h3 : (1 / 16 : ℝ) * ((8 / 3 : ℝ) * Real.log (e : ℝ))
          = (1 / 6) * Real.log (e : ℝ) := by ring
      linarith
    have hexp : Real.sqrt (Real.log (x : ℝ)) - Real.sqrt (Real.log (m : ℝ))
        ≤ Real.sqrt (Real.log (2 * (e : ℝ))) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · have hxe : x < e := by
          rw [hm] at hm0
          exact (Nat.div_eq_zero_iff_lt hepos).mp hm0
        rw [hm0]
        simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero, sub_zero]
        apply Real.sqrt_le_sqrt
        rcases Nat.eq_zero_or_pos x with hx0 | hxpos
        · rw [hx0]
          simp only [Nat.cast_zero, Real.log_zero]
          have heR : (1 : ℝ) ≤ 2 * (e : ℝ) := by
            have : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast (by omega : 1 ≤ e)
            linarith
          exact Real.log_nonneg heR
        · have hxle : (x : ℝ) ≤ 2 * (e : ℝ) := by
            have : (x : ℝ) ≤ (e : ℝ) := by exact_mod_cast (by omega : x ≤ e)
            linarith
          exact Real.log_le_log (by positivity) hxle
      · have hmx : m ≤ x := by rw [hm]; exact Nat.div_le_self x e
        have hlt : x < 2 * e * m := by
          have hx_eq : x = e * m + x % e := by
            rw [hm]; exact (Nat.div_add_mod x e).symm
          have hmod : x % e < e := Nat.mod_lt x hepos
          have h2 : x < e * m + e := by omega
          have h3 : e * m + e = e * (m + 1) := by ring
          have h4 : e * (m + 1) ≤ 2 * e * m := by
            calc e * (m + 1) ≤ e * (2 * m) := Nat.mul_le_mul_left e (by omega)
              _ = 2 * e * m := by ring
          exact lt_of_lt_of_le (h3 ▸ h2) h4
        have hxR : (x : ℝ) < 2 * (e : ℝ) * (m : ℝ) := by
          have hcast : ((2 * e * m : ℕ) : ℝ) = 2 * (e : ℝ) * (m : ℝ) := by push_cast; ring
          rw [← hcast]
          exact_mod_cast hlt
        have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
        have hxposR : (0 : ℝ) < (x : ℝ) := by
          have : 0 < x := lt_of_lt_of_le hmpos hmx
          exact_mod_cast this
        have hdiv : (x : ℝ) / (m : ℝ) < 2 * (e : ℝ) := (div_lt_iff₀ hmR).mpr hxR
        have hlogineq : Real.log ((x : ℝ) / (m : ℝ)) ≤ Real.log (2 * (e : ℝ)) :=
          Real.log_le_log (div_pos hxposR hmR) hdiv.le
        have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hmpos)
        have hlogmx : Real.log (m : ℝ) ≤ Real.log (x : ℝ) :=
          Real.log_le_log hmR (by exact_mod_cast hmx)
        calc Real.sqrt (Real.log (x : ℝ)) - Real.sqrt (Real.log (m : ℝ))
            ≤ Real.sqrt (Real.log (x : ℝ) - Real.log (m : ℝ)) :=
              KMDcDivLe_sqrt_sub_sqrt _ _ hlogm_nn hlogmx
          _ = Real.sqrt (Real.log ((x : ℝ) / (m : ℝ))) := by
              rw [Real.log_div (ne_of_gt hxposR) (ne_of_gt hmR)]
          _ ≤ Real.sqrt (Real.log (2 * (e : ℝ))) := Real.sqrt_le_sqrt hlogineq
    calc c * (Real.sqrt (Real.log (x : ℝ)) - Real.sqrt (Real.log (m : ℝ)))
        ≤ c * Real.sqrt (Real.log (2 * (e : ℝ))) := mul_le_mul_of_nonneg_left hexp hc.le
      _ ≤ Real.log A := hbound

/-- **Comparison of the exponential envelope at `x / e` and at `x`.** -/
theorem KMDcDivLe (c : ℝ) (hc : 0 < c) (hc16 : c ≤ 1 / 16) (x e : ℕ) (he : Squarefree e) :
    Dc c (x / e)
      ≤ (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) * Dc c x := by
  have hkey := KMDcDivLe_key c hc hc16 x e he
  have hApos : 0 < ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1) :=
    lt_of_lt_of_le zero_lt_one (KMDcDivLe_prod_one_le e)
  calc Dc c (x / e)
      = Real.exp (c * (Real.sqrt (Real.log (x : ℝ)) - Real.sqrt (Real.log ((x / e : ℕ) : ℝ)))
            - c * Real.sqrt (Real.log (x : ℝ))) := by
        rw [Dc]; congr 1; ring
    _ ≤ Real.exp (Real.log (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
            - c * Real.sqrt (Real.log (x : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ = (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1)) * Dc c x := by
        rw [Real.exp_sub, Real.exp_log hApos, Dc, Real.exp_neg]
        ring

end

end Work.ZeroDensity.Jutila
