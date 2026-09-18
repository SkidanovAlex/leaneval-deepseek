import Mathlib
import Mathlib.NumberTheory.SelbergSieve
import Submission.Commons.NumberTheory.Totient.coprime_window_mainTerm_bound
import Submission.Commons.Data.Nat.moebiusInversionRoundTrip
import Submission.Commons.NumberTheory.Totient.sum_sigma_div_totient_divisors_le_four_mul

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

noncomputable section

/-- The arithmetic function `d ↦ 1/d`, ℝ-valued. -/
private def invArith : ArithmeticFunction ℝ := ⟨fun d => (1 : ℝ) / d, by simp⟩

private lemma invArith_mult : ArithmeticFunction.IsMultiplicative invArith := by
  constructor
  · simp [invArith]
  · intro a b hab
    by_cases ha0 : a = 0
    · subst ha0
      have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
      subst hb; simp [invArith]
    · by_cases hb0 : b = 0
      · subst hb0
        have ha : a = 1 := (Nat.coprime_zero_right a).mp hab
        subst ha; simp [invArith]
      · simp only [invArith, ArithmeticFunction.coe_mk, one_div]
        rw [Nat.cast_mul, mul_inv_rev, mul_comm]

/-- The coprime-window sieve as a `BoundingSieve`. -/
private def windowSieve (P y : ℕ) (hP : Squarefree P) : BoundingSieve where
  support := Finset.Icc 1 y
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (y : ℝ)
  nu := invArith
  nu_mult := invArith_mult
  nu_pos_of_prime := by
    intro p hp hpd
    simp only [invArith, ArithmeticFunction.coe_mk]
    exact one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp hpd
    simp only [invArith, ArithmeticFunction.coe_mk]
    rw [one_div]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private lemma window_multSum (P y : ℕ) (hP : Squarefree P) (d : ℕ) :
    (windowSieve P y hP).multSum d = ((y / d : ℕ) : ℝ) := by
  classical
  unfold BoundingSieve.multSum
  rw [show (windowSieve P y hP).support = Finset.Icc 1 y by rfl]
  rw [show (windowSieve P y hP).weights = (fun _ : ℕ => (1 : ℝ)) by rfl]
  rw [Finset.sum_boole]
  exact_mod_cast card_multiples_Icc_one d y

private lemma window_rem_eq (P y : ℕ) (hP : Squarefree P) (d : ℕ) :
    (windowSieve P y hP).rem d = ((y / d : ℕ) : ℝ) - (y : ℝ) / (d : ℝ) := by
  rw [BoundingSieve.rem, window_multSum]
  rw [show (windowSieve P y hP).nu d = (1:ℝ)/d by rfl]
  rw [show (windowSieve P y hP).totalMass = (y:ℝ) by rfl]
  ring

private lemma window_rem_abs_le (P y : ℕ) (hP : Squarefree P) (d : ℕ) (hd : 1 ≤ d) :
    |(windowSieve P y hP).rem d| ≤ 1 := by
  rw [window_rem_eq]
  exact floor_div_sub_le_one y d hd

private lemma window_siftedSum (P y : ℕ) (hP : Squarefree P) :
    (windowSieve P y hP).siftedSum =
      (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ) := by
  classical
  unfold BoundingSieve.siftedSum
  rw [show (windowSieve P y hP).support = Finset.Icc 1 y by rfl]
  rw [show (windowSieve P y hP).prodPrimes = P by rfl]
  rw [show (windowSieve P y hP).weights = (fun _ : ℕ => (1 : ℝ)) by rfl]
  rw [Finset.sum_boole]
  have : (Finset.Icc 1 y).filter (fun d : ℕ => P.Coprime d) =
      (Finset.Icc 1 y).filter (fun c : ℕ => c.Coprime P) := by
    apply Finset.filter_congr
    intro c hc
    exact Nat.coprime_comm
  rw [this]

private lemma totient_ratio_real (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / (n : ℝ) =
      ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  have hmain := Nat.totient_mul_prod_primeFactors n
  have hcast : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ)) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hmain
    push_cast at this
    simpa using this
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpR : (∏ p ∈ n.primeFactors, (p : ℝ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  have key : (Nat.totient n : ℝ) / (n : ℝ) =
      (∏ p ∈ n.primeFactors, (((p - 1 : ℕ) : ℝ))) / ∏ p ∈ n.primeFactors, (p : ℝ) := by
    field_simp [hnR, hpR]
    linarith [hcast]
  rw [key, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpge : 1 ≤ p := Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)
  have hpne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
  rw [Nat.cast_sub hpge, one_div]
  field_simp
  norm_num

private lemma window_selbergTerms (P y : ℕ) (hP : Squarefree P) (l : ℕ) (hl : l ≠ 0) :
    (windowSieve P y hP).selbergTerms l = (Nat.totient l : ℝ)⁻¹ := by
  rw [BoundingSieve.selbergTerms_apply]
  rw [show (windowSieve P y hP).nu = invArith from rfl]
  simp only [invArith, ArithmeticFunction.coe_mk]
  have hprod : ∏ p ∈ l.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) =
      (Nat.totient l : ℝ) / (l : ℝ) := (totient_ratio_real l hl).symm
  rw [Finset.prod_inv_distrib, hprod]
  have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  have hphi : (Nat.totient l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl)).ne'
  field_simp
/-! ## The truncated Selberg sum and the explicit optimal weight -/

/-- `S(z) = Σ_{d | P, d ≤ z} 1/φ(d)`. -/
private def truncSum (P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then (Nat.totient d : ℝ)⁻¹ else 0

private lemma truncSum_eq_filter (P z : ℕ) :
    truncSum P z = ∑ d ∈ P.divisors.filter (fun d => d ≤ z), (Nat.totient d : ℝ)⁻¹ := by
  rw [truncSum, ← Finset.sum_filter]

private lemma truncSum_pos (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) : 0 < truncSum P z := by
  rw [truncSum]
  have hmem : 1 ∈ P.divisors := by
    rw [Nat.mem_divisors]; exact ⟨one_dvd P, hP.ne_zero⟩
  calc (0 : ℝ) < ((Nat.totient 1 : ℝ))⁻¹ := by norm_num
    _ = (if (1 : ℕ) ≤ z then (Nat.totient 1 : ℝ)⁻¹ else 0) := by rw [if_pos hz]
    _ ≤ ∑ d ∈ P.divisors, if d ≤ z then (Nat.totient d : ℝ)⁻¹ else 0 :=
        Finset.single_le_sum (f := fun d => if d ≤ z then (Nat.totient d : ℝ)⁻¹ else 0)
          (fun d _ => by positivity) hmem


private lemma dT_sum_eq (P z : ℕ) (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
        if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0)
      = ∑ l' ∈ P.divisors.filter (fun l' => l' ≤ z),
          ((ArithmeticFunction.sigma 1 l' : ℕ) : ℝ) / (Nat.totient l' : ℝ) := by
  classical
  have hP0 : P ≠ 0 := hP.ne_zero
  have hstep : (∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
        if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0))
      = ∑ l' ∈ P.divisors, (if l' ≤ z then
          (Nat.totient l' : ℝ)⁻¹ * (∑ d ∈ P.divisors, if d ∣ l' then (d : ℝ) else 0) else 0) := by
    rw [show (∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
          if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0))
        = ∑ d ∈ P.divisors, ∑ l' ∈ P.divisors,
            (d : ℝ) * (if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) by
      apply Finset.sum_congr rfl; intro d _; rw [Finset.mul_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l' _
    by_cases hlz : l' ≤ z
    · rw [if_pos hlz]
      rw [show (∑ d ∈ P.divisors,
            (d : ℝ) * (if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0))
          = ∑ d ∈ P.divisors, (if d ∣ l' then (d : ℝ) else 0) * (Nat.totient l' : ℝ)⁻¹ by
        apply Finset.sum_congr rfl; intro d _
        by_cases hdl : d ∣ l'
        · rw [if_pos ⟨hdl, hlz⟩, if_pos hdl]
        · rw [if_neg (fun h => hdl h.1), if_neg hdl]; ring]
      rw [← Finset.sum_mul]; ring
    · rw [if_neg hlz]
      apply Finset.sum_eq_zero; intro d _
      rw [if_neg (fun h => hlz h.2)]; ring
  rw [hstep, ← Finset.sum_filter]
  apply Finset.sum_congr rfl; intro l' hl'
  have hl'P : l' ∈ P.divisors := (Finset.mem_filter.mp hl').1
  have hl'0 : l' ≠ 0 := ne_zero_of_dvd_ne_zero hP0 (Nat.dvd_of_mem_divisors hl'P)
  have hsig : (∑ d ∈ P.divisors, if d ∣ l' then (d : ℝ) else 0)
      = ((ArithmeticFunction.sigma 1 l' : ℕ) : ℝ) := by
    have hfilter : P.divisors.filter (fun d => d ∣ l') = l'.divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdP, _⟩, hdl'⟩; exact ⟨hdl', hl'0⟩
      · rintro ⟨hdl', _⟩
        exact ⟨⟨hdl'.trans (Nat.dvd_of_mem_divisors hl'P), hP0⟩, hdl'⟩
    rw [show (∑ d ∈ P.divisors, (if d ∣ l' then (d : ℝ) else 0))
        = ∑ d ∈ P.divisors.filter (fun d => d ∣ l'), (d : ℝ) from (Finset.sum_filter _ _).symm]
    rw [hfilter, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  rw [hsig, div_eq_mul_inv]
  ring

private lemma dT_sum_le (P z : ℕ) (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
        if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) ≤ 4 * (z : ℝ) := by
  rw [dT_sum_eq P z hP]
  exact sum_sigma_div_totient_divisors_le_four_mul P z hP

/-- The Selberg `y`-coordinate: `y⁰ l = μ(l)·(1/φ(l))/S` for `l ≤ z`, `0` otherwise. -/
private def yZero (z : ℕ) (S : ℝ) (l : ℕ) : ℝ :=
  if l ≤ z then (ArithmeticFunction.moebius l : ℝ) * (Nat.totient l : ℝ)⁻¹ / S else 0

/-- The explicit Selberg weight `w(d) = d·Σ_{l' : d | l'} μ(l'/d)·y⁰(l')`. -/
private def solW (P z : ℕ) (S : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * ∑ l' ∈ P.divisors,
    if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0

private lemma moebius_sq_one_of_mem_divisors {P l : ℕ} (hP : Squarefree P)
    (hl : l ∈ P.divisors) : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
  have hsq : Squarefree l := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hl)
  have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
  exact_mod_cast this

private lemma solW_one (P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    solW P z (truncSum P z) 1 = 1 := by
  unfold solW
  rw [Nat.cast_one, one_mul]
  have hterm : ∀ l' ∈ P.divisors,
      (if (1 : ℕ) ∣ l' then
          (ArithmeticFunction.moebius (l' / 1) : ℝ) * yZero z (truncSum P z) l' else 0)
        = (if l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) / (truncSum P z) := by
    intro l' hl'
    rw [if_pos (one_dvd l'), Nat.div_one]
    unfold yZero
    by_cases hlz : l' ≤ z
    · rw [if_pos hlz, if_pos hlz]
      have hsq : (ArithmeticFunction.moebius l' : ℝ) ^ 2 = 1 :=
        moebius_sq_one_of_mem_divisors hP hl'
      rw [show (ArithmeticFunction.moebius l' : ℝ) *
            ((ArithmeticFunction.moebius l' : ℝ) * (Nat.totient l' : ℝ)⁻¹ / (truncSum P z))
          = ((ArithmeticFunction.moebius l' : ℝ)) ^ 2 *
            ((Nat.totient l' : ℝ)⁻¹ / (truncSum P z)) by ring]
      rw [hsq, one_mul, div_eq_mul_inv]
    · rw [if_neg hlz, if_neg hlz]
      simp
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div, ← Finset.sum_filter, ← truncSum_eq_filter]
  exact div_self (ne_of_gt (truncSum_pos P z hP hz))

/-- The Selberg diagonalisation coordinate `Σ_{d : l | d} ν d · w d` equals `y⁰ l`. -/
private lemma solW_lambdaY (P y l : ℕ) (hP : Squarefree P) (hlP : l ∣ P) :
    (∑ d ∈ P.divisors,
        if l ∣ d then
          (windowSieve P y hP).nu d * solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d
        else 0)
      = yZero (Nat.sqrt y) (truncSum P (Nat.sqrt y)) l := by
  have hterm : ∀ d ∈ P.divisors,
      (if l ∣ d then
          (windowSieve P y hP).nu d * solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d else 0)
        = (if l ∣ d then
            (∑ l' ∈ P.divisors, if d ∣ l' then
              (ArithmeticFunction.moebius (l' / d) : ℝ) *
                yZero (Nat.sqrt y) (truncSum P (Nat.sqrt y)) l' else 0)
          else 0) := by
    intro d hd
    by_cases hld : l ∣ d
    · rw [if_pos hld, if_pos hld]
      unfold solW
      rw [show (windowSieve P y hP).nu d = (1 : ℝ) / d from rfl]
      have hd0 : (d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
    · rw [if_neg hld, if_neg hld]
  rw [Finset.sum_congr rfl hterm]
  exact Commons.Data.Nat.moebiusInversionRoundTrip P hP
    (yZero (Nat.sqrt y) (truncSum P (Nat.sqrt y))) l hlP

/-- The main term is exactly `S(z)⁻¹`. -/
private lemma solW_mainSum (P y : ℕ) (hP : Squarefree P) (hy1 : 1 ≤ y) :
    (windowSieve P y hP).mainSum
        (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))))
      = (truncSum P (Nat.sqrt y))⁻¹ := by
  have hz1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by omega)
  have hSpos : 0 < truncSum P (Nat.sqrt y) := truncSum_pos P (Nat.sqrt y) hP hz1
  have hSne : truncSum P (Nat.sqrt y) ≠ 0 := ne_of_gt hSpos
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  rw [show (windowSieve P y hP).prodPrimes = P from rfl]
  have hterm : ∀ l ∈ P.divisors,
      ((windowSieve P y hP).selbergTerms l)⁻¹ *
        (∑ d ∈ P.divisors, if l ∣ d then
          (windowSieve P y hP).nu d * solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d else 0) ^ 2
      = (if l ≤ Nat.sqrt y then (Nat.totient l : ℝ)⁻¹ / (truncSum P (Nat.sqrt y)) ^ 2 else 0) := by
    intro l hl
    have hl0 : l ≠ 0 := (Nat.pos_of_mem_divisors hl).ne'
    have hlP : l ∣ P := Nat.dvd_of_mem_divisors hl
    rw [show ((windowSieve P y hP).selbergTerms l)⁻¹ = (Nat.totient l : ℝ) from by
      rw [window_selbergTerms P y hP l hl0, inv_inv]]
    rw [solW_lambdaY P y l hP hlP]
    unfold yZero
    by_cases hlz : l ≤ Nat.sqrt y
    · rw [if_pos hlz, if_pos hlz]
      have hsq : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := moebius_sq_one_of_mem_divisors hP hl
      have hphi : (Nat.totient l : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hl0)).ne'
      rw [show (Nat.totient l : ℝ) *
            ((ArithmeticFunction.moebius l : ℝ) * (Nat.totient l : ℝ)⁻¹ /
              (truncSum P (Nat.sqrt y))) ^ 2
          = (Nat.totient l : ℝ)⁻¹ / (truncSum P (Nat.sqrt y)) ^ 2 by
        rw [div_pow, mul_pow, hsq, one_mul]
        field_simp]
    · rw [if_neg hlz, if_neg hlz]; ring
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∀ l, (if l ≤ Nat.sqrt y then (Nat.totient l : ℝ)⁻¹ / (truncSum P (Nat.sqrt y)) ^ 2 else 0)
      = (if l ≤ Nat.sqrt y then (Nat.totient l : ℝ)⁻¹ else 0) / (truncSum P (Nat.sqrt y)) ^ 2 := by
    intro l; by_cases h : l ≤ Nat.sqrt y <;> simp [h]
  rw [Finset.sum_congr rfl (fun l _ => hsplit l)]
  rw [← Finset.sum_div, ← Finset.sum_filter, ← truncSum_eq_filter]
  field_simp

/-- `Σ_{d | P} |λ²w d| ≤ (Σ_{d | P} |w d|)²` when `w` vanishes off the divisors of `P`. -/
private lemma sum_abs_lambdaSquared_le (P : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d, d ∉ P.divisors → w d = 0) :
    ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| ≤ (∑ d ∈ P.divisors, |w d|) ^ 2 := by
  classical
  rcases eq_or_ne P 0 with hPzero | hP0
  · subst hPzero
    simp
  have hinner : ∀ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d| ≤
      ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) := by
    intro d hd
    have hsub : d.divisors ⊆ P.divisors := by
      intro x hx
      rw [Nat.mem_divisors] at hx ⊢
      exact ⟨hx.1.trans (Nat.dvd_of_mem_divisors hd), hP0⟩
    calc |BoundingSieve.lambdaSquared w d|
        = |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            (if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)| := by rfl
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            |(if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)| := by
          calc _ ≤ ∑ d1 ∈ d.divisors,
                |∑ d2 ∈ d.divisors, (if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                |(if d = Nat.lcm d1 d2 then w d1 * w d2 else 0)| :=
                Finset.sum_le_sum (fun d1 _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) := by
          apply Finset.sum_le_sum; intro d1 _
          apply Finset.sum_le_sum; intro d2 _
          by_cases hl : Nat.lcm d1 d2 = d
          · rw [if_pos hl, if_pos hl.symm]; exact le_of_eq (by rw [abs_mul])
          · rw [if_neg hl, if_neg (fun h => hl h.symm)]; simp
      _ ≤ ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
            (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) := by
          have h1 : ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
                (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0)
              ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ P.divisors,
                (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) := by
            apply Finset.sum_le_sum; intro d1 _
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
          refine le_trans h1 ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
  calc ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|
      ≤ ∑ d ∈ P.divisors, ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors,
          (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) :=
        Finset.sum_le_sum hinner
    _ = ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, ∑ d ∈ P.divisors,
          (if Nat.lcm d1 d2 = d then |w d1| * |w d2| else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro d1 _
        rw [Finset.sum_comm]
    _ = ∑ d1 ∈ P.divisors, ∑ d2 ∈ P.divisors, |w d1| * |w d2| := by
        apply Finset.sum_congr rfl; intro d1 hd1
        apply Finset.sum_congr rfl; intro d2 hd2
        have hlcm_mem : Nat.lcm d1 d2 ∈ P.divisors := by
          rw [Nat.mem_divisors]
          exact ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd1) (Nat.dvd_of_mem_divisors hd2), hP0⟩
        rw [Finset.sum_ite_eq P.divisors (Nat.lcm d1 d2) (fun _ => |w d1| * |w d2|),
          if_pos hlcm_mem]
    _ = (∑ d ∈ P.divisors, |w d|) ^ 2 := by rw [sq, Finset.sum_mul_sum]

private lemma solW_support (P z : ℕ) (S : ℝ) {d : ℕ} (hd : d ∉ P.divisors) :
    solW P z S d = 0 := by
  unfold solW
  have hsum : (∑ l' ∈ P.divisors, if d ∣ l' then
      (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro l' hl'
    by_cases hdl : d ∣ l'
    · have hP0 : P ≠ 0 := fun h => by rw [h] at hl'; simp at hl'
      exact absurd (Nat.mem_divisors.mpr ⟨hdl.trans (Nat.dvd_of_mem_divisors hl'), hP0⟩) hd
    · simp [hdl]
  rw [hsum, mul_zero]

private lemma abs_yZero_le (z : ℕ) (S : ℝ) (hSpos : 0 < S) (l : ℕ) (hlz : l ≤ z) :
    |yZero z S l| ≤ (Nat.totient l : ℝ)⁻¹ / S := by
  unfold yZero
  rw [if_pos hlz, abs_div, abs_of_pos hSpos, abs_mul]
  have h1 : |(ArithmeticFunction.moebius l : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := l)
    exact_mod_cast this
  have h2 : |(Nat.totient l : ℝ)⁻¹| = (Nat.totient l : ℝ)⁻¹ :=
    abs_of_nonneg (by positivity)
  rw [h2]
  calc |(ArithmeticFunction.moebius l : ℝ)| * (Nat.totient l : ℝ)⁻¹ / S
      ≤ 1 * (Nat.totient l : ℝ)⁻¹ / S := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hSpos)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (Nat.totient l : ℝ)⁻¹ / S := by rw [one_mul]

private lemma solW_abs_le (P z : ℕ) (S : ℝ) (hSpos : 0 < S) (d : ℕ) :
    |solW P z S d| ≤
      (d : ℝ) * (∑ l' ∈ P.divisors,
        if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) / S := by
  have hinner : |(∑ l' ∈ P.divisors,
        if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0)|
      ≤ (∑ l' ∈ P.divisors, if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) / S := by
    rw [le_div_iff₀ hSpos]
    calc |∑ l' ∈ P.divisors,
            (if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0)| * S
        ≤ (∑ l' ∈ P.divisors,
            |(if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0)|) * S := by
          apply mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (le_of_lt hSpos)
      _ = ∑ l' ∈ P.divisors,
            |(if d ∣ l' then (ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l' else 0)| * S := by
          rw [Finset.sum_mul]
      _ ≤ ∑ l' ∈ P.divisors, (if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) := by
          apply Finset.sum_le_sum; intro l' _
          by_cases hdl : d ∣ l'
          · rw [if_pos hdl]
            have hmu : |(ArithmeticFunction.moebius (l' / d) : ℝ)| ≤ 1 := by
              have := ArithmeticFunction.abs_moebius_le_one (n := l' / d)
              exact_mod_cast this
            by_cases hlz : l' ≤ z
            · rw [if_pos ⟨hdl, hlz⟩]
              calc |(ArithmeticFunction.moebius (l' / d) : ℝ) * yZero z S l'| * S
                  = |(ArithmeticFunction.moebius (l' / d) : ℝ)| * |yZero z S l'| * S := by
                    rw [abs_mul]
                _ ≤ 1 * ((Nat.totient l' : ℝ)⁻¹ / S) * S := by
                    apply mul_le_mul_of_nonneg_right _ (le_of_lt hSpos)
                    exact mul_le_mul hmu (abs_yZero_le z S hSpos l' hlz) (abs_nonneg _) (by norm_num)
                _ = (Nat.totient l' : ℝ)⁻¹ := by
                    rw [one_mul, div_mul_cancel₀ _ (ne_of_gt hSpos)]
            · rw [if_neg (fun h => hlz h.2)]
              have : yZero z S l' = 0 := by unfold yZero; rw [if_neg hlz]
              rw [this, mul_zero, abs_zero, zero_mul]
          · rw [if_neg hdl, if_neg (fun h => hdl h.1)]; simp
  unfold solW
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d), mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg d)

private lemma solW_sum_abs_le (P z : ℕ) (S : ℝ) (_hP : Squarefree P) (hSpos : 0 < S)
    (hH : ∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
        if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) ≤ 4 * (z : ℝ)) :
    ∑ d ∈ P.divisors, |solW P z S d| ≤ 4 * (z : ℝ) / S := by
  calc ∑ d ∈ P.divisors, |solW P z S d|
      ≤ ∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
          if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0) / S :=
        Finset.sum_le_sum (fun d _ => solW_abs_le P z S hSpos d)
    _ = (∑ d ∈ P.divisors, (d : ℝ) * (∑ l' ∈ P.divisors,
          if d ∣ l' ∧ l' ≤ z then (Nat.totient l' : ℝ)⁻¹ else 0)) / S := by
        rw [Finset.sum_div]
    _ ≤ 4 * (z : ℝ) / S := div_le_div_of_nonneg_right hH (le_of_lt hSpos)

private lemma solW_errSum_le (P y : ℕ) (hP : Squarefree P) (hy1 : 1 ≤ y) :
    (windowSieve P y hP).errSum
        (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))))
      ≤ (4 * (Nat.sqrt y : ℝ) / truncSum P (Nat.sqrt y)) ^ 2 := by
  have hz1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by omega)
  have hSpos : 0 < truncSum P (Nat.sqrt y) := truncSum_pos P (Nat.sqrt y) hP hz1
  have hH := dT_sum_le P (Nat.sqrt y) hP
  have h1 : (windowSieve P y hP).errSum
      (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))))
      ≤ ∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d| := by
    unfold BoundingSieve.errSum
    rw [show (windowSieve P y hP).prodPrimes = P from rfl]
    apply Finset.sum_le_sum; intro d hd
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_mem_divisors hd)
    calc |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d|
            * |(windowSieve P y hP).rem d|
        ≤ |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d| * 1 :=
          mul_le_mul_of_nonneg_left (window_rem_abs_le P y hP d hd1) (abs_nonneg _)
      _ = |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d| := by rw [mul_one]
  have h2 : ∑ d ∈ P.divisors,
        |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d|
      ≤ (∑ d ∈ P.divisors, |solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d|) ^ 2 := by
    apply sum_abs_lambdaSquared_le
    intro d hd
    exact solW_support P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) hd
  have h3 : ∑ d ∈ P.divisors, |solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d|
      ≤ 4 * (Nat.sqrt y : ℝ) / truncSum P (Nat.sqrt y) :=
    solW_sum_abs_le P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) hP hSpos hH
  calc (windowSieve P y hP).errSum
          (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))))
      ≤ ∑ d ∈ P.divisors,
          |BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y))) d| := h1
    _ ≤ (∑ d ∈ P.divisors, |solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d|) ^ 2 := h2
    _ ≤ (4 * (Nat.sqrt y : ℝ) / truncSum P (Nat.sqrt y)) ^ 2 := by
        have hnn : 0 ≤ ∑ d ∈ P.divisors, |solW P (Nat.sqrt y) (truncSum P (Nat.sqrt y)) d| :=
          Finset.sum_nonneg (fun d _ => abs_nonneg _)
        have h4nn : 0 ≤ 4 * (Nat.sqrt y : ℝ) / truncSum P (Nat.sqrt y) := by positivity
        nlinarith [h3, hnn, h4nn]

/-! ## The final count bound -/

theorem selberg_window_count_le (P y : ℕ) (hP : Squarefree P) (hy1 : 1 ≤ y) :
    (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ) ≤
      (y : ℝ) / (∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0)
      + (4 * (Nat.sqrt y : ℝ) / (∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0))^2 := by
  set S : ℝ := ∑ d ∈ P.divisors, if d ≤ Nat.sqrt y then (Nat.totient d : ℝ)⁻¹ else 0 with hS
  have hSz : S = truncSum P (Nat.sqrt y) := by rw [hS, truncSum]
  have hw1 : solW P (Nat.sqrt y) S 1 = 1 := by rw [hSz]; exact solW_one P (Nat.sqrt y) hP (Nat.le_sqrt.mpr (by omega))
  have hup := BoundingSieve.upperMoebius_lambdaSquared (solW P (Nat.sqrt y) S) hw1
  have hsel := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius (s := windowSieve P y hP)
      (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) S)) hup
  rw [window_siftedSum] at hsel
  have hmain : (windowSieve P y hP).mainSum
      (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) S)) = S⁻¹ := by
    rw [hSz]; exact solW_mainSum P y hP hy1
  have herr : (windowSieve P y hP).errSum
      (BoundingSieve.lambdaSquared (solW P (Nat.sqrt y) S)) ≤ (4 * (Nat.sqrt y : ℝ) / S) ^ 2 := by
    rw [hSz]; exact solW_errSum_le P y hP hy1
  rw [show (windowSieve P y hP).totalMass = (y : ℝ) from rfl, hmain] at hsel
  calc (((Finset.Icc 1 y).filter (fun c : ℕ => Nat.Coprime c P)).card : ℝ)
      ≤ (y : ℝ) * S⁻¹ + (4 * (Nat.sqrt y : ℝ) / S) ^ 2 :=
        le_trans hsel (by linarith [herr])
    _ = (y : ℝ) / S + (4 * (Nat.sqrt y : ℝ) / S) ^ 2 := by simp only [div_eq_mul_inv]

end

end Commons.NumberTheory.Totient

