import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

open scoped BigOperators

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.Nat

namespace SumRad

/-- `rad n` is the radical (squarefree kernel) of `n`: the product of the primes dividing `n`. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := by
  rw [rad]
  exact Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma rad_pos (n : ℕ) : 0 < rad n := Nat.pos_of_ne_zero (rad_ne_zero n)

lemma sqrt_pow_of_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = (Real.sqrt x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

lemma rad_cast (n : ℕ) : (rad n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
  rw [rad, Nat.cast_prod]
  simp

lemma sqrt_natCast_mul_rad (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (n : ℝ) * (rad n : ℝ) =
      ∏ p ∈ n.primeFactors,
        ((Real.sqrt (p : ℝ)) ^ (n.factorization p) * (p : ℝ)) := by
  have h1 : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  conv_lhs => rw [h1]
  rw [Real.sqrt_prod n.primeFactors (fun p _ => by positivity), rad_cast]
  have hthis : (∏ p ∈ n.primeFactors, Real.sqrt ((p : ℝ) ^ n.factorization p))
      = ∏ p ∈ n.primeFactors, (Real.sqrt (p : ℝ)) ^ n.factorization p := by
    refine Finset.prod_congr rfl fun p _ => ?_
    exact sqrt_pow_of_nonneg (Nat.cast_nonneg p) _
  rw [hthis, Finset.prod_mul_distrib]

/-- The local factor: `w p 0 = 1` and `w p k = (√p ^ k · p)⁻¹ = p^{-k/2-1}` for `k ≥ 1`. -/
noncomputable def w (p k : ℕ) : ℝ :=
  if k = 0 then 1 else ((Real.sqrt (p : ℝ)) ^ k * (p : ℝ))⁻¹

lemma w_zero (p : ℕ) : w p 0 = 1 := by simp [w]

lemma w_pos {p k : ℕ} (hp : p.Prime) : 0 < w p k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [w]
  · simp only [w, if_neg hk]
    exact inv_pos.mpr (mul_pos (pow_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)) k)
      (by exact_mod_cast hp.pos))

lemma w_nonneg {p k : ℕ} (hp : p.Prime) : 0 ≤ w p k := le_of_lt (w_pos hp)

lemma prod_w_eq (n : ℕ) (hn : n ≠ 0) {S : Finset ℕ} (hsub : n.primeFactors ⊆ S)
    (hprime : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, w p (n.factorization p) = 1 / (Real.sqrt (n : ℝ) * (rad n : ℝ)) := by
  have hzero : ∀ p ∈ S, p ∉ n.primeFactors → w p (n.factorization p) = 1 := by
    intro p _ hpn
    have hfac : n.factorization p = 0 := by
      rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
      exact hpn
    simp [w, hfac]
  rw [← Finset.prod_subset hsub hzero]
  trans ∏ p ∈ n.primeFactors, ((Real.sqrt (p : ℝ)) ^ n.factorization p * (p : ℝ))⁻¹
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hne : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hp
    simp [w, hne]
  · rw [Finset.prod_inv_distrib, ← sqrt_natCast_mul_rad n hn, inv_eq_one_div]


lemma factorization_le_of_mem {N n p : ℕ} (hn : n ∈ Finset.Icc 1 N) (hp : p.Prime) :
    n.factorization p ≤ N := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hn0 : n ≠ 0 := by omega
  rcases eq_or_ne (n.factorization p) 0 with h0 | h0
  · omega
  have hdvd : p ^ (n.factorization p) ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn0).mpr le_rfl
  have hle : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd (by omega) hdvd
  have h2 : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) :=
    Nat.pow_le_pow_left hp.two_le _
  have h3 : n.factorization p < 2 ^ (n.factorization p) := Nat.lt_two_pow_self
  omega

theorem sum_le_prod_w (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, 1 / (Real.sqrt (n : ℝ) * (rad n : ℝ)))
      ≤ ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime,
          (∑ k ∈ Finset.range (N+1), w p k) := by
  classical
  set S : Finset ℕ := (Finset.range (N+1)).filter Nat.Prime with hS
  have hprimeS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hmemS : ∀ p, p.Prime → p ≤ N → p ∈ S := by
    intro p hp hpN
    rw [hS]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpN), hp⟩
  have hL : (∑ n ∈ Finset.Icc 1 N, 1 / (Real.sqrt (n : ℝ) * (rad n : ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, w (i:ℕ) (n.factorization (i:ℕ)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hsub : n.primeFactors ⊆ S := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hdvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
      have hle : p ≤ N := le_trans (Nat.le_of_dvd (by omega) hdvd) (Finset.mem_Icc.mp hn).2
      exact hmemS p hpp hle
    rw [← prod_w_eq n hn0 hsub hprimeS, ← Finset.prod_attach S (fun p => w p (n.factorization p)),
      ← Finset.univ_eq_attach S]
  rw [hL]
  set Φ : ℕ → (↥S → ℕ) := fun n i => n.factorization (i : ℕ) with hΦ
  have hinj : Set.InjOn Φ ↑(Finset.Icc 1 N) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbN : b ≤ N := (Finset.mem_Icc.mp hb).2
    refine Nat.eq_of_factorization_eq (by omega) (by omega) fun p => ?_
    by_cases hp : p.Prime
    · by_cases hpN : p ≤ N
      · have hpS : p ∈ S := hmemS p hp hpN
        exact congrFun hab ⟨p, hpS⟩
      · have ha0 : a.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun h => hpN (le_trans (Nat.le_of_dvd (by omega) h) haN))
        have hb0 : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
          (fun h => hpN (le_trans (Nat.le_of_dvd (by omega) h) hbN))
        rw [ha0, hb0]
    · rw [Nat.factorization_eq_zero_of_not_prime a hp,
        Nat.factorization_eq_zero_of_not_prime b hp]
  have hmem_img : ∀ y ∈ (Finset.Icc 1 N).image Φ,
      y ∈ Fintype.piFinset (fun _ : ↥S => Finset.range (N+1)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨n, hn, rfl⟩ := hy
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (factorization_le_of_mem hn (hprimeS i.1 i.2))
  have hprod : ∏ p ∈ S, (∑ k ∈ Finset.range (N+1), w p k)
      = ∑ x ∈ Fintype.piFinset (fun _ : ↥S => Finset.range (N+1)),
          ∏ i : ↥S, w (i:ℕ) (x i) := by
    rw [← Finset.prod_attach S (fun p => ∑ k ∈ Finset.range (N+1), w p k)]
    rw [← Finset.univ_eq_attach S]
    exact Finset.prod_univ_sum (fun _ : ↥S => Finset.range (N+1))
      (fun (i : ↥S) (k : ℕ) => w (i:ℕ) k)
  have himg := Finset.sum_image (f := fun y : (↥S → ℕ) => ∏ i : ↥S, w (↑i) (y i)) hinj
  rw [hprod]
  rw [show (∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, w (↑i) (n.factorization ↑i))
        = ∑ n ∈ Finset.Icc 1 N, ∏ i : ↥S, w (↑i) (Φ n i) from by
      refine Finset.sum_congr rfl fun n _ => Finset.prod_congr rfl fun i _ => ?_
      rw [hΦ]]
  rw [← himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg hmem_img (fun y _ _ => ?_)
  exact Finset.prod_nonneg fun i _ => w_nonneg (hprimeS i.1 i.2)

lemma tel6_aux {y : ℝ} (hy : 1 ≤ y) :
    1 / ((y + 6) * Real.sqrt (y + 6)) ≤ (1/3) * (1 / Real.sqrt y - 1 / Real.sqrt (y + 6)) := by
  have hy6 : 0 < y + 6 := by linarith
  have hy0 : 0 < y := by linarith
  have hA : 0 < Real.sqrt (y + 6) := Real.sqrt_pos.mpr hy6
  have hB : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hA2 : (Real.sqrt (y + 6))^2 = y + 6 := Real.sq_sqrt (le_of_lt hy6)
  have hkey : Real.sqrt y * (y + 9) ≤ (Real.sqrt (y + 6))^3 := by
    have h1 : (Real.sqrt y * (y + 9))^2 ≤ ((Real.sqrt (y + 6))^3)^2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hy0)]
      have h2 : ((Real.sqrt (y + 6))^3)^2 = (y+6)^3 := by
        rw [← pow_mul]
        norm_num
        rw [show (6:ℕ) = 2 * 3 by norm_num, pow_mul, hA2]
      rw [h2]
      nlinarith [sq_nonneg (y + 4), sq_nonneg y]
    have habs := sq_le_sq.mp h1
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (y + 6) * Real.sqrt (y + 6))]
  have h1 : (1:ℝ)/3 * (1 / Real.sqrt y - 1 / Real.sqrt (y + 6))
      = (Real.sqrt (y + 6) - Real.sqrt y) / (3 * (Real.sqrt y * Real.sqrt (y + 6))) := by
    rw [div_sub_div _ _ hB.ne' hA.ne']; ring
  rw [h1, show (Real.sqrt (y+6) - Real.sqrt y) / (3 * (Real.sqrt y * Real.sqrt (y+6)))
        * ((y + 6) * Real.sqrt (y+6))
      = ((Real.sqrt (y+6) - Real.sqrt y) * ((y + 6) * Real.sqrt (y+6)))
        / (3 * (Real.sqrt y * Real.sqrt (y+6))) by ring]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * (Real.sqrt y * Real.sqrt (y+6)))]
  nlinarith [hkey, hA2, sq_nonneg (Real.sqrt y), Real.sqrt_nonneg y]

lemma tel6_range (a M : ℕ) (ha : 7 ≤ a) :
    (∑ k ∈ Finset.range (M+1),
        1 / ((((a + 6*k : ℕ)) : ℝ) * Real.sqrt (((a + 6*k : ℕ)) : ℝ)))
      ≤ (1/3) / Real.sqrt (((a-6 : ℕ)) : ℝ) := by
  have hkey : ∀ M, (∑ k ∈ Finset.range (M+1),
        1 / ((((a + 6*k : ℕ)) : ℝ) * Real.sqrt (((a + 6*k : ℕ)) : ℝ)))
      ≤ (1/3) * (1 / Real.sqrt (((a-6:ℕ)) : ℝ) - 1 / Real.sqrt (((a+6*M:ℕ)) : ℝ)) := by
    intro M
    induction M with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, zero_add, Finset.sum_range_one]
      have hy : (1:ℝ) ≤ (((a-6:ℕ)) : ℝ) := by
        have : 1 ≤ a - 6 := by omega
        exact_mod_cast this
      have h := tel6_aux hy
      have hcast : (((a-6:ℕ)) : ℝ) + 6 = (((a:ℕ)) : ℝ) := by
        rw [Nat.cast_sub (show 6 ≤ a by omega)]
        ring
      rwa [hcast] at h
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hy : (1:ℝ) ≤ (((a + 6*M:ℕ)) : ℝ) := by
        have : 1 ≤ a + 6*M := by omega
        exact_mod_cast this
      have hstep := tel6_aux hy
      have hcast : (((a + 6*M:ℕ)) : ℝ) + 6 = (((a + 6*(M+1):ℕ)) : ℝ) := by
        have h2 : a + 6*M + 6 = a + 6*(M+1) := by omega
        rw [← h2, Nat.cast_add]
        norm_num
      rw [hcast] at hstep
      linarith
  have hfin := hkey M
  have hle : (∑ k ∈ Finset.range (M+1),
        1 / ((((a + 6*k : ℕ)) : ℝ) * Real.sqrt (((a + 6*k : ℕ)) : ℝ)))
      ≤ (1/3) * (1 / Real.sqrt (((a-6:ℕ)) : ℝ)) := by
    have h1 : 0 ≤ 1 / Real.sqrt (((a+6*M:ℕ)) : ℝ) := by positivity
    linarith
  simpa [div_eq_mul_inv] using hle

lemma coprime_six_rcp_sqrt_mul_le (M : ℕ) :
    (∑ n ∈ (Finset.Icc 11 M).filter (fun n => Nat.Coprime n 6),
        1 / ((n : ℝ) * Real.sqrt (n : ℝ))) ≤ 0.276 := by
  set T := (Finset.Icc 11 M).filter (fun n => Nat.Coprime n 6) with hT
  set T5 := T.filter (fun n => n % 6 = 5) with hT5
  set T1 := T.filter (fun n => n % 6 = 1) with hT1
  have hmod : ∀ n ∈ T, n % 6 = 5 ∨ n % 6 = 1 := by
    intro n hn
    rw [hT, Finset.mem_filter] at hn
    obtain ⟨-, hcop⟩ := hn
    have h2 : ¬ 2 ∣ n := fun hd =>
      (by decide : ¬ Nat.Coprime 2 6) (hcop.coprime_dvd_left hd)
    have h3 : ¬ 3 ∣ n := fun hd =>
      (by decide : ¬ Nat.Coprime 3 6) (hcop.coprime_dvd_left hd)
    omega
  have hsub : T ⊆ T5 ∪ T1 := by
    intro n hn
    rcases hmod n hn with h | h
    · exact Finset.mem_union_left _ (by rw [hT5, Finset.mem_filter]; exact ⟨hn, h⟩)
    · exact Finset.mem_union_right _ (by rw [hT1, Finset.mem_filter]; exact ⟨hn, h⟩)
  have hdisj : Disjoint T5 T1 := by
    rw [Finset.disjoint_left]
    intro n hn5 hn1
    rw [hT5, Finset.mem_filter] at hn5
    rw [hT1, Finset.mem_filter] at hn1
    omega
  have h5 : (∑ n ∈ T5, 1 / ((n : ℝ) * Real.sqrt (n : ℝ))) ≤ (1/3)/Real.sqrt 5 := by
    have hsub5 : T5 ⊆ (Finset.range (M+1)).image (fun k => 11 + 6*k) := by
      intro n hn
      rw [hT5, Finset.mem_filter] at hn
      obtain ⟨hnT, hn5⟩ := hn
      rw [hT, Finset.mem_filter, Finset.mem_Icc] at hnT
      obtain ⟨⟨hn11, hnM⟩, -⟩ := hnT
      rw [Finset.mem_image]
      exact ⟨(n-11)/6, by rw [Finset.mem_range]; omega, by omega⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub5 (fun n _ _ => by positivity)) ?_
    rw [Finset.sum_image]
    · exact tel6_range 11 M (by norm_num)
    · intro a _ b _ hab
      simp only at hab
      omega
  have h1 : (∑ n ∈ T1, 1 / ((n : ℝ) * Real.sqrt (n : ℝ))) ≤ (1/3)/Real.sqrt 7 := by
    have hsub1 : T1 ⊆ (Finset.range (M+1)).image (fun k => 13 + 6*k) := by
      intro n hn
      rw [hT1, Finset.mem_filter] at hn
      obtain ⟨hnT, hn1⟩ := hn
      rw [hT, Finset.mem_filter, Finset.mem_Icc] at hnT
      obtain ⟨⟨hn11, hnM⟩, -⟩ := hnT
      have hn13 : 13 ≤ n := by omega
      rw [Finset.mem_image]
      exact ⟨(n-13)/6, by rw [Finset.mem_range]; omega, by omega⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun n _ _ => by positivity)) ?_
    rw [Finset.sum_image]
    · exact tel6_range 13 M (by norm_num)
    · intro a _ b _ hab
      simp only at hab
      omega
  have hfin : (1/3)/Real.sqrt 5 + (1/3)/Real.sqrt 7 ≤ 0.276 := by
    have hs5 : (2.236:ℝ) ≤ Real.sqrt 5 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hs7 : (2.645:ℝ) ≤ Real.sqrt 7 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hb5 : (1:ℝ)/Real.sqrt 5 ≤ 1/2.236 := one_div_le_one_div_of_le (by norm_num) hs5
    have hb7 : (1:ℝ)/Real.sqrt 7 ≤ 1/2.645 := one_div_le_one_div_of_le (by norm_num) hs7
    have e5 : (1/3:ℝ)/Real.sqrt 5 = (1/3) * (1/Real.sqrt 5) := by simp [div_eq_mul_inv]
    have e7 : (1/3:ℝ)/Real.sqrt 7 = (1/3) * (1/Real.sqrt 7) := by simp [div_eq_mul_inv]
    rw [e5, e7]
    linarith
  calc (∑ n ∈ T, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)))
      ≤ ∑ n ∈ T5 ∪ T1, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = (∑ n ∈ T5, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)))
        + (∑ n ∈ T1, 1 / ((n : ℝ) * Real.sqrt (n : ℝ))) := Finset.sum_union hdisj
    _ ≤ (1/3)/Real.sqrt 5 + (1/3)/Real.sqrt 7 := add_le_add h5 h1
    _ ≤ 0.276 := hfin

lemma tel2_aux {y : ℝ} (hy : 1 ≤ y) :
    1 / (y + 2)^2 ≤ (1/2) * (1/y - 1/(y+2)) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hy2 : (0:ℝ) < y + 2 := by linarith
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (y+2)^2)]
  have h : (1:ℝ)/y - 1/(y+2) = 2/(y*(y+2)) := by
    field_simp
    ring
  rw [h]
  have h2 : (1/2:ℝ) * (2/(y*(y+2))) * (y+2)^2 = (y+2)/y := by
    field_simp
    try ring
  rw [h2, le_div_iff₀ hy0]
  linarith

lemma tel2_range (a M : ℕ) (ha : 3 ≤ a) :
    (∑ k ∈ Finset.range (M+1), 1 / ((((a + 2*k : ℕ)) : ℝ)^2)) ≤ (1/2) / ((((a-2 : ℕ)) : ℝ)) := by
  have hkey : ∀ M, (∑ k ∈ Finset.range (M+1), 1 / ((((a + 2*k : ℕ)) : ℝ)^2))
      ≤ (1/2) * (1 / (((a-2:ℕ)) : ℝ) - 1 / (((a+2*M:ℕ)) : ℝ)) := by
    intro M
    induction M with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, zero_add, Finset.sum_range_one]
      have hy : (1:ℝ) ≤ (((a-2:ℕ)) : ℝ) := by
        have : 1 ≤ a - 2 := by omega
        exact_mod_cast this
      have h := tel2_aux hy
      have hcast : (((a-2:ℕ)) : ℝ) + 2 = (((a:ℕ)) : ℝ) := by
        rw [Nat.cast_sub (show 2 ≤ a by omega)]
        ring
      rwa [hcast] at h
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have hy : (1:ℝ) ≤ (((a + 2*M:ℕ)) : ℝ) := by
        have : 1 ≤ a + 2*M := by omega
        exact_mod_cast this
      have hstep := tel2_aux hy
      have hcast : (((a + 2*M:ℕ)) : ℝ) + 2 = (((a + 2*(M+1):ℕ)) : ℝ) := by
        have h2 : a + 2*M + 2 = a + 2*(M+1) := by omega
        rw [← h2, Nat.cast_add]
        norm_num
      rw [hcast] at hstep
      linarith
  have hfin := hkey M
  have hle : (∑ k ∈ Finset.range (M+1), 1 / ((((a + 2*k : ℕ)) : ℝ)^2))
      ≤ (1/2) * (1 / (((a-2:ℕ)) : ℝ)) := by
    have h1 : 0 ≤ 1 / (((a+2*M:ℕ)) : ℝ) := by positivity
    linarith
  simpa [div_eq_mul_inv] using hle

lemma odd_inv_sq_le (M : ℕ) :
    (∑ n ∈ (Finset.Icc 11 M).filter (fun n => Odd n), 1 / (n : ℝ) ^ 2) ≤ 1/18 := by
  set T := (Finset.Icc 11 M).filter (fun n => Odd n) with hT
  have hsub : T ⊆ (Finset.range (M+1)).image (fun k => 11 + 2*k) := by
    intro n hn
    rw [hT, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn11, hnM⟩, hodd⟩ := hn
    rw [Nat.odd_iff] at hodd
    rw [Finset.mem_image]
    refine ⟨(n-11)/2, by rw [Finset.mem_range]; omega, ?_⟩
    omega
  have hinj : Set.InjOn (fun k => 11 + 2*k) ↑(Finset.range (M+1)) := by
    intro x _ y _ h
    simp only at h
    omega
  calc (∑ n ∈ T, 1 / (n : ℝ) ^ 2)
      ≤ ∑ k ∈ Finset.range (M+1), 1 / ((((11 + 2*k : ℕ)) : ℝ) ^ 2) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)) ?_
        rw [Finset.sum_image hinj]
    _ ≤ (1/2) / ((((11-2 : ℕ)) : ℝ)) := tel2_range 11 M (by norm_num)
    _ ≤ 1/18 := by norm_num

noncomputable def cg (p : ℕ) : ℝ := 1 / ((p : ℝ) * (Real.sqrt (p : ℝ) - 1))
noncomputable def sqp (p : ℕ) : ℝ := 1 / ((p : ℝ) * Real.sqrt (p : ℝ))
noncomputable def dpr (p : ℕ) : ℝ := 1.432 / (p : ℝ) ^ 2

lemma geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) ≤ 1 / (1 - x) := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : (∑ i ∈ Finset.range n, x ^ i) * (1 - x) = 1 - x ^ n := by
    have h := geom_sum_mul x n
    linarith
  have h3 : 1 - x ^ n ≤ 1 := by
    have := pow_nonneg hx0 n
    linarith
  rw [le_div_iff₀ h1]
  linarith

lemma sum_w_le (p N : ℕ) (hp : p.Prime) :
    (∑ k ∈ Finset.range (N+1), w p k) ≤ 1 + cg p := by
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have hsp1 : (1:ℝ) < Real.sqrt (p : ℝ) := by
    have := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) < p by exact_mod_cast hp.one_lt)
    rwa [Real.sqrt_one] at this
  set x := (Real.sqrt (p : ℝ))⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [hx, inv_lt_one_iff₀]
    exact Or.inr hsp1
  rw [Finset.sum_range_succ']
  have hterm : ∀ k, w p (k+1) = (1/(p:ℝ)) * x^(k+1) := by
    intro k
    simp only [w, if_neg (Nat.succ_ne_zero k)]
    rw [hx, mul_inv, inv_pow]
    ring
  have hsum : (∑ k ∈ Finset.range N, w p (k+1))
      = (1/(p:ℝ)) * (∑ k ∈ Finset.range N, x^(k+1)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hterm k
  rw [hsum, w_zero]
  have hbound : (∑ k ∈ Finset.range N, x^(k+1)) ≤ x * (1/(1-x)) := by
    rw [show (∑ k ∈ Finset.range N, x^(k+1)) = x * ∑ k ∈ Finset.range N, x^k by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [pow_succ, mul_comm]]
    exact mul_le_mul_of_nonneg_left (geom_le hx0 hx1 N) hx0
  have hcg : (1/(p:ℝ)) * (x * (1/(1-x))) = cg p := by
    rw [hx, cg]
    field_simp
    try ring
  have hp_pos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have h1p : 0 < 1/(p:ℝ) := one_div_pos.mpr hp_pos
  nlinarith [hbound, hcg, h1p]

lemma prime_gt_seven (p : ℕ) (hp : p.Prime) (h : 7 < p) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> norm_num at hp

lemma cg_le (p : ℕ) (hp : p.Prime) (hp7 : 7 < p) :
    1 + cg p ≤ (1 + sqp p) * (1 + dpr p) := by
  have hp11 : 11 ≤ p := prime_gt_seven p hp hp7
  have hp_pos : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hsp : 0 < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp_pos
  have hA2 : (Real.sqrt (p:ℝ))^2 = (p:ℝ) := Real.sq_sqrt (le_of_lt hp_pos)
  have hsp1 : (1:ℝ) < Real.sqrt (p:ℝ) := by
    have := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) < p by exact_mod_cast hp.one_lt)
    rwa [Real.sqrt_one] at this
  have hsp11 : (3.316:ℝ) ≤ Real.sqrt (p:ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have h1 : (3.316:ℝ)^2 ≤ 11 := by norm_num
    have h2 : (11:ℝ) ≤ p := by exact_mod_cast hp11
    linarith
  have key : (1.432:ℝ) * Real.sqrt (p:ℝ) ≤ 0.432 * p := by
    have h1 : (1.432:ℝ) * Real.sqrt (p:ℝ) = 1.432 * p / Real.sqrt (p:ℝ) := by
      rw [eq_div_iff (ne_of_gt hsp), mul_assoc, ← sq, hA2]
    rw [h1, div_le_iff₀ hsp]
    nlinarith [hsp11, hp_pos]
  have hdiff : cg p - sqp p ≤ dpr p := by
    have hspm : (0:ℝ) < Real.sqrt (p:ℝ) - 1 := by linarith
    have hX : (0:ℝ) < (p:ℝ) * (Real.sqrt (p:ℝ) - 1) * Real.sqrt (p:ℝ) :=
      mul_pos (mul_pos hp_pos hspm) hsp
    have h1 : cg p - sqp p = 1 / ((p:ℝ) * (Real.sqrt (p:ℝ) - 1) * Real.sqrt (p:ℝ)) := by
      rw [cg, sqp]
      have h1 : Real.sqrt (p:ℝ) - 1 ≠ 0 := ne_of_gt hspm
      field_simp
      ring
    rw [h1, dpr, div_le_iff₀ hX]
    rw [show (1.432 / (p:ℝ)^2) * ((p:ℝ) * (Real.sqrt (p:ℝ) - 1) * Real.sqrt (p:ℝ))
        = (1.432 * ((p:ℝ) * (Real.sqrt (p:ℝ) - 1) * Real.sqrt (p:ℝ))) / (p:ℝ)^2 by ring]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (p:ℝ)^2)]
    nlinarith [key, hA2]
  have h1 : (1 + sqp p) * (1 + dpr p) = 1 + sqp p + dpr p + sqp p * dpr p := by ring
  have h2 : 0 < sqp p := div_pos one_pos (mul_pos hp_pos hsp)
  have h3 : 0 < dpr p := by rw [dpr]; positivity
  have h4 : 0 ≤ sqp p * dpr p := le_of_lt (mul_pos h2 h3)
  linarith

lemma cg_nonneg (p : ℕ) : 0 ≤ cg p := by
  rw [cg]
  rcases eq_or_ne p 0 with h0 | hp0
  · subst h0; simp
  rcases eq_or_ne p 1 with h1 | hp1
  · subst h1; norm_num
  have hp2 : 1 < p := by omega
  have hp : (0:ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hs : (1:ℝ) < Real.sqrt (p:ℝ) := by
    have := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ 1 by norm_num)
      (show (1:ℝ) < p by exact_mod_cast hp2)
    rwa [Real.sqrt_one] at this
  exact le_of_lt (div_pos one_pos (mul_pos hp (by linarith)))

lemma cg_bound (p : ℕ) (r : ℝ) (hr : r ≤ Real.sqrt (p:ℝ)) (hr1 : (1:ℝ) < r) :
    1 + cg p ≤ 1 + 1/((p:ℝ)*(r-1)) := by
  rw [cg]
  have hpl : (0:ℝ) < (p:ℝ) := by
    rcases eq_or_ne p 0 with h0 | hp0
    · subst h0
      simp at hr
      linarith [Real.sqrt_nonneg (0:ℝ)]
    · exact_mod_cast Nat.pos_of_ne_zero hp0
  have h1 : (0:ℝ) < (p:ℝ)*(r-1) := mul_pos hpl (by linarith)
  have h2 : (p:ℝ)*(r-1) ≤ (p:ℝ)*(Real.sqrt (p:ℝ)-1) := by nlinarith
  have := one_div_le_one_div_of_le h1 h2
  linarith

lemma cg_two : 1 + cg 2 ≤ 2.2072 := by
  have hs : (1.4142:ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hb := cg_bound 2 1.4142 hs (by norm_num)
  have h2 : (1:ℝ)/((2:ℝ)*((1.4142:ℝ)-1)) ≤ 1.2072 := by norm_num
  linarith

lemma cg_three : 1 + cg 3 ≤ 1.4554 := by
  have hs : (1.732:ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hb := cg_bound 3 1.732 hs (by norm_num)
  have h2 : (1:ℝ)/((3:ℝ)*((1.732:ℝ)-1)) ≤ 0.4554 := by norm_num
  linarith

lemma cg_five : 1 + cg 5 ≤ 1.1619 := by
  have hs : (2.236:ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hb := cg_bound 5 2.236 hs (by norm_num)
  have h2 : (1:ℝ)/((5:ℝ)*((2.236:ℝ)-1)) ≤ 0.1619 := by norm_num
  linarith

lemma cg_seven : 1 + cg 7 ≤ 1.0869 := by
  have hs : (2.645:ℝ) ≤ Real.sqrt 7 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hb := cg_bound 7 2.645 hs (by norm_num)
  have h2 : (1:ℝ)/((7:ℝ)*((2.645:ℝ)-1)) ≤ 0.0869 := by norm_num
  linarith

lemma prod_small_primes_le :
    (∏ p ∈ ({2,3,5,7} : Finset ℕ), (1 + cg p)) ≤ 4.057 := by
  have h : (∏ p ∈ ({2,3,5,7} : Finset ℕ), (1 + cg p))
      = (1 + cg 2) * (1 + cg 3) * (1 + cg 5) * (1 + cg 7) := by
    norm_num [Finset.prod_insert]
    try ring
  rw [h]
  have e2 : (0:ℝ) ≤ 1 + cg 2 := by linarith [cg_nonneg 2]
  have e3 : (0:ℝ) ≤ 1 + cg 3 := by linarith [cg_nonneg 3]
  have e5 : (0:ℝ) ≤ 1 + cg 5 := by linarith [cg_nonneg 5]
  have e7 : (0:ℝ) ≤ 1 + cg 7 := by linarith [cg_nonneg 7]
  have hA : (1 + cg 2) * (1 + cg 3) ≤ 2.2072 * 1.4554 := by nlinarith [cg_two, cg_three, e2, e3]
  have hB : (1 + cg 5) * (1 + cg 7) ≤ 1.1619 * 1.0869 := by nlinarith [cg_five, cg_seven, e5, e7]
  have eA : (0:ℝ) ≤ 1.1619 * 1.0869 := by norm_num
  have hmul := mul_le_mul hA hB (mul_nonneg e5 e7) (by norm_num : (0:ℝ) ≤ 2.2072 * 1.4554)
  nlinarith [hmul]

lemma one_sub_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
    have h2 : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
    have h3 : 0 ≤ ∏ j ∈ s, (1 - a j) := by
      refine Finset.prod_nonneg fun j hj => ?_
      have hj' := ha1 j (Finset.mem_insert_of_mem hj)
      linarith
    have h4 : 0 ≤ ∑ j ∈ s, a j := by
      refine Finset.sum_nonneg fun j hj => ?_
      exact ha j (Finset.mem_insert_of_mem hj)
    have h5 : ∏ j ∈ s, (1 - a j) ≤ 1 := by
      refine Finset.prod_le_one₀ (s := s) (f := fun j => 1 - a j) ?_ ?_
      · intro j hj
        have hj' := ha1 j (Finset.mem_insert_of_mem hj)
        linarith
      · intro j hj
        have hj' := ha j (Finset.mem_insert_of_mem hj)
        linarith
    have h6 : 0 ≤ 1 - a i := by
      have hi' := ha1 i (Finset.mem_insert_self i s)
      linarith
    have h7 : (1 - a i) * (1 - ∑ j ∈ s, a j) ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
      mul_le_mul_of_nonneg_left h1 h6
    have h8 : 1 - (a i + ∑ j ∈ s, a j) ≤ (1 - a i) * (1 - ∑ j ∈ s, a j) := by
      nlinarith [h2, h4, h6]
    linarith [h7, h8]

lemma prod_one_add_le_inv (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∑ i ∈ s, a i < 1) :
    ∏ i ∈ s, (1 + a i) ≤ 1/(1 - ∑ i ∈ s, a i) := by
  have h2 : ∀ i ∈ s, a i < 1 := by
    intro i hi
    have := Finset.single_le_sum (f := a) (fun j hj => ha j hj) hi
    linarith
  have h3 : ∀ i ∈ s, 1 + a i ≤ 1/(1 - a i) := by
    intro i hi
    rw [le_div_iff₀ (by linarith [h2 i hi])]
    nlinarith [ha i hi]
  have h4 : ∏ i ∈ s, (1 + a i) ≤ ∏ i ∈ s, (1/(1 - a i)) :=
    Finset.prod_le_prod₀ (fun i hi => by linarith [ha i hi]) h3
  have h5 : ∏ i ∈ s, (1/(1 - a i)) = 1/(∏ i ∈ s, (1 - a i)) := by
    rw [Finset.prod_div_distrib]
    simp
  have h6 : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) :=
    one_sub_sum_le_prod s a ha (fun i hi => le_of_lt (h2 i hi))
  have h7 : (0:ℝ) < 1 - ∑ i ∈ s, a i := by linarith
  have h8 : (0:ℝ) < ∏ i ∈ s, (1 - a i) := lt_of_lt_of_le h7 h6
  rw [h5] at h4
  have h9 : 1/(∏ i ∈ s, (1 - a i)) ≤ 1/(1 - ∑ i ∈ s, a i) :=
    one_div_le_one_div_of_le h7 h6
  linarith [h4, h9]

lemma prod_sqp_mul_eq (t : Finset ℕ) :
    (∏ p ∈ t, ((p:ℝ) * Real.sqrt (p:ℝ)))
      = ((∏ p ∈ t, p : ℕ):ℝ) * Real.sqrt (((∏ p ∈ t, p : ℕ):ℝ)) := by
  rw [Finset.prod_mul_distrib, ← Nat.cast_prod]
  congr 1
  conv_rhs => rw [Nat.cast_prod, Real.sqrt_prod t (fun p _ => by positivity)]

lemma prod_sqp_eq (t : Finset ℕ) :
    (∏ p ∈ t, sqp p) = 1/(((∏ p ∈ t, p : ℕ):ℝ) * Real.sqrt (((∏ p ∈ t, p : ℕ):ℝ))) := by
  have hL : (∏ p ∈ t, sqp p) = (∏ p ∈ t, ((p:ℝ) * Real.sqrt (p:ℝ)))⁻¹ := by
    simp only [sqp, one_div]
    rw [Finset.prod_inv_distrib]
  rw [hL, prod_sqp_mul_eq, inv_eq_one_div]

lemma sum_dpr_le (N : ℕ) :
    (∑ p ∈ ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p), dpr p)
      ≤ 1.432/18 := by
  set T₀ := ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p) with hT0
  have hsub : T₀ ⊆ (Finset.Icc 11 N).filter (fun n => Odd n) := by
    intro p hp
    rw [hT0, Finset.mem_filter] at hp
    obtain ⟨hpS, hp7⟩ := hp
    rw [Finset.mem_filter] at hpS
    obtain ⟨hpR, hpprime⟩ := hpS
    rw [Finset.mem_range] at hpR
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨prime_gt_seven p hpprime hp7, by omega⟩,
      Nat.Prime.odd_of_ne_two hpprime (by rintro rfl; norm_num at hp7)⟩
  have h1 : (∑ p ∈ T₀, dpr p) = 1.432 * ∑ p ∈ T₀, 1/(p:ℝ)^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dpr]
    ring
  rw [h1]
  have h2 : (∑ p ∈ T₀, 1/(p:ℝ)^2) ≤ 1/18 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity))
      (odd_inv_sq_le N)
  nlinarith [h2]

lemma prod_dpr_le (N : ℕ) :
    (∏ p ∈ ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p), (1 + dpr p))
      ≤ 1/(1 - 1.432/18) := by
  set T₀ := ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p) with hT0
  have hsum := sum_dpr_le N
  have ha : ∀ p ∈ T₀, 0 ≤ dpr p := by
    intro p _
    rw [dpr]
    positivity
  have h1 : ∑ p ∈ T₀, dpr p < 1 := by linarith [hsum]
  have h2 := prod_one_add_le_inv T₀ dpr ha h1
  have h3 : 1/(1 - ∑ p ∈ T₀, dpr p) ≤ 1/(1 - 1.432/18) :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 - 1.432/18) (by linarith [hsum])
  linarith [h2, h3]

lemma prod_sqp_le (N : ℕ) :
    (∏ p ∈ ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p), (1 + sqp p))
      ≤ 1 + 0.276 := by
  classical
  set T₀ := ((Finset.range (N+1)).filter Nat.Prime).filter (fun p => 7 < p) with hT0
  have hprime : ∀ p ∈ T₀, p.Prime := by
    intro p hp
    rw [hT0, Finset.mem_filter] at hp
    exact (Finset.mem_filter.mp hp.1).2
  have hp7 : ∀ p ∈ T₀, 7 < p := by
    intro p hp
    rw [hT0, Finset.mem_filter] at hp
    exact hp.2
  set M := ∏ p ∈ T₀, p with hM
  have hterm : ∀ t ∈ T₀.powerset, (∏ p ∈ t, sqp p)
      = 1/(((∏ p ∈ t, p : ℕ):ℝ) * Real.sqrt (((∏ p ∈ t, p : ℕ):ℝ))) :=
    fun t _ => prod_sqp_eq t
  have himgsub : ∀ t ∈ T₀.powerset.erase ∅,
      (∏ p ∈ t, p) ∈ (Finset.Icc 11 M).filter (fun n => Nat.Coprime n 6) := by
    intro t ht
    rw [Finset.mem_erase, Finset.mem_powerset] at ht
    obtain ⟨hne, htpow⟩ := ht
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hne' : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨p0, hp0⟩ := hne'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have hp0T : p0 ∈ T₀ := htpow hp0
      have h11 : 11 ≤ p0 := prime_gt_seven p0 (hprime p0 hp0T) (hp7 p0 hp0T)
      have hle : p0 ≤ ∏ q ∈ t, q :=
        Finset.single_le_prod' (fun q hq => Nat.one_le_iff_ne_zero.mpr
          (hprime q (htpow hq)).ne_zero) hp0
      omega
    · exact Finset.prod_le_prod_of_subset_of_one_le₀ htpow
        (fun q _ => Nat.cast_nonneg q)
        (fun q hq _ => Nat.one_le_iff_ne_zero.mpr (hprime q hq).ne_zero)
    · refine Nat.Coprime.prod_left fun q hq => ?_
      have hqT := htpow hq
      have h11 : 11 ≤ q := prime_gt_seven q (hprime q hqT) (hp7 q hqT)
      refine (Nat.Prime.coprime_iff_not_dvd (hprime q hqT)).mpr ?_
      intro hd
      have := Nat.le_of_dvd (by norm_num : 0 < 6) hd
      omega
  have hinj : Set.InjOn (fun t => ∏ p ∈ t, p) (↑(T₀.powerset.erase ∅) : Set (Finset ℕ)) := by
    intro t1 ht1 t2 ht2 hab
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_powerset] at ht1 ht2
    have h1 : (∏ p ∈ t1, p).primeFactors = t1 :=
      Nat.primeFactors_prod (fun p hp => hprime p (ht1.2 hp))
    have h2 : (∏ p ∈ t2, p).primeFactors = t2 :=
      Nat.primeFactors_prod (fun p hp => hprime p (ht2.2 hp))
    have hab' : (∏ p ∈ t1, p) = (∏ p ∈ t2, p) := hab
    rw [← h1, ← h2, hab']
  rw [Finset.prod_one_add]
  have hmem : (∅ : Finset ℕ) ∈ T₀.powerset := Finset.empty_mem_powerset T₀
  rw [← Finset.sum_erase_add _ _ hmem]
  have hemp : (∏ p ∈ (∅ : Finset ℕ), sqp p) = 1 := by simp
  rw [hemp]
  have hmain : (∑ t ∈ T₀.powerset.erase ∅, ∏ p ∈ t, sqp p) ≤ 0.276 := by
    have hsum_eq : (∑ t ∈ T₀.powerset.erase ∅, ∏ p ∈ t, sqp p)
        = ∑ n ∈ (T₀.powerset.erase ∅).image (fun t => ∏ p ∈ t, p),
            1/((n:ℝ) * Real.sqrt (n:ℝ)) := by
      calc (∑ t ∈ T₀.powerset.erase ∅, ∏ p ∈ t, sqp p)
          = ∑ t ∈ T₀.powerset.erase ∅,
              1/(((∏ p ∈ t, p : ℕ):ℝ) * Real.sqrt (((∏ p ∈ t, p : ℕ):ℝ))) :=
            Finset.sum_congr rfl fun t ht => hterm t (Finset.mem_of_mem_erase ht)
        _ = ∑ t ∈ T₀.powerset.erase ∅,
              (fun n : ℕ => 1/((n:ℝ) * Real.sqrt (n:ℝ))) ((fun t => ∏ p ∈ t, p) t) := rfl
        _ = ∑ n ∈ (T₀.powerset.erase ∅).image (fun t => ∏ p ∈ t, p),
              1/((n:ℝ) * Real.sqrt (n:ℝ)) := by
            rw [← Finset.sum_image (f := fun n : ℕ => 1/((n:ℝ) * Real.sqrt (n:ℝ))) hinj]
    rw [hsum_eq]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr himgsub) (fun n _ _ => by positivity)) ?_
    exact coprime_six_rcp_sqrt_mul_le M
  linarith [hmain]

end SumRad

open SumRad

theorem sum_recip_sqrt_mul_radical_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℝ) / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ))) ≤ 6 := by
  classical
  have h1 : (∑ n ∈ Finset.Icc 1 N,
        (1 : ℝ) / (Real.sqrt (n : ℝ) * ((n.primeFactors.prod id : ℕ) : ℝ)))
      ≤ ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (∑ k ∈ Finset.range (N+1), w p k) :=
    sum_le_prod_w N
  have h2 : ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (∑ k ∈ Finset.range (N+1), w p k)
      ≤ ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 + cg p) := by
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · exact Finset.sum_nonneg fun k _ => w_nonneg (Finset.mem_filter.mp hp).2
    · exact sum_w_le p N (Finset.mem_filter.mp hp).2
  have h3 : ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 + cg p) ≤ 6 := by
    set S := (Finset.range (N+1)).filter Nat.Prime with hS
    rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ≤ 7) (fun p => 1 + cg p)]
    have hset : S.filter (fun p => ¬ p ≤ 7) = S.filter (fun p => 7 < p) :=
      Finset.filter_congr fun p _ => by omega
    rw [hset]
    have hsub : S.filter (fun p => p ≤ 7) ⊆ ({2,3,5,7} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hp7⟩ := hp
      have hpp : p.Prime := (Finset.mem_filter.mp hpS).2
      have hp2 : 2 ≤ p := hpp.two_le
      have hp8 : p < 8 := by omega
      interval_cases p
      · simp
      · simp
      · exfalso; norm_num at hpp
      · simp
      · exfalso; norm_num at hpp
      · simp
    have hsmall : (∏ p ∈ S.filter (fun p => p ≤ 7), (1 + cg p)) ≤ 4.057 :=
      le_trans (Finset.prod_le_prod_of_subset_of_one_le₀ hsub
        (fun p _ => by linarith [cg_nonneg p])
        (fun p _ _ => by linarith [cg_nonneg p])) prod_small_primes_le
    have htail : (∏ p ∈ S.filter (fun p => 7 < p), (1 + cg p))
        ≤ (1 + 0.276) * (1/(1 - 1.432/18)) := by
      have hstep : (∏ p ∈ S.filter (fun p => 7 < p), (1 + cg p))
          ≤ (∏ p ∈ S.filter (fun p => 7 < p), (1 + sqp p))
            * (∏ p ∈ S.filter (fun p => 7 < p), (1 + dpr p)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod₀ (fun p _ => by linarith [cg_nonneg p]) (fun p hp => ?_)
        have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        exact cg_le p hpp (Finset.mem_filter.mp hp).2
      have hsq := prod_sqp_le N
      have hdp := prod_dpr_le N
      have e1 : (0:ℝ) ≤ ∏ p ∈ S.filter (fun p => 7 < p), (1 + sqp p) := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hp' : (0:ℝ) < p := by
          have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          exact_mod_cast this.pos
        have : (0:ℝ) < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp'
        have : (0:ℝ) < (p:ℝ) * Real.sqrt (p:ℝ) := mul_pos hp' this
        simp only [sqp]
        positivity
      nlinarith [hstep, hsq, hdp, e1]
    have e : 0 ≤ ∏ p ∈ S.filter (fun p => 7 < p), (1 + cg p) :=
      Finset.prod_nonneg fun p _ => by linarith [cg_nonneg p]
    have hmul := mul_le_mul hsmall htail e (by norm_num : (0:ℝ) ≤ 4.057)
    nlinarith [hmul]
  linarith [h1, h2, h3]

end Commons.NumberTheory.Nat