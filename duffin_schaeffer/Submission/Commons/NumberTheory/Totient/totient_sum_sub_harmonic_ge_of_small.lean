import Mathlib
import Submission.Commons.NumberTheory.Totient.totient_sum_ge_A6_combo

/-!
# `∑_{r ≤ z} μ(r)²/φ(r) − H_z ≥ 9/20` for `2 ≤ z ≤ 1000`, `z ≠ 4`

Lower bound for the squarefree-restricted totient sum, complementary to the
"large `z`" companion `totient_sum_sub_harmonic_ge_of_large` (which handles
`z ≥ 1001`).

**Math.**  Split a squarefree `r` as `r = 2^a 3^b m` with `(m,6)=1`; this gives
`S(z) = S₆(z) + S₆(z/2) + S₆(z/3)/2 + S₆(z/6)/2` where `S₆` sums `1/φ` over squarefree
integers coprime to `6`.  The radical bijection bounds `S₆(y) ≥ A₆(y)`
(`totient_sum_ge_A6_combo`), and inclusion–exclusion turns `A₆` into harmonic
numbers, so that
`S(z) − H_z ≥ E(z) := ½(H_{z/2}−H_{z/4}) + ⅙(H_{z/3}−H_{z/9}) + 1/12(H_{z/6}−H_{z/12})
 − 1/12(H_{z/18}−H_{z/36})`.
For `6 ≤ z ≤ 99` the inequality `E(z) ≥ 9/20` is checked by direct computation, while
for `z ≥ 100` each harmonic difference is bounded below via `log`, and
`H_{z/18} − H_{z/36} ≤ 1`.  The few small values `z ∈ {2,3,5}` are checked directly.
-/

open scoped BigOperators

namespace Commons.NumberTheory.Totient

/-! ## Auxiliary reindexing and harmonic lemmas -/

private lemma harmonic_real_Icc (Y : ℕ) :
    (harmonic Y : ℝ) = ∑ n ∈ Finset.Icc 1 Y, (1:ℝ)/n := by
  rw [harmonic_eq_sum_Icc]; push_cast
  apply Finset.sum_congr rfl; intro i _; rw [one_div]

private lemma sum_reindex (R d : ℕ) (G : ℕ → ℝ) (hd : 0 < d) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r => d ∣ r), G r)
      = ∑ m ∈ Finset.Icc 1 (R/d), G (d*m) := by
  have hset : (Finset.Icc 1 R).filter (fun r => d ∣ r)
      = (Finset.Icc 1 (R/d)).image (fun m => d*m) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hr1, hrR⟩, hdvd⟩
      obtain ⟨m, rfl⟩ := hdvd
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hr1)
      exact ⟨m, ⟨hm1, (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hrR)⟩, rfl⟩
    · rintro ⟨m, ⟨hm1, hmR⟩, rfl⟩
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (ne_of_gt hd) (Nat.one_le_iff_ne_zero.mp hm1)),
        (by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmR)⟩, ⟨m, rfl⟩⟩
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hd hab

private lemma Td (Y d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => d ∣ n), (1:ℝ)/n) = (1/(d:ℝ)) * (harmonic (Y/d) : ℝ) := by
  rw [sum_reindex Y d (fun n => (1:ℝ)/n) hd]
  rw [harmonic_real_Icc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [one_div, Nat.cast_mul, mul_inv]

private lemma Tdif (Y d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 Y, (if d ∣ n then (1:ℝ)/n else 0)) = (1/(d:ℝ)) * (harmonic (Y/d) : ℝ) := by
  classical
  rw [← Finset.sum_filter (fun n => d ∣ n) (fun n => (1:ℝ)/n)]
  exact Td Y d hd

/-- `A₆` expressed through harmonic numbers (inclusion–exclusion for the primes `2,3`). -/
private lemma A6_eq_harmonic (Y : ℕ) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
    = (harmonic Y : ℝ) - (1/2) * (harmonic (Y/2) : ℝ) - (1/3) * (harmonic (Y/3) : ℝ)
      + (1/6) * (harmonic (Y/6) : ℝ) := by
  classical
  have key : ∀ n : ℕ, (if ¬ 2 ∣ n ∧ ¬ 3 ∣ n then (1:ℝ)/n else 0)
      = (1:ℝ)/n - (if 2 ∣ n then (1:ℝ)/n else 0) - (if 3 ∣ n then (1:ℝ)/n else 0)
        + (if 6 ∣ n then (1:ℝ)/n else 0) := by
    intro n
    have h6 : (2 ∣ n ∧ 3 ∣ n) ↔ 6 ∣ n := by omega
    by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n
    · rw [if_neg (by rintro ⟨a,_⟩; exact a h2), if_pos h2, if_pos h3, if_pos (h6.mp ⟨h2,h3⟩)]; ring
    · rw [if_neg (by rintro ⟨a,_⟩; exact a h2), if_pos h2, if_neg h3,
          if_neg (by rintro h; exact h3 (h6.mpr h).2)]; ring
    · rw [if_neg (by rintro ⟨_,b⟩; exact b h3), if_neg h2, if_pos h3,
          if_neg (by rintro h; exact h2 (h6.mpr h).1)]; ring
    · rw [if_pos ⟨h2,h3⟩, if_neg h2, if_neg h3,
          if_neg (by rintro h; exact h2 (h6.mpr h).1)]; ring
  calc (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ 2 ∣ n ∧ ¬ 3 ∣ n), (1:ℝ)/n)
      = ∑ n ∈ Finset.Icc 1 Y, (if ¬ 2 ∣ n ∧ ¬ 3 ∣ n then (1:ℝ)/n else 0) := Finset.sum_filter _ _
    _ = ∑ n ∈ Finset.Icc 1 Y, ((1:ℝ)/n - (if 2 ∣ n then (1:ℝ)/n else 0) - (if 3 ∣ n then (1:ℝ)/n else 0) + (if 6 ∣ n then (1:ℝ)/n else 0)) :=
        Finset.sum_congr rfl (fun n _ => key n)
    _ = (∑ n ∈ Finset.Icc 1 Y, (1:ℝ)/n)
        - (∑ n ∈ Finset.Icc 1 Y, (if 2 ∣ n then (1:ℝ)/n else 0))
        - (∑ n ∈ Finset.Icc 1 Y, (if 3 ∣ n then (1:ℝ)/n else 0))
        + (∑ n ∈ Finset.Icc 1 Y, (if 6 ∣ n then (1:ℝ)/n else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (harmonic Y : ℝ) - (1/2) * (harmonic (Y/2) : ℝ) - (1/3) * (harmonic (Y/3) : ℝ)
          + (1/6) * (harmonic (Y/6) : ℝ) := by
        rw [Tdif Y 2 (by norm_num), Tdif Y 3 (by norm_num), Tdif Y 6 (by norm_num),
            ← harmonic_real_Icc]
        norm_num

/-! ## The upper comparison function `E` -/

/-- `E(z) = ½(H_{z/2}−H_{z/4}) + ⅙(H_{z/3}−H_{z/9}) + 1/12(H_{z/6}−H_{z/12}) − 1/12(H_{z/18}−H_{z/36})`. -/
private noncomputable def Ereal (z : ℕ) : ℝ :=
  (1/2) * ((harmonic (z / 2) : ℝ) - (harmonic (z / 4) : ℝ))
    + (1/6) * ((harmonic (z / 3) : ℝ) - (harmonic (z / 9) : ℝ))
    + (1/12) * ((harmonic (z / 6) : ℝ) - (harmonic (z / 12) : ℝ))
    - (1/12) * ((harmonic (z / 18) : ℝ) - (harmonic (z / 36) : ℝ))

private def EQ (z : ℕ) : ℚ :=
  (1/2) * (harmonic (z/2) - harmonic (z/4))
    + (1/6) * (harmonic (z/3) - harmonic (z/9))
    + (1/12) * (harmonic (z/6) - harmonic (z/12))
    - (1/12) * (harmonic (z/18) - harmonic (z/36))

private lemma Ereal_eq_EQ (z : ℕ) : ((EQ z : ℚ) : ℝ) = Ereal z := by
  unfold EQ Ereal; push_cast; ring

/-- The squarefree totient sum dominates `E(z) + H_z`. -/
private lemma D_ge_E (z : ℕ) :
    Ereal z ≤ (∑ r ∈ Finset.Icc 1 z,
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ)) - (harmonic z : ℝ) := by
  have h := Commons.NumberTheory.Totient.totient_sum_ge_A6_combo z
  rw [A6_eq_harmonic z, A6_eq_harmonic (z/2), A6_eq_harmonic (z/3), A6_eq_harmonic (z/6)] at h
  simp only [Nat.div_div_eq_div_mul, Nat.reduceMul] at h
  unfold Ereal
  linarith

/-! ## Finite verification for `6 ≤ z ≤ 99` -/

private lemma EQ_ge (z : ℕ) (h1 : 6 ≤ z) (h2 : z ≤ 99) : (9/20:ℚ) ≤ EQ z := by
  interval_cases z <;> norm_num [EQ, harmonic_eq_sum_Icc, Finset.sum_Icc_succ_top]

/-! ## Analytic bound for `z ≥ 100` -/

private lemma harmonic_succ_real (n : ℕ) :
    (harmonic (n+1) : ℝ) = (harmonic n : ℝ) + 1/((n:ℝ)+1) := by
  rw [harmonic_real_Icc (n+1), harmonic_real_Icc n]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  push_cast; ring

private lemma harmonic_mono_real {a b : ℕ} (h : a ≤ b) : (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  induction b, h using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [harmonic_succ_real m]
    have : (0:ℝ) ≤ 1/((m:ℝ)+1) := by positivity
    linarith

private lemma harmonic_sub_ge_log (a b : ℕ) (hab : a ≤ b) :
    Real.log (((b:ℝ)+1)/((a:ℝ)+1)) ≤ (harmonic b : ℝ) - (harmonic a : ℝ) := by
  have key : ∀ n, a ≤ n → Real.log (((n:ℝ)+1)/((a:ℝ)+1)) ≤ (harmonic n : ℝ) - (harmonic a : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [harmonic_succ_real m]
      push_cast
      have hstep : Real.log (((m:ℝ)+1+1)/((m:ℝ)+1)) ≤ 1/((m:ℝ)+1) := by
        have hx : 0 < 1 + 1/((m:ℝ)+1) := by positivity
        have h := Real.log_le_sub_one_of_pos hx
        have heq : ((m:ℝ)+1+1)/((m:ℝ)+1) = 1 + 1/((m:ℝ)+1) := by field_simp
        rw [heq]
        simpa using h
      have hmul : Real.log (((m:ℝ)+1+1)/((a:ℝ)+1))
          = Real.log (((m:ℝ)+1)/((a:ℝ)+1)) + Real.log (((m:ℝ)+1+1)/((m:ℝ)+1)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      rw [hmul]; linarith [ih, hstep]
  exact key b hab

private lemma harmonic_sub_le_div (a b : ℕ) (hab : a ≤ b) :
    (harmonic b : ℝ) - (harmonic a : ℝ) ≤ ((b:ℝ) - a)/((a:ℝ)+1) := by
  have key : ∀ n, a ≤ n → (harmonic n : ℝ) - (harmonic a : ℝ) ≤ ((n:ℝ) - a)/((a:ℝ)+1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [harmonic_succ_real m]
      push_cast
      have hle : 1/((m:ℝ)+1) ≤ 1/((a:ℝ)+1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (a:ℝ) ≤ m := by exact_mod_cast hm
        linarith
      have hsplit : (((m:ℝ)+1) - a)/((a:ℝ)+1) = ((m:ℝ) - a)/((a:ℝ)+1) + 1/((a:ℝ)+1) := by
        field_simp; ring
      rw [hsplit]; linarith [ih, hle]
  exact key b hab

private lemma log_ge_two_div (t : ℝ) (ht : 1 ≤ t) :
    2*(t-1)/(t+1) ≤ Real.log t := by
  have hx : 0 ≤ t - 1 := by linarith
  have h := Real.le_log_one_add_of_nonneg hx
  have h1 : (1:ℝ) + (t-1) = t := by ring
  rw [h1] at h
  convert h using 1
  ring

private lemma E_ge_of_large (z : ℕ) (hz : 100 ≤ z) : (9/20:ℝ) ≤ Ereal z := by
  have hk : 25 ≤ z/4 := by omega
  have hj : 11 ≤ z/9 := by omega
  have hi : 8 ≤ z/12 := by omega
  have hzk : 2*(z/4) ≤ z/2 := by omega
  have hzj : 3*(z/9) ≤ z/3 := by omega
  have hzi : 2*(z/12) ≤ z/6 := by omega
  have t1 : (25/77:ℝ) ≤ (1/2) * ((harmonic (z/2):ℝ) - (harmonic (z/4):ℝ)) := by
    have hsub := harmonic_sub_ge_log (z/4) (z/2) (by omega)
    have hr1 : (51:ℝ)/26 ≤ (((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1) := by
      rw [le_div_iff₀ (by positivity)]
      have hkR : (25:ℝ) ≤ ((z/4:ℕ):ℝ) := by exact_mod_cast hk
      have h2kR : (2:ℝ)*((z/4:ℕ):ℝ) ≤ ((z/2:ℕ):ℝ) := by exact_mod_cast hzk
      nlinarith
    have hlog := log_ge_two_div ((((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1)) (by linarith)
    have hbound : (50/77:ℝ) ≤ 2*((((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1)-1)/((((z/2:ℕ):ℝ)+1)/(((z/4:ℕ):ℝ)+1)+1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hr1]
    linarith
  have t2 : (11/69:ℝ) ≤ (1/6) * ((harmonic (z/3):ℝ) - (harmonic (z/9):ℝ)) := by
    have hsub := harmonic_sub_ge_log (z/9) (z/3) (by omega)
    have hr2 : (17:ℝ)/6 ≤ (((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1) := by
      rw [le_div_iff₀ (by positivity)]
      have hjR : (11:ℝ) ≤ ((z/9:ℕ):ℝ) := by exact_mod_cast hj
      have h3jR : (3:ℝ)*((z/9:ℕ):ℝ) ≤ ((z/3:ℕ):ℝ) := by exact_mod_cast hzj
      nlinarith
    have hlog := log_ge_two_div ((((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1)) (by linarith)
    have hbound : (22/23:ℝ) ≤ 2*((((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1)-1)/((((z/3:ℕ):ℝ)+1)/(((z/9:ℕ):ℝ)+1)+1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hr2]
    linarith
  have t3 : (2/39:ℝ) ≤ (1/12) * ((harmonic (z/6):ℝ) - (harmonic (z/12):ℝ)) := by
    have hsub := harmonic_sub_ge_log (z/12) (z/6) (by omega)
    have hr3 : (17:ℝ)/9 ≤ (((z/6:ℕ):ℝ)+1)/(((z/12:ℕ):ℝ)+1) := by
      rw [le_div_iff₀ (by positivity)]
      have hiR : (8:ℝ) ≤ ((z/12:ℕ):ℝ) := by exact_mod_cast hi
      have h2iR : (2:ℝ)*((z/12:ℕ):ℝ) ≤ ((z/6:ℕ):ℝ) := by exact_mod_cast hzi
      nlinarith
    have hlog := log_ge_two_div ((((z/6:ℕ):ℝ)+1)/(((z/12:ℕ):ℝ)+1)) (by linarith)
    have hbound : (8/13:ℝ) ≤ 2*((((z/6:ℕ):ℝ)+1)/(((z/12:ℕ):ℝ)+1)-1)/((((z/6:ℕ):ℝ)+1)/(((z/12:ℕ):ℝ)+1)+1) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [hr3]
    linarith
  have tn : -(1/12) * ((harmonic (z/18):ℝ) - (harmonic (z/36):ℝ)) ≥ -1/12 := by
    have hle : (harmonic (z/18):ℝ) - (harmonic (z/36):ℝ) ≤ 1 := by
      have hdiv := harmonic_sub_le_div (z/36) (z/18) (by omega)
      have hnum : z/18 ≤ 2*(z/36)+1 := by omega
      have hnumR : ((z/18:ℕ):ℝ) ≤ 2*((z/36:ℕ):ℝ)+1 := by exact_mod_cast hnum
      have : (((z/18:ℕ):ℝ) - ((z/36:ℕ):ℝ))/(((z/36:ℕ):ℝ)+1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    linarith
  have hnum : (9/20:ℝ) ≤ 25/77 + 11/69 + 2/39 - 1/12 := by norm_num
  unfold Ereal
  linarith [t1, t2, t3, tn, hnum]

/-! ## The small cases `z ∈ {2,3,5}` -/

private lemma mu_four : ArithmeticFunction.moebius 4 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)

private lemma phi_four : Nat.totient 4 = 2 := by
  rw [show (4:ℕ)=2^2 by norm_num, Nat.totient_prime_pow Nat.prime_two (by norm_num)]; norm_num

/-! ## Main theorem -/

theorem totient_sum_sub_harmonic_ge_of_small (z : ℕ) (hz : 2 ≤ z) (hzle : z ≤ 1000) (h4 : z ≠ 4) :
    (9/20 : ℝ) ≤ (∑ r ∈ Finset.Icc 1 z,
      ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / (Nat.totient r : ℝ))
      - (harmonic z : ℝ) := by
  by_cases h6 : 6 ≤ z
  · by_cases h100 : z ≤ 99
    · have hE : (9/20:ℚ) ≤ EQ z := EQ_ge z h6 h100
      have hcast : (9/20:ℝ) ≤ Ereal z := by
        have h2 : ((9/20:ℚ):ℝ) ≤ Ereal z := by
          rw [← Ereal_eq_EQ z]; exact_mod_cast hE
        norm_num at h2; exact h2
      linarith [hcast, D_ge_E z]
    · have hz100 : 100 ≤ z := by omega
      linarith [E_ge_of_large z hz100, D_ge_E z]
  · have hz5 : z ≤ 5 := by omega
    interval_cases z
    · norm_num [harmonic_real_Icc, Finset.sum_Icc_succ_top,
        ArithmeticFunction.moebius_apply_prime, Nat.totient_one, Nat.totient_two, Nat.prime_two]
    · norm_num [harmonic_real_Icc, Finset.sum_Icc_succ_top,
        ArithmeticFunction.moebius_apply_prime, Nat.totient_one, Nat.totient_two,
        Nat.totient_prime, Nat.prime_two]
    · exact absurd rfl h4
    · norm_num [harmonic_real_Icc, Finset.sum_Icc_succ_top,
        ArithmeticFunction.moebius_apply_prime, mu_four, Nat.totient_one, Nat.totient_two,
        Nat.totient_prime, phi_four, Nat.prime_two]

end Commons.NumberTheory.Totient
