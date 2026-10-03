/-
# Pólya–Vinogradov for the Jacobi-symbol character `(·|b)` (FI (22.5), (11.16))

The proof is assembled from

* the Dirichlet character `jacobiChar b` (`Submission/Work/FIArea4/JacobiChar.lean`),
* the squarefree kernel `sqfreeKernel`/`sqPart` (`Submission/Work/FIArea4/SqfreeKernel.lean`),
* the Pólya–Vinogradov inequality for *primitive* characters
  (`Submission/Work/FIArea4/pv_primitive.lean`),
* primitivity of the Jacobi character of a squarefree odd modulus
  (`Submission/Work/FIArea4/jacobiChar_isPrimitive.lean`),
* the reduction `J(n|m) = J(n|sqfreeKernel m)` for `(n,m) = 1`
  (`Submission/Work/FIArea4/jacobiSym_sqfreeKernel_of_coprime.lean`),
* the Möbius coprimality sieve (`Submission/Work/FIArea4/sum_coprime_mul_eq.lean`) and the
  count of squarefree divisors of `2^e s^2` (`Submission/Work/FIArea4/card_divisors_rad_le.lean`).
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.JacobiChar
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.Assembly
import Submission.Work.FIArea4.norm_stdAddChar_sub_one_lower
import Submission.Work.FIArea4.geom_sum_bound
import Submission.Work.FIArea4.sum_filter_ne_zero_eq
import Submission.Work.FIArea4.pv_primitive
import Submission.Work.FIArea4.jacobiChar_isPrimitive
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.jacobiSym_sqfreeKernel_of_coprime
import Submission.Work.FIArea4.sum_coprime_mul_eq
import Submission.Work.FIArea4.card_divisors_rad_le

namespace Work.FIArea4

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- `J(n | b) = J(n | oddPart b)` when `n` is coprime to `b` (the `2`-adic part of the Jacobi
symbol equals one on odd arguments, and `n` is odd as soon as `2 ∣ b` and `(n,b) = 1`). -/
lemma jacobiSym_eq_jacobiSym_oddPart_of_coprime {n b : ℕ} (h : n.gcd b = 1) :
    jacobiSym (n : ℤ) b = jacobiSym (n : ℤ) (oddPart b) := by
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [Work.FIPlan.oddPart]
  · haveI : NeZero (oddPart b) := ⟨oddPart_ne_zero hb0⟩
    conv_lhs => rw [← oddPart_mul_two_pow b]
    rw [jacobiSym.mul_right]
    have h2 : jacobiSym (n : ℤ) (2 ^ (b.factorization 2)) = 1 := by
      by_cases he : b.factorization 2 = 0
      · rw [he]; simp
      · have h2b : 2 ∣ b := Nat.dvd_of_factorization_pos he
        have hn : ¬ 2 ∣ n := fun h2n => by
          have hd : 2 ∣ n.gcd b := Nat.dvd_gcd h2n h2b
          omega
        exact jacobiSym_two_pow_eq_one_of_odd (by rw [Nat.odd_iff]; omega)
    rw [h2, one_mul]

/-- For `n` coprime to `b`, the Jacobi symbol `J(n | b)` is the value of the Jacobi character of
the squarefree kernel of the odd part of `b`. -/
lemma jacobiSym_eq_jacobiSym_sqfreeKernel_of_gcd_eq_one {n b : ℕ} (h : n.gcd b = 1) :
    jacobiSym (n : ℤ) b = jacobiSym (n : ℤ) (sqfreeKernel (oddPart b)) := by
  rw [jacobiSym_eq_jacobiSym_oddPart_of_coprime h]
  have h1 : Nat.Coprime n b := Nat.coprime_iff_gcd_eq_one.mpr h
  refine jacobiSym_sqfreeKernel_of_coprime ?_
  rw [← Nat.coprime_iff_gcd_eq_one]
  exact Nat.Coprime.coprime_dvd_right (oddPart_dvd b) h1

/-- `J(n | b) = 0` when `n` is not coprime to `b`. -/
lemma jacobiSym_eq_zero_of_gcd_ne_one {n b : ℕ} (hb : b ≠ 0) (h : n.gcd b ≠ 1) :
    jacobiSym (n : ℤ) b = 0 := by
  refine jacobiSym.eq_zero_iff.mpr ⟨hb, ?_⟩
  intro hcontra
  exact h (by
    have : ((n : ℤ).natAbs).gcd b = 1 := by simpa using hcontra
    simpa using this)

/-- **Pólya–Vinogradov for the Jacobi-symbol character `(·|b)` (FI (22.5), (11.16)).**
For `b ≥ 1` whose *odd part* is not a perfect square, the function `n ↦ J(n | b)` is a
non-principal Dirichlet character modulo `b` (multiplicative in `n`, periodic mod `b`, vanishing
exactly on the `n` with `gcd(n,b) ≠ 1`), and its partial sums satisfy the Pólya–Vinogradov bound
with an absolute constant.  `oddPart b = b / 2 ^ (b.factorization 2)` is the odd part of `b`,
in `Submission/Work/FIPlan/Interface.lean` (frozen vocabulary of this workspace). -/
theorem polya_vinogradov :
    ∃ C : ℝ, 0 < C ∧ ∀ (b N : ℕ), 1 ≤ b →
      (∀ k : ℕ, Work.FIPlan.oddPart b ≠ k ^ 2) →
      |∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℝ)|
        ≤ C * Real.sqrt b * (Real.log b + 1) := by
  refine ⟨8, by norm_num, ?_⟩
  intro b N hb hns
  have hb0 : b ≠ 0 := by omega
  set m := oddPart b with hm
  set m₁ := sqfreeKernel m with hm1
  set s := sqPart m with hs
  have hm_ne : m ≠ 0 := (oddPart_pos hb0).ne'
  have hm_dvd : m ∣ b := by rw [hm]; exact oddPart_dvd b
  have hm_le : m ≤ b := by rw [hm]; exact oddPart_le b
  have hm_odd : Odd m := by rw [hm]; exact oddPart_odd hb0
  have hb_split : b = 2 ^ (b.factorization 2) * m := by
    rw [hm]; exact (oddPart_mul_two_pow b).symm
  -- structure of the squarefree kernel
  obtain ⟨hsq_dvd₀, hs_max₀, hmul₀, hm1_dvd₀, hm1_sqf₀⟩ := sqfree_kernel m hm_ne
  have hsq_dvd : s ^ 2 ∣ m := hsq_dvd₀
  have hs_max : ∀ t : ℕ, t ^ 2 ∣ m → t ≤ s := hs_max₀
  have hmul : m₁ * s ^ 2 = m := hmul₀
  have hm1_dvd : m₁ ∣ m := hm1_dvd₀
  have hm1_sqf : Squarefree m₁ := hm1_sqf₀
  have hm1_ne1 : m₁ ≠ 1 := by
    intro h
    refine hns s ?_
    rw [← hmul, h, one_mul]
  have hm1_dvd_b : m₁ ∣ b := hm1_dvd.trans hm_dvd
  have hm1_pos : 0 < m₁ := Nat.pos_of_dvd_of_pos hm1_dvd (by rw [hm]; exact oddPart_pos hb0)
  have hm1_odd : Odd m₁ := hm_odd.of_dvd_nat hm1_dvd
  have hm1_le_b : m₁ ≤ b :=
    le_trans (Nat.le_of_dvd (by rw [hm]; exact oddPart_pos hb0) hm1_dvd) hm_le
  have hm1_ge3 : 3 ≤ m₁ := by
    have h2 : 2 ≤ m₁ := by omega
    obtain ⟨k, hk⟩ := hm1_odd
    omega
  have hs_pos : 1 ≤ s := hs_max 1 (by norm_num)
  have hs_sq : s ^ 2 * m₁ = m := by rw [mul_comm]; exact hmul
  haveI : NeZero m₁ := ⟨hm1_pos.ne'⟩
  -- the primitive character and its Pólya–Vinogradov bound
  have hprim : (jacobiChar m₁).IsPrimitive := jacobiChar_isPrimitive hm1_sqf hm1_odd hm1_ge3
  have hpv : ∀ X : ℕ, ‖∑ n ∈ Finset.Icc 1 X, (jacobiSym (n : ℤ) m₁ : ℂ)‖
      ≤ 4 * Real.sqrt m₁ * (Real.log m₁ + 1) := fun X => by
    have h := pv_primitive (jacobiChar m₁) hprim (by omega) (norm_jacobiChar_le_one m₁) X
    simpa only [jacobiChar_natCast] using h
  -- the sieve modulus
  have hc0 : b / m₁ ≠ 0 := by
    have : 0 < b / m₁ := Nat.div_pos (Nat.le_of_dvd (by omega) hm1_dvd_b) hm1_pos
    omega
  have hdiv : b / m₁ = 2 ^ (b.factorization 2) * s ^ 2 := by
    conv_lhs => rw [hb_split]
    rw [
      show 2 ^ (b.factorization 2) * m = m₁ * (2 ^ (b.factorization 2) * s ^ 2) from by
        rw [← hmul]; ring,
      Nat.mul_div_cancel_left _ hm1_pos]
  -- pointwise reduction
  have hpoint : ∀ n : ℕ, (jacobiSym (n : ℤ) b : ℂ)
      = if n.gcd (b / m₁) = 1 then (jacobiSym (n : ℤ) m₁ : ℂ) else 0 := by
    intro n
    by_cases hg : n.gcd b = 1
    · have hgb : n.gcd (b / m₁) = 1 := by
        have h1 : Nat.Coprime n b := Nat.coprime_iff_gcd_eq_one.mpr hg
        exact Nat.coprime_iff_gcd_eq_one.mp
          (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hm1_dvd_b) h1)
      rw [if_pos hgb]
      have h1 : jacobiSym (n : ℤ) b = jacobiSym (n : ℤ) m₁ := by
        rw [show m₁ = sqfreeKernel (oddPart b) from by rw [hm1, hm]]
        exact jacobiSym_eq_jacobiSym_sqfreeKernel_of_gcd_eq_one hg
      rw [h1]
    · rw [jacobiSym_eq_zero_of_gcd_ne_one hb0 hg]
      by_cases hgb : n.gcd (b / m₁) = 1
      · rw [if_pos hgb]
        have hmc : n.gcd m₁ ≠ 1 := by
          obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
          have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_left n b)
          have hpb : p ∣ b := hpdvd.trans (Nat.gcd_dvd_right n b)
          have hpm : p ∣ m₁ := by
            by_contra hpnot
            have hb_eq : b = m₁ * (b / m₁) := (Nat.mul_div_cancel' hm1_dvd_b).symm
            have hpdiv : p ∣ m₁ * (b / m₁) := by rwa [← hb_eq]
            rcases hp.dvd_mul.mp hpdiv with h | h
            · exact absurd h hpnot
            · have hp1 : p ∣ n.gcd (b / m₁) := Nat.dvd_gcd hpn h
              have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) (by rwa [hgb] at hp1)
              have h2 := hp.two_le
              omega
          have hp1 : p ∣ n.gcd m₁ := Nat.dvd_gcd hpn hpm
          intro hcon
          have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) (by rwa [hcon] at hp1)
          have h2 := hp.two_le
          omega
        rw [jacobiSym_eq_zero_of_gcd_ne_one hm1_pos.ne' hmc]
      · rw [if_neg hgb]
        simp
  -- the sieve
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ)
      = ∑ d ∈ (∏ p ∈ (b / m₁).primeFactors, p).divisors,
          (ArithmeticFunction.moebius d : ℂ) * (jacobiSym (d : ℤ) m₁ : ℂ)
            * ∑ n' ∈ Finset.Icc 1 (N / d), (jacobiSym (n' : ℤ) m₁ : ℂ) := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ)
        = ∑ n ∈ Finset.Icc 1 N,
            (if n.gcd (b / m₁) = 1 then (jacobiSym (n : ℤ) m₁ : ℂ) else 0) :=
      Finset.sum_congr rfl (fun n _ => hpoint n)
    rw [h1, ← Finset.sum_filter]
    exact sum_coprime_mul_eq hc0 (fun n => (jacobiSym (n : ℤ) m₁ : ℂ)) (by simp)
      (fun a c => by
        simp only [jacobiSym_mul_nat]
        push_cast
        ring)
  -- the bound
  have hmain : ‖∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ)‖
      ≤ 8 * Real.sqrt b * (Real.log b + 1) := by
    rw [hsum_eq]
    have hcard : ((∏ p ∈ (b / m₁).primeFactors, p).divisors.card : ℝ) ≤ 2 * s := by
      have h := card_divisors_rad_le (e := b.factorization 2) (s := s) hs_pos
      rw [← hdiv] at h
      exact_mod_cast h
    calc ‖∑ d ∈ (∏ p ∈ (b / m₁).primeFactors, p).divisors,
            (ArithmeticFunction.moebius d : ℂ) * (jacobiSym (d : ℤ) m₁ : ℂ)
              * ∑ n' ∈ Finset.Icc 1 (N / d), (jacobiSym (n' : ℤ) m₁ : ℂ)‖
        ≤ ∑ d ∈ (∏ p ∈ (b / m₁).primeFactors, p).divisors,
            (4 * Real.sqrt m₁ * (Real.log m₁ + 1)) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun d _ => ?_))
          have hd1 : ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            have h := ArithmeticFunction.abs_moebius_le_one (n := d)
            exact_mod_cast h
          have hd2 : ‖((jacobiSym (d : ℤ) m₁ : ℤ) : ℂ)‖ ≤ 1 := by
            rcases jacobiSym.trichotomy (d : ℤ) m₁ with h | h | h <;> rw [h] <;> norm_num
          calc ‖((ArithmeticFunction.moebius d : ℤ) : ℂ) * ((jacobiSym (d : ℤ) m₁ : ℤ) : ℂ)
                  * ∑ n' ∈ Finset.Icc 1 (N / d), (jacobiSym (n' : ℤ) m₁ : ℂ)‖
              = ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖
                  * ‖((jacobiSym (d : ℤ) m₁ : ℤ) : ℂ)‖
                  * ‖∑ n' ∈ Finset.Icc 1 (N / d), (jacobiSym (n' : ℤ) m₁ : ℂ)‖ := by
                rw [norm_mul, norm_mul]
            _ ≤ 1 * 1 * (4 * Real.sqrt m₁ * (Real.log m₁ + 1)) := by
                gcongr
                exact hpv _
            _ = 4 * Real.sqrt m₁ * (Real.log m₁ + 1) := by ring
      _ = ((∏ p ∈ (b / m₁).primeFactors, p).divisors.card : ℝ)
            * (4 * Real.sqrt m₁ * (Real.log m₁ + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * s) * (4 * Real.sqrt m₁ * (Real.log m₁ + 1)) := by
          have h1 : (0:ℝ) ≤ 4 * Real.sqrt m₁ * (Real.log m₁ + 1) := by positivity
          exact mul_le_mul_of_nonneg_right hcard h1
      _ ≤ 8 * Real.sqrt b * (Real.log b + 1) := by
          have hs_sqrt : (s : ℝ) * Real.sqrt m₁ = Real.sqrt m := by
            have h1 : (s : ℝ) = Real.sqrt ((s : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
            rw [h1, ← Real.sqrt_mul (by positivity)]
            congr 1
            rw [← hs_sq]; push_cast; ring
          have hsqrt : Real.sqrt m ≤ Real.sqrt b :=
            Real.sqrt_le_sqrt (by exact_mod_cast hm_le)
          have hlog : Real.log m₁ + 1 ≤ Real.log b + 1 := by
            have h1 : Real.log m₁ ≤ Real.log b :=
              Real.log_le_log (by exact_mod_cast hm1_pos) (by exact_mod_cast hm1_le_b)
            linarith
          calc (2 * s) * (4 * Real.sqrt m₁ * (Real.log m₁ + 1))
              = 8 * ((s : ℝ) * Real.sqrt m₁) * (Real.log m₁ + 1) := by ring
            _ = 8 * Real.sqrt m * (Real.log m₁ + 1) := by rw [hs_sqrt]
            _ ≤ 8 * Real.sqrt b * (Real.log b + 1) := by gcongr
  -- transfer back to `ℝ`
  have hre : (∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℝ))
      = (∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ)).re := by
    have h1 : (((∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℝ)) : ℝ) : ℂ)
        = ∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      push_cast
      ring
    rw [← h1]
    exact (Complex.ofReal_re _).symm
  calc |∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℝ)|
      = |((∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ))).re| := by rw [← hre]
    _ ≤ ‖∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) b : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ 8 * Real.sqrt b * (Real.log b + 1) := hmain

end

end Work.FIArea4
