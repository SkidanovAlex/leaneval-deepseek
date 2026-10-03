import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_le_two_pow_omega
import Submission.Commons.NumberTheory.FriedlanderIwaniec.square_divisor_max_characterization
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sqKernel_sq_dvd
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-!
# The average of `ρ(c²; d) / d`

For the Friedlander–Iwaniec analysis (§3, display (3.4)/(3.5)) one needs that the
number of solutions `ρ(c²; d)` of `α² + c⁴ ≡ 0 (mod d)` is, on average over `d`,
controlled by a power of `log`.  Writing `d₂(d) = ∏_{p ∣ d} p ^ ⌊v_p(d)/2⌋` for the
square root of the largest square divisor of `d`, the commons lemma
`sq_sum_sq_root_count_le_two_pow_omega` gives

`ρ(c²; d) ≤ 2 ^ ω(d) · gcd (c², d₂(d)) ≤ 2 ^ ω(d) · d₂(d)`,

so it suffices to bound `∑_{d ≤ D} 2 ^ ω(d) d₂(d) / d`.  Splitting `d = a · d₂(d)²`
with `a` squarefree (the squarefree kernel of `d`), we have

`2 ^ ω(d) d₂(d) / d = 2 ^ ω(d) / (a · d₂(d)) ≤ (2 ^ ω(a)/a) · (2 ^ ω(d₂)/d₂)`

because `ω(d) ≤ ω(a) + ω(d₂)`, and the summands are now separated.  Summing over the
pairs `(a, b)` with `a` squarefree, `b = d₂(d)` (an injection into `ℕ × ℕ`), and using
the elementary bound `∑_{n ≤ N} 2 ^ ω(n)/n ≤ (1 + log N)²` yields the result.
-/

/-! ## The elementary bound `∑_{n ≤ N} 2 ^ ω(n)/n ≤ (1 + log N)²` -/

/-- The arithmetic function `n ↦ 1/n`. -/
private noncomputable def invAFdiv : ArithmeticFunction ℝ where
  toFun := fun n => (n : ℝ)⁻¹
  map_zero' := by simp

private lemma invAFdiv_apply (n : ℕ) : invAFdiv n = (n : ℝ)⁻¹ := rfl

private lemma invAFdiv_mul_self {n : ℕ} (_hn : 0 < n) :
    (invAFdiv * invAFdiv) n = (n.divisors.card : ℝ) / (n : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => invAFdiv a * invAFdiv b)]
  simp only [invAFdiv_apply]
  have hpoint : ∀ i ∈ n.divisors, (i : ℝ)⁻¹ * ((n / i : ℕ) : ℝ)⁻¹ = (n : ℝ)⁻¹ := by
    intro i hi
    have hidvd : i ∣ n := Nat.dvd_of_mem_divisors hi
    have hni : n / i * i = n := Nat.div_mul_cancel hidvd
    rw [mul_comm, ← mul_inv, ← Nat.cast_mul, hni]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- `∑_{n ≤ N} 2 ^ ω(n)/n ≤ (1 + log N)²` for every `N`. -/
private lemma sum_two_pow_omega_div_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ))
      ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [Finset.Icc_eq_empty_iff.mpr (by norm_num : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty]
    rw [Nat.cast_zero, Real.log_zero]
    positivity
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  have h1 : ∑ n ∈ Finset.Ioc 0 N, (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)
      ≤ ∑ n ∈ Finset.Ioc 0 N, (invAFdiv * invAFdiv) n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnp : 0 < n := hn1
    rw [invAFdiv_mul_self hnp]
    have h2 : (2 : ℝ) ^ (Nat.primeFactors n).card ≤ ((Nat.divisors n).card : ℝ) := by
      exact_mod_cast two_pow_card_primeFactors_le_card_divisors hnp
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have h2 : ∑ n ∈ Finset.Ioc 0 N, (invAFdiv * invAFdiv) n
      = ∑ n ∈ Finset.Ioc 0 N, invAFdiv n * (∑ m ∈ Finset.Ioc 0 (N / n), invAFdiv m) :=
    ArithmeticFunction.sum_Ioc_mul_eq_sum_sum invAFdiv invAFdiv N
  have h3 : ∑ n ∈ Finset.Ioc 0 N, invAFdiv n * (∑ m ∈ Finset.Ioc 0 (N / n), invAFdiv m)
      ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
    have hInner : ∀ n ∈ Finset.Ioc 0 N,
        (∑ m ∈ Finset.Ioc 0 (N / n), invAFdiv m) ≤ 1 + Real.log (N : ℝ) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
      have hIoc : Finset.Ioc 0 (N / n) = Finset.Icc 1 (N / n) := by
        ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hIoc]
      have hcast : (∑ m ∈ Finset.Icc 1 (N / n), (m : ℝ)⁻¹) = (harmonic (N / n) : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast; rfl
      have hsum : (∑ m ∈ Finset.Icc 1 (N / n), invAFdiv m)
          = ∑ m ∈ Finset.Icc 1 (N / n), (m : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl; intro m _; simp only [invAFdiv_apply]
      rw [hsum, hcast]
      calc (harmonic (N / n) : ℝ) ≤ 1 + Real.log ((N / n : ℕ) : ℝ) :=
            harmonic_le_one_add_log (N / n)
        _ ≤ 1 + Real.log (N : ℝ) := by
            have hpos : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by
              have hle : 1 ≤ N / n := (Nat.one_le_div_iff (by omega : 0 < n)).mpr hnN
              exact_mod_cast hle
            have hle : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast Nat.div_le_self N n
            have hlog := Real.log_le_log hpos hle
            linarith
    calc ∑ n ∈ Finset.Ioc 0 N, invAFdiv n * (∑ m ∈ Finset.Ioc 0 (N / n), invAFdiv m)
        ≤ ∑ n ∈ Finset.Ioc 0 N, invAFdiv n * (1 + Real.log (N : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          apply mul_le_mul_of_nonneg_left (hInner n hn)
          simp only [invAFdiv_apply]; positivity
      _ = (∑ n ∈ Finset.Ioc 0 N, invAFdiv n) * (1 + Real.log (N : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ (1 + Real.log (N : ℝ)) * (1 + Real.log (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hIocN : Finset.Ioc 0 N = Finset.Icc 1 N := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIocN]
          have hcast : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]; push_cast; rfl
          have hsum : (∑ n ∈ Finset.Icc 1 N, invAFdiv n) = ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl; intro n _; simp only [invAFdiv_apply]
          rw [hsum, hcast]
          exact harmonic_le_one_add_log N
      _ = (1 + Real.log (N : ℝ)) ^ 2 := by ring
  calc ∑ n ∈ Finset.Ioc 0 N, (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)
      ≤ ∑ n ∈ Finset.Ioc 0 N, (invAFdiv * invAFdiv) n := h1
    _ = ∑ n ∈ Finset.Ioc 0 N, invAFdiv n * (∑ m ∈ Finset.Ioc 0 (N / n), invAFdiv m) := h2
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 := h3

/-! ## The square root of the largest square divisor -/

/-- `d₂(d) = ∏_{p ∣ d} p ^ ⌊v_p(d)/2⌋`, the square root of the largest square divisor of `d`. -/
private noncomputable def Kd (d : ℕ) : ℕ :=
  (Nat.primeFactors d).prod (fun p => p ^ (d.factorization p / 2))

private lemma Kd_sq_dvd (d : ℕ) : (Kd d) ^ 2 ∣ d := by
  rw [Kd]; exact sqKernel_sq_dvd d

private lemma Kd_pos (d : ℕ) (hd : 0 < d) : 0 < Kd d := by
  have h : 0 < (Kd d) ^ 2 := Nat.pos_of_dvd_of_pos (Kd_sq_dvd d) hd
  rcases Nat.eq_zero_or_pos (Kd d) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

/-- `2 ^ ω(n) / n`. -/
private noncomputable def gg (n : ℕ) : ℝ := (2 : ℝ) ^ (Nat.primeFactors n).card / (n : ℝ)

private lemma gg_nonneg (n : ℕ) : 0 ≤ gg n := by
  rw [gg]; positivity

/-- Pointwise separation of the summand: for `d > 0`, setting `b = d₂(d)` and
`a = d / b²`, one has `2 ^ ω(d) · b / d ≤ gg a · gg b`. -/
private lemma summand_le_gg (d : ℕ) (hd : 0 < d) :
    (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ)
      ≤ gg (d / (Kd d) ^ 2) * gg (Kd d) := by
  set b : ℕ := Kd d with hb
  set a : ℕ := d / b ^ 2 with ha
  have hb2dvd : b ^ 2 ∣ d := by rw [hb]; exact Kd_sq_dvd d
  have hd_eq : a * b ^ 2 = d := by rw [ha]; exact Nat.div_mul_cancel hb2dvd
  have hb2pos : 0 < b ^ 2 := Nat.pos_of_dvd_of_pos hb2dvd hd
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb2pos; simp at hb2pos
    · exact h
  have hb2le : b ^ 2 ≤ d := Nat.le_of_dvd hd hb2dvd
  have hapos : 0 < a := Nat.div_pos hb2le hb2pos
  have hane : a ≠ 0 := hapos.ne'
  have hbne : b ≠ 0 := hbpos.ne'
  -- cardinality inequality via the prime-factor inclusion
  have hpf : Nat.primeFactors d = Nat.primeFactors a ∪ Nat.primeFactors b := by
    rw [← hd_eq, Nat.primeFactors_mul hane (pow_ne_zero 2 hbne),
      Nat.primeFactors_pow b (by norm_num : (2 : ℕ) ≠ 0)]
  have hcard : (Nat.primeFactors d).card ≤ (Nat.primeFactors a).card + (Nat.primeFactors b).card := by
    rw [hpf]; exact Finset.card_union_le _ _
  have h2 : (2 : ℝ) ^ (Nat.primeFactors d).card
      ≤ (2 : ℝ) ^ (Nat.primeFactors a).card * (2 : ℝ) ^ (Nat.primeFactors b).card := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hcard
  have hdR : (d : ℝ) = (a : ℝ) * (b : ℝ) ^ 2 := by
    rw [← hd_eq]; push_cast; ring
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast hane
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbne
  have hgoal : ((2 : ℝ) ^ (Nat.primeFactors a).card * (2 : ℝ) ^ (Nat.primeFactors b).card)
      / ((a : ℝ) * (b : ℝ)) = gg a * gg b := by
    simp only [gg]
    rw [div_mul_div_comm]
  calc (2 : ℝ) ^ (Nat.primeFactors d).card * (b : ℝ) / (d : ℝ)
      = (2 : ℝ) ^ (Nat.primeFactors d).card / ((a : ℝ) * (b : ℝ)) := by
        rw [hdR, div_eq_div_iff (by positivity) (by positivity)]
        ring
    _ ≤ ((2 : ℝ) ^ (Nat.primeFactors a).card * (2 : ℝ) ^ (Nat.primeFactors b).card)
          / ((a : ℝ) * (b : ℝ)) := div_le_div_of_nonneg_right h2 (by positivity)
    _ = gg a * gg b := hgoal

/-- `∑_{d ≤ D} 2 ^ ω(d) d₂(d)/d ≤ (1 + log D)^4`. -/
private lemma sum_Kd_div_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
        (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ))
      ≤ (1 + Real.log (D : ℝ)) ^ 4 := by
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ)
        ≤ gg (d / (Kd d) ^ 2) * gg (Kd d) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    exact summand_le_gg d hd1
  have hinj : Set.InjOn (fun d => (d / (Kd d) ^ 2, Kd d)) ↑(Finset.Icc 1 D) := by
    intro d _ d' _ heq
    have hb : Kd d = Kd d' := congrArg Prod.snd heq
    have ha : d / (Kd d) ^ 2 = d' / (Kd d') ^ 2 := congrArg Prod.fst heq
    calc d = d / (Kd d) ^ 2 * (Kd d) ^ 2 := (Nat.div_mul_cancel (Kd_sq_dvd d)).symm
      _ = d' / (Kd d') ^ 2 * (Kd d') ^ 2 := by rw [ha, hb]
      _ = d' := Nat.div_mul_cancel (Kd_sq_dvd d')
  have hsub : (Finset.Icc 1 D).image (fun d => (d / (Kd d) ^ 2, Kd d))
      ⊆ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨d, hd, rfl⟩ := hp
    rw [Finset.mem_product]
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : 0 < d := hd1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hd).2
    have hb2dvd : (Kd d) ^ 2 ∣ d := Kd_sq_dvd d
    have hb2pos : 0 < (Kd d) ^ 2 := Nat.pos_of_dvd_of_pos hb2dvd hd0
    have hb2le : (Kd d) ^ 2 ≤ d := Nat.le_of_dvd hd0 hb2dvd
    have hKpos : 0 < Kd d := by
      rcases Nat.eq_zero_or_pos (Kd d) with h | h
      · rw [h] at hb2pos; simp at hb2pos
      · exact h
    have hKle : Kd d ≤ D := by
      have h1 : Kd d ≤ (Kd d) ^ 2 := by
        have := Nat.le_mul_of_pos_right (Kd d) hKpos
        simpa [pow_two] using this
      exact le_trans (le_trans h1 hb2le) hdD
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos hb2le hb2pos, le_trans (Nat.div_le_self d _) hdD⟩
    · rw [Finset.mem_Icc]
      exact ⟨hKpos, hKle⟩
  have hsum2 : (∑ a ∈ Finset.Icc 1 D, gg a) ≤ (1 + Real.log (D : ℝ)) ^ 2 := by
    have := sum_two_pow_omega_div_le D
    simpa only [gg] using this
  calc (∑ d ∈ Finset.Icc 1 D, (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D, gg (d / (Kd d) ^ 2) * gg (Kd d) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ (Finset.Icc 1 D).image (fun d => (d / (Kd d) ^ 2, Kd d)), gg p.1 * gg p.2 := by
        rw [Finset.sum_image (f := fun p => gg p.1 * gg p.2) hinj]
    _ ≤ ∑ p ∈ (Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D), gg p.1 * gg p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ => mul_nonneg (gg_nonneg _) (gg_nonneg _))
    _ = (∑ a ∈ Finset.Icc 1 D, gg a) * (∑ b ∈ Finset.Icc 1 D, gg b) := by
        rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ (1 + Real.log (D : ℝ)) ^ 2 * (1 + Real.log (D : ℝ)) ^ 2 :=
        mul_le_mul hsum2 hsum2 (Finset.sum_nonneg (fun b _ => gg_nonneg b)) (sq_nonneg _)
    _ = (1 + Real.log (D : ℝ)) ^ 4 := by ring

/-! ## The logarithm comparison -/

private lemma log_pow_ineq (D : ℕ) :
    (1 + Real.log (D : ℝ)) ^ 4 ≤ 16 * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    rw [Nat.cast_zero, mul_zero, zero_add]
    have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h6 : (2 / 3 : ℝ) ^ 6 ≤ (Real.log 2) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) hlog2.le 6
    have h16 : (1 : ℝ) ≤ 16 * (2 / 3 : ℝ) ^ 6 := by norm_num
    have h1 : 1 + Real.log (0 : ℝ) = 1 := by rw [Real.log_zero]; ring
    rw [h1]
    nlinarith [h6, h16]
  · have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hlog4 : (1 : ℝ) < Real.log 4 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [h4]; linarith [Real.log_two_gt_d9]
    have hlogge : (1 : ℝ) < Real.log (2 * (D : ℝ) + 2) := by
      have h4le : (4 : ℝ) ≤ 2 * (D : ℝ) + 2 := by linarith
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4le
      linarith
    have hlogDle : Real.log (D : ℝ) ≤ Real.log (2 * (D : ℝ) + 2) := by
      apply Real.log_le_log (by exact_mod_cast hD)
      linarith
    have hstep : 1 + Real.log (D : ℝ) ≤ 2 * Real.log (2 * (D : ℝ) + 2) := by linarith
    have hnn : 0 ≤ 1 + Real.log (D : ℝ) := by
      have : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg hD1
      linarith
    have hpow1 : (1 + Real.log (D : ℝ)) ^ 4 ≤ (2 * Real.log (2 * (D : ℝ) + 2)) ^ 4 :=
      pow_le_pow_left₀ hnn hstep 4
    have hpow2 : (Real.log (2 * (D : ℝ) + 2)) ^ 4 ≤ (Real.log (2 * (D : ℝ) + 2)) ^ 6 :=
      pow_le_pow_right₀ hlogge.le (by norm_num : (4 : ℕ) ≤ 6)
    calc (1 + Real.log (D : ℝ)) ^ 4
        ≤ (2 * Real.log (2 * (D : ℝ) + 2)) ^ 4 := hpow1
      _ = 16 * (Real.log (2 * (D : ℝ) + 2)) ^ 4 := by ring
      _ ≤ 16 * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by linarith

/-! ## The main theorem -/

theorem sum_rho_sq_div_le :
    ∃ C : ℝ, 0 < C ∧ ∀ D c : ℕ,
      (∑ d ∈ Finset.Icc 1 D, (({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℝ) / (d : ℝ))
        ≤ C * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := by
  refine ⟨16, by norm_num, ?_⟩
  intro D c
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      (({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℝ) / (d : ℝ)
        ≤ (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd0 : 0 < d := hd1
    have hpow : (((c ^ 2 : ℕ)) : ZMod d) ^ 2 = (c : ZMod d) ^ 4 := by
      rw [Nat.cast_pow]; ring
    have hset : ({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0} : Set (ZMod d))
        = {α : ZMod d | α ^ 2 + (((c ^ 2 : ℕ)) : ZMod d) ^ 2 = 0} := by
      ext α; rw [hpow]
    have hbound := sq_sum_sq_root_count_le_two_pow_omega (d := d) (b := c ^ 2) hd0
    have hbound' : ({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard
        ≤ 2 ^ (Nat.primeFactors d).card * Nat.gcd (c ^ 2) (Kd d) := by
      rw [hset]
      simpa [Kd] using hbound
    have hgcd : Nat.gcd (c ^ 2) (Kd d) ≤ Kd d := Nat.gcd_le_right (c ^ 2) (Kd_pos d hd0)
    have hfin : ((({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) := by
      have hcast : ((2 ^ (Nat.primeFactors d).card * Nat.gcd (c ^ 2) (Kd d) : ℕ) : ℝ)
          = (2 : ℝ) ^ (Nat.primeFactors d).card * (Nat.gcd (c ^ 2) (Kd d) : ℝ) := by
        push_cast; ring
      have hstep1 : ((({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℕ) : ℝ)
          ≤ ((2 ^ (Nat.primeFactors d).card * Nat.gcd (c ^ 2) (Kd d) : ℕ) : ℝ) := by
        exact_mod_cast hbound'
      rw [hcast] at hstep1
      calc ((({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (Nat.primeFactors d).card * (Nat.gcd (c ^ 2) (Kd d) : ℝ) := hstep1
        _ ≤ (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact_mod_cast hgcd
    have hdposR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    exact div_le_div_of_nonneg_right hfin hdposR.le
  calc (∑ d ∈ Finset.Icc 1 D, (({α : ZMod d | α ^ 2 + (c : ZMod d) ^ 4 = 0}).ncard : ℝ) / (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 D, (2 : ℝ) ^ (Nat.primeFactors d).card * (Kd d : ℝ) / (d : ℝ) :=
        Finset.sum_le_sum hpt
    _ ≤ (1 + Real.log (D : ℝ)) ^ 4 := sum_Kd_div_le D
    _ ≤ 16 * (Real.log (2 * (D : ℝ) + 2)) ^ 6 := log_pow_ineq D

end Commons.NumberTheory.FriedlanderIwaniec
