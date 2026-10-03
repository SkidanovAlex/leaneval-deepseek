/-
  The passage from the main paper's sequence to the companion paper's objects.

  The main paper's development (`Submission/S3*.lean`) works with

      `an n = #{x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = n}`,  `Aseq x = ∑_{n ≤ x} an n`,
      `Ad d x = ∑_{n ≤ x, d ∣ n} an n`,  `gdens d = N(d)/d ^ 2`,

  while the companion paper ("Asymptotic sieve for primes") is stated for an abstract sequence
  `a : ℕ → ℝ` with counting function `Acount`, congruence sums `Ad`, density `g` and remainders
  `r`.  This file sets up the dictionary between the two and verifies the companion's
  hypotheses (1.7), (1.8), (1.9), (9.1) and (1.4).

  The one bookkeeping point is the pair `(0,0)`: `Acount`/`Ad` of the companion sum over
  `n ∈ [1, m]` whereas `Aseq`/`Ad` of the main paper sum over `n ∈ [0, m]`, and the extra term
  is `an 0 = 1`.
-/
import Mathlib
import Submission.S3g
import Submission.ASP.Defs
import Submission.ASP_R
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sum_Ad_le
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.ncard_sq_add_pow_four_ge
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_prime_sum
import Submission.Commons.NumberTheory.FriedlanderIwaniec.local_density_prime_sq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

namespace Submission.ASP

open Finset

noncomputable section

/-! ### The dictionary -/

/-- The Friedlander–Iwaniec sequence in the companion's language. -/
noncomputable def FIa (n : ℕ) : ℝ := (Submission.an n : ℝ)

/-- Its density `g(d) = N(d)/d²`. -/
noncomputable def FIg (d : ℕ) : ℝ := ((Submission.gdens d : ℚ) : ℝ)

/-- Its remainder function `r_d(m) = A_d(m) − g(d)A(m)`, in the companion's objects. -/
noncomputable def FIr (d m : ℕ) : ℝ := Ad FIa d m - FIg d * Acount FIa (m : ℝ)

/-- `an 0 = 1` (the pair `(0,0)`). -/
lemma FIa_zero : Submission.an 0 = 1 :=
  Commons.NumberTheory.FriedlanderIwaniec.X2Y4_an_zero

/-- `Acount FIa m = Aseq m − 1`. -/
lemma FI_Acount_eq (m : ℕ) : Acount FIa (m : ℝ) = (Submission.Aseq m : ℝ) - 1 := by
  have h0 : (0 : ℕ) ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
  have herase : (Finset.range (m + 1)).erase 0 = Finset.Icc 1 m := by
    ext n; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
  have hsum := Finset.sum_erase_add (Finset.range (m + 1))
    (fun n => (Submission.an n : ℝ)) h0
  rw [herase] at hsum
  rw [show (Submission.an 0 : ℝ) = 1 from by rw [FIa_zero]; norm_num] at hsum
  rw [Acount, Nat.floor_natCast, Submission.Aseq, Nat.cast_sum]
  simp only [FIa]
  rw [← hsum]
  ring

/-- `Ad FIa d m = Ad d m − 1` (the modulus `d` always divides `0`). -/
lemma FI_Ad_eq (d m : ℕ) : Ad FIa d (m : ℝ) = (Submission.Ad d m : ℝ) - 1 := by
  have h0 : (0 : ℕ) ∈ (Finset.range (m + 1)).filter (fun n => d ∣ n) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), dvd_zero d⟩
  have herase : ((Finset.range (m + 1)).filter (fun n => d ∣ n)).erase 0
      = (Finset.Icc 1 m).filter (fun n => d ∣ n) := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_erase_add ((Finset.range (m + 1)).filter (fun n => d ∣ n))
    (fun n => (Submission.an n : ℝ)) h0
  rw [herase] at hsum
  rw [show (Submission.an 0 : ℝ) = 1 from by rw [FIa_zero]; norm_num] at hsum
  rw [Ad, Nat.floor_natCast, Submission.Ad, Nat.cast_sum]
  simp only [FIa]
  rw [← hsum]
  ring

/-- The companion's remainder, expressed through the main paper's objects. -/
lemma FIr_eq (d m : ℕ) :
    FIr d m = (Submission.Ad d m : ℝ) - FIg d * (Submission.Aseq m : ℝ) + (FIg d - 1) := by
  rw [FIr, FI_Ad_eq, FI_Acount_eq]
  ring

/-- **Hypothesis (1.7) for the Friedlander–Iwaniec sequence** (holds by construction). -/
theorem FI_approx (x : ℝ) : Approx FIa FIg FIr x :=
  fun d m => by rw [FIr]; ring

/-! ### The companion's hypotheses for `FIa` -/

/-- (1.8): `0 ≤ g(p) < 1`. -/
theorem FI_gdens_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ FIg p ∧ FIg p < 1 :=
  ⟨by rw [FIg, Submission.gdens]; positivity,
   by rw [FIg]; exact_mod_cast Submission.gdens_prime_lt_one hp⟩

/-- (1.8): there is `C > 0` with `g(p) ≤ C/p` for every prime `p`. -/
theorem FI_gdens_bound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → FIg p ≤ C / (p : ℝ) := by
  refine ⟨2, by norm_num, fun p hp => ?_⟩
  have h := Submission.gdens_prime_mul_le hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [FIg, le_div_iff₀ hp0]
  have h2 : (((Submission.gdens p) * (p : ℚ) : ℚ) : ℝ) ≤ 2 := by exact_mod_cast h
  calc ((Submission.gdens p : ℚ) : ℝ) * (p : ℝ)
      = (((Submission.gdens p) * (p : ℚ) : ℚ) : ℝ) := by push_cast; ring
    _ ≤ 2 := h2

/-- (1.8): `g` is multiplicative. -/
theorem FI_gdens_mul {m n : ℕ} (h : Nat.Coprime m n) :
    FIg (m * n) = FIg m * FIg n := by
  rw [FIg, FIg, FIg, Submission.gdens_mul_of_coprime h]
  norm_num

/-- (1.8): `g 1 = 1`. -/
theorem FI_gdens_one : FIg 1 = 1 := by rw [FIg, Submission.gdens_one]; norm_num

/-- (1.9): `∑_{p ≤ y} g(p) = log log y + c + O((log y)^{-10})`, in the quotient form
`C / (log y)^10` (which equals `C·(log y)^{-10}`). -/
theorem FI_gdens_prime_sum :
    ∃ c : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, FIg p) - Real.log (Real.log y) - c|
        ≤ C / (Real.log y) ^ A := by
  obtain ⟨c, hc⟩ := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_gdens_prime_sum
  refine ⟨c, fun A hA => ?_⟩
  obtain ⟨C, hC, hsum⟩ := hc A hA
  refine ⟨C, hC, fun y hy => ?_⟩
  have h := hsum y hy
  rw [Nat.primesLE_eq_filter_range] at h
  have hset : (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime
      = (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩
  rw [hset] at h
  have hval : ∀ p : ℕ, FIg p
      = (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2 := by
    intro p
    rw [FIg, Submission.gdens, Submission.N]
    norm_num
  have hL : (∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, FIg p)
      = ∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime,
          (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2 :=
    Finset.sum_congr rfl fun p _ => hval p
  have h1 : |∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime, FIg p
        - Real.log (Real.log y) - c|
      = |∑ p ∈ (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime,
          (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard : ℝ) / (p : ℝ) ^ 2
            - (Real.log (Real.log y) + c)| := by
    rw [hL]; congr 1; ring
  rw [h1]
  exact h

/-- (9.1): `g(p²) ≤ g(p)` and `g(p²) ≤ 4/p²`. -/
theorem FI_gdens_prime_sq_le (p : ℕ) (hp : p.Prime) :
    FIg (p ^ 2) ≤ FIg p ∧ FIg (p ^ 2) * (p : ℝ) ^ 2 ≤ 4 := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.local_density_prime_sq_le p hp
  have hpow : ((p : ℝ) ^ 2) ^ 2 = (p : ℝ) ^ 4 := by ring
  rw [FIg, FIg, Submission.gdens, Submission.gdens, Submission.N, Submission.N]
  push_cast
  constructor
  · rw [hpow]; exact h.1
  · rw [hpow]
    have hp2 : (0:ℝ) < (p:ℝ)^2 := pow_pos (by exact_mod_cast hp.pos) 2
    have h2 := mul_le_mul_of_nonneg_right h.2 hp2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hp2)] at h2

/-- `an 1 ≥ 1` (the pair `(1,0)` represents `1`). -/
private lemma an_one_pos : 1 ≤ Submission.an 1 := by
  have hfin : ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = 1}).Finite := by
    have h1 : ({a : ℤ | a ^ 2 ≤ 1}).Finite := by
      have h : {a : ℤ | a ^ 2 ≤ 1} = Set.Icc (-1) 1 := by
        ext a
        simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · intro ha; exact ⟨by nlinarith [sq_nonneg a], by nlinarith [sq_nonneg a]⟩
        · rintro ⟨ha1, ha2⟩; nlinarith
      rw [h]; exact Set.finite_Icc _ _
    have h2 : ({b : ℤ | b ^ 4 ≤ 1}).Finite := by
      have h : {b : ℤ | b ^ 4 ≤ 1} = {b : ℤ | b ^ 2 ≤ 1} := by
        ext b
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro hb <;> nlinarith [sq_nonneg b, sq_nonneg (b ^ 2)]
      rw [h]; exact h1
    refine (h1.prod h2).subset ?_
    rintro ⟨a, b⟩ hab
    simp only [Set.mem_prod, Set.mem_ofPred_eq] at hab ⊢
    exact ⟨by nlinarith [hab, sq_nonneg a, show (0:ℤ) ≤ b ^ 4 by positivity],
           by nlinarith [hab, sq_nonneg a, show (0:ℤ) ≤ b ^ 4 by positivity]⟩
  rw [Submission.an]
  exact Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt ((Set.ncard_pos hfin).mpr ⟨(1, 0), by norm_num⟩))

end

end Submission.ASP
