import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.q_trick_lower_struct
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_error_le
import Submission.Work.ChenPlan.LinearSieve.RI.support_lt
import Submission.Work.ChenPlan.LinearSieve.FrameworkR

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical

/-! ## Helper lemmas for the `Q`-trick (lower form) -/

/-- `Σ_{d ∣ n} μ(d) = [n = 1]`. -/
lemma moebius_sum_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if n = 1 then 1 else 0 := by
  have h1 : ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) * ArithmeticFunction.zeta
      : ArithmeticFunction ℝ) n = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]; rfl
  rw [← h1, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

lemma abs_moebius_cast_le_one (q : ℕ) :
    |((ArithmeticFunction.moebius q : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

lemma abs_lamMinus_le_one (P : ℕ) (D : ℝ) (d : ℕ) : |lamMinus P D d| ≤ 1 := by
  unfold lamMinus
  split_ifs with h
  · exact abs_moebius_cast_le_one d
  · simp

/-- `[q·d ∣ n] = [q ∣ n]·[d ∣ n]` for coprime `q, d`. -/
lemma ite_dvd_mul_of_coprime {q d n : ℕ} (h : Nat.Coprime q d) (w : ℝ) :
    (if q * d ∣ n then w else 0)
      = (if q ∣ n then (1 : ℝ) else 0) * ((if d ∣ n then (1 : ℝ) else 0) * w) := by
  have hiff : (q * d ∣ n) ↔ (q ∣ n ∧ d ∣ n) := by
    constructor
    · intro hc
      exact ⟨dvd_trans (dvd_mul_of_dvd_left (dvd_refl q) d) hc,
        dvd_trans (dvd_mul_of_dvd_right (dvd_refl d) q) hc⟩
    · rintro ⟨hq, hd⟩
      exact h.mul_dvd_of_dvd_of_dvd hq hd
  by_cases hq : q ∣ n
  · by_cases hd : d ∣ n
    · rw [if_pos hq, if_pos hd, if_pos (hiff.mpr ⟨hq, hd⟩)]; ring
    · rw [if_pos hq, if_neg hd, if_neg (fun hc => hd (hiff.mp hc).2)]; ring
  · by_cases hd : d ∣ n
    · rw [if_pos hd, if_neg hq, if_neg (fun hc => hq (hiff.mp hc).1)]; ring
    · rw [if_neg hq, if_neg hd, if_neg (fun hc => hq (hiff.mp hc).1)]; ring

lemma sum_ite_one_mul_mem {s : Finset ℕ} (p : ℕ → Prop) [DecidablePred p] (c : ℕ → ℝ) :
    (∑ q ∈ s, (if p q then (1 : ℝ) else 0) * c q) = ∑ q ∈ s.filter p, c q := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases h : p q <;> simp [h]

/-- The **`Q`-trick core** (lower form), the `λ⁻` analogue of `q_trick_upper_core`: the
lower-Moebius (minorant) property for the combined weights `μ(q)·λ⁻(d)` on the divisors `q·d`
(`q ∣ Q = Qmod A u₀`, `d ∣ (P/Q)(Z)`), the main-term factorisation
`∏_{p ∣ Q}(1-ν_p) × Σ_d λ⁻(d)ν_d`, and the remainder bound.  `Z² ≤ D'` is the classical side
condition of the lower sieve, which is what makes the `λ⁻` support land below the level (via
`RI.rdMinus_lt`); `u₀ ≤ Z` makes every prime of `Q` actually sifted (`Q ∣ Pz A Z`).

Vocabulary: `JR2/Defs.lean` (`Qmod`, `Qmod_dvd`, `subSieve`);
`Work.ChenPlan.LinearSieve.{Pz, lamMinus, siftedSumR}`; Mathlib's
`BoundingSieve.multSum_eq_main_err`.  Ingredients: `RI/lamMinus_sieve_lower.lean`
(`RI.lamMinus_moebius_sum_le` / `IsLowerMoebiusOn`), `RI/support_lt.lean` (`RI.rdMinus_lt`),
`A.nu_mult`.  (Note: `Pz A Z = Qmod A u₀ · Pz (subSieve …) Z` as `Finset`s/products is a useful
auxiliary fact; `Qmod_mul_VfR` gives the multiplicative version.) -/
theorem q_trick_lower_core (A : BoundingSieve) (u₀ Z D' : ℝ) (hu₀ : 2 ≤ u₀) (hu₀Z : u₀ ≤ Z)
    (hZ : 2 ≤ Z) (hD' : 1 < D') (hZ2 : Z ^ 2 ≤ D') :
    ( (∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
          ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                  (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                    (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ)
              * (Work.ChenPlan.LinearSieve.lamMinus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
              * A.multSum (q * d))
        ≤ Work.ChenPlan.LinearSieve.siftedSumR A Z )
    ∧ ( (∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
            ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
              ((ArithmeticFunction.moebius q : ℤ) : ℝ)
                * (Work.ChenPlan.LinearSieve.lamMinus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
                * A.nu (q * d))
          = (∏ p ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).primeFactors, (1 - A.nu p))
              * (∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
                  (Work.ChenPlan.LinearSieve.lamMinus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)
                    * A.nu d) )
    ∧ ( (∑ q ∈ (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀).divisors,
            ∑ d ∈ (Work.ChenPlan.LinearSieve.Pz
                    (Work.ChenPlan.LinearSieve.JR2.subSieve A (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀)
                      (Work.ChenPlan.LinearSieve.JR2.Qmod_dvd A u₀)) Z).divisors,
              |((ArithmeticFunction.moebius q : ℤ) : ℝ)
                * (Work.ChenPlan.LinearSieve.lamMinus (A.prodPrimes / Work.ChenPlan.LinearSieve.JR2.Qmod A u₀) D' d)|
                * |A.rem (q * d)|)
          ≤ ∑ m ∈ (Work.ChenPlan.LinearSieve.Pz A Z).divisors.filter
                  (fun m : ℕ => (m : ℝ) < (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ) * D'),
              (3 : ℝ) ^ m.primeFactors.card * |A.rem m| ) := by
  classical
  set Q := Qmod A u₀ with hQdef
  set Qz := Pz (subSieve A Q (Qmod_dvd A u₀)) Z with hQzdef
  have hstruct := Qmod_structure A u₀ Z hu₀ hu₀Z
  have hmul : Q * Qz = Pz A Z := hstruct.1
  have hcop : Nat.Coprime Q Qz := hstruct.2.1
  have hQpf : Q.primeFactors = A.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < u₀) :=
    hstruct.2.2.1
  have hQzpf : Qz.primeFactors
      = A.prodPrimes.primeFactors.filter (fun p : ℕ => u₀ ≤ (p : ℝ) ∧ (p : ℝ) < Z) :=
    hstruct.2.2.2.1
  have hQpz : ∀ p ∈ Qz.primeFactors, (p : ℝ) < Z ∧ u₀ ≤ (p : ℝ) := Qmod_Qz_prime_bound A u₀ Z hu₀ hu₀Z
  have hQsq : Squarefree Q := Squarefree.squarefree_of_dvd (Qmod_dvd A u₀) A.prodPrimes_squarefree
  have hQzsq : Squarefree Qz := RI.Pz_squarefree _ _
  have hQne : Q ≠ 0 := hQsq.ne_zero
  have hQz0 : Qz ≠ 0 := hQzsq.ne_zero
  have hQpos : 0 < Q := Nat.pos_iff_ne_zero.mpr hQne
  have hQz_dvdB : ∀ d ∈ Qz.divisors, d ∣ A.prodPrimes / Q :=
    fun d hd => (Nat.mem_divisors.mp hd).1.trans (RI.Pz_dvd_prodPrimes _ _)
  have hnu_mul : ∀ q ∈ Q.divisors, ∀ d ∈ Qz.divisors, A.nu (q * d) = A.nu q * A.nu d := by
    intro q hq d hd
    have hqQ : q ∣ Q := (Nat.mem_divisors.mp hq).1
    have hdQz : d ∣ Qz := (Nat.mem_divisors.mp hd).1
    exact A.nu_mult.map_mul_of_coprime ((hcop.coprime_dvd_left hqQ).coprime_dvd_right hdQz)
  have hgcd : ∀ n : ℕ,
      (if Nat.gcd n Q = 1 then (1 : ℝ) else 0) * (if Nat.gcd n Qz = 1 then (1 : ℝ) else 0)
        = (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) := by
    intro n
    rw [← hmul]
    by_cases h1 : Nat.gcd n Q = 1
    · by_cases h2 : Nat.gcd n Qz = 1
      · rw [if_pos h1, if_pos h2, if_pos (Nat.coprime_mul_iff_right.mpr ⟨h1, h2⟩)]
        ring
      · rw [if_pos h1, if_neg h2, if_neg (fun hc => h2 (Nat.coprime_mul_iff_right.mp hc).2)]
        ring
    · rw [if_neg h1, if_neg (fun hc => h1 (Nat.coprime_mul_iff_right.mp hc).1)]
      ring
  refine ⟨?_, ?_, ?_⟩
  · -- #### Conjunct 1: the minorant property
    have hQsum : ∀ n : ℕ,
        (∑ q ∈ Q.divisors, (if q ∣ n then (1 : ℝ) else 0) * ((ArithmeticFunction.moebius q : ℤ) : ℝ))
          = (if Nat.gcd n Q = 1 then (1 : ℝ) else 0) := by
      intro n
      rw [sum_ite_one_mul_mem]
      have hset : Q.divisors.filter (fun q => q ∣ n) = (Nat.gcd n Q).divisors := by
        ext d
        rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨Nat.dvd_gcd h2 h1, fun hh => hQne (Nat.gcd_eq_zero_iff.mp hh).2⟩
        · rintro ⟨h1, -⟩
          exact ⟨⟨dvd_trans h1 (Nat.gcd_dvd_right n Q), hQne⟩,
            dvd_trans h1 (Nat.gcd_dvd_left n Q)⟩
      rw [hset, moebius_sum_divisors]
    have hQzsum : ∀ n : ℕ,
        (∑ d ∈ Qz.divisors, (if d ∣ n then (1 : ℝ) else 0) * lamMinus (A.prodPrimes / Q) D' d)
          ≤ (if Nat.gcd n Qz = 1 then (1 : ℝ) else 0) := by
      intro n
      rw [sum_ite_one_mul_mem]
      have hset : Qz.divisors.filter (fun d => d ∣ n) = (Nat.gcd n Qz).divisors := by
        ext d
        rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩
          exact ⟨Nat.dvd_gcd h2 h1, fun hh => hQz0 (Nat.gcd_eq_zero_iff.mp hh).2⟩
        · rintro ⟨h1, -⟩
          exact ⟨⟨dvd_trans h1 (Nat.gcd_dvd_right n Qz), hQz0⟩,
            dvd_trans h1 (Nat.gcd_dvd_left n Qz)⟩
      rw [hset]
      have hlam : ∀ d ∈ (Nat.gcd n Qz).divisors, lamMinus (A.prodPrimes / Q) D' d
          = (if rdMinus D' d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
        intro d hd
        have hdQz : d ∣ Qz := (Nat.mem_divisors.mp hd).1.trans (Nat.gcd_dvd_right n Qz)
        have hdB : d ∣ A.prodPrimes / Q := hQz_dvdB d (Nat.mem_divisors.mpr ⟨hdQz, hQz0⟩)
        rw [lamMinus]
        by_cases h : rdMinus D' d
        · rw [if_pos ⟨hdB, h⟩, if_pos h]
        · rw [if_neg (fun hc => h hc.2), if_neg h]
      rw [Finset.sum_congr rfl hlam]
      exact RI.lamMinus_moebius_sum_le _
        (Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right n Qz) hQzsq) D' (by linarith)
    have hexp : (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d * A.multSum (q * d))
        = ∑ n ∈ A.support, A.weights n *
            (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
              (if q * d ∣ n then (1 : ℝ) else 0)
                * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d)) := by
      have hmm : ∀ q d : ℕ,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d * A.multSum (q * d)
            = ∑ n ∈ A.support,
                (if q * d ∣ n then (1 : ℝ) else 0)
                  * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d)
                  * A.weights n := by
        intro q d
        rw [BoundingSieve.multSum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases h : q * d ∣ n <;> simp [h]
      rw [Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun d _ => hmm q d))]
      rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      have hA : (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            (if q * d ∣ n then (1 : ℝ) else 0)
              * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d)
              * A.weights n)
          = (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
              (if q * d ∣ n then (1 : ℝ) else 0)
                * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d))
            * A.weights n := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Finset.sum_mul]
      rw [hA, mul_comm]
    have hinner : ∀ n : ℕ,
        (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            (if q * d ∣ n then (1 : ℝ) else 0)
              * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d))
          ≤ (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) := by
      intro n
      have hfac : ∀ q ∈ Q.divisors, ∀ d ∈ Qz.divisors,
          (if q * d ∣ n then (1 : ℝ) else 0)
              * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d)
            = ((if q ∣ n then (1 : ℝ) else 0) * ((ArithmeticFunction.moebius q : ℤ) : ℝ))
              * ((if d ∣ n then (1 : ℝ) else 0) * lamMinus (A.prodPrimes / Q) D' d) := by
        intro q hq d hd
        have hqQ : q ∣ Q := (Nat.mem_divisors.mp hq).1
        have hdQz : d ∣ Qz := (Nat.mem_divisors.mp hd).1
        rw [ite_dvd_mul_of_coprime ((hcop.coprime_dvd_left hqQ).coprime_dvd_right hdQz) 1]
        ring
      have hstep : (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            (if q * d ∣ n then (1 : ℝ) else 0)
              * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d))
          = (∑ q ∈ Q.divisors, (if q ∣ n then (1 : ℝ) else 0) * ((ArithmeticFunction.moebius q : ℤ) : ℝ))
            * (∑ d ∈ Qz.divisors,
                (if d ∣ n then (1 : ℝ) else 0) * lamMinus (A.prodPrimes / Q) D' d) := by
        rw [Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun d hd => hfac q hq d hd))]
        rw [Finset.sum_mul_sum]
      rw [hstep, hQsum n]
      calc (if Nat.gcd n Q = 1 then (1 : ℝ) else 0)
            * (∑ d ∈ Qz.divisors, (if d ∣ n then (1 : ℝ) else 0) * lamMinus (A.prodPrimes / Q) D' d)
          ≤ (if Nat.gcd n Q = 1 then (1 : ℝ) else 0) * (if Nat.gcd n Qz = 1 then (1 : ℝ) else 0) :=
            mul_le_mul_of_nonneg_left (hQzsum n) (by split <;> norm_num)
        _ = (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) := hgcd n
    rw [hexp]
    calc (∑ n ∈ A.support, A.weights n *
            (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
              (if q * d ∣ n then (1 : ℝ) else 0)
                * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d)))
        ≤ ∑ n ∈ A.support, (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) * A.weights n :=
          Finset.sum_le_sum (fun n _ => by
            calc A.weights n * (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
                  (if q * d ∣ n then (1 : ℝ) else 0)
                    * (((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d))
                ≤ A.weights n * (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) :=
                  mul_le_mul_of_nonneg_left (hinner n) (A.weights_nonneg n)
              _ = (if Nat.gcd n (Pz A Z) = 1 then (1 : ℝ) else 0) * A.weights n := by ring)
      _ = siftedSumR A Z := by
          rw [siftedSumR]
          refine Finset.sum_congr rfl (fun n _ => ?_)
          by_cases h : Nat.gcd n (Pz A Z) = 1
          · rw [if_pos h, if_pos ((RI.coprime_Pz_iff A n Z).mp h)]; ring
          · rw [if_neg h, if_neg (fun hh => h ((RI.coprime_Pz_iff A n Z).mpr hh))]; ring
  · -- #### Conjunct 2: the main-term factorisation
    have hQprod : (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) * A.nu q)
        = ∏ p ∈ Q.primeFactors, (1 - A.nu p) :=
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
        A.nu A.nu_mult hQsq).symm
    calc (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d * A.nu (q * d))
        = ∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            (((ArithmeticFunction.moebius q : ℤ) : ℝ) * A.nu q)
              * (lamMinus (A.prodPrimes / Q) D' d * A.nu d) := by
          refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun d hd => ?_))
          rw [hnu_mul q hq d hd]; ring
      _ = (∑ q ∈ Q.divisors, ((ArithmeticFunction.moebius q : ℤ) : ℝ) * A.nu q)
            * (∑ d ∈ Qz.divisors, lamMinus (A.prodPrimes / Q) D' d * A.nu d) := by
          rw [Finset.sum_mul_sum]
      _ = (∏ p ∈ Q.primeFactors, (1 - A.nu p))
            * (∑ d ∈ Qz.divisors, lamMinus (A.prodPrimes / Q) D' d * A.nu d) := by
          rw [hQprod]
  · -- #### Conjunct 3: the remainder bound
    set G : ℕ → ℝ := fun m =>
      if ((m : ℕ) : ℝ) < (Q : ℝ) * D' then (3 : ℝ) ^ m.primeFactors.card * |A.rem m| else 0
      with hG
    have hterm : ∀ q ∈ Q.divisors, ∀ d ∈ Qz.divisors,
        |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|
          ≤ G (q * d) := by
      intro q hq d hd
      have hqQ : q ∣ Q := (Nat.mem_divisors.mp hq).1
      have hdQz : d ∣ Qz := (Nat.mem_divisors.mp hd).1
      by_cases hlt : ((q * d : ℕ) : ℝ) < (Q : ℝ) * D'
      · rw [hG]
        simp only
        rw [if_pos hlt]
        have h1 : |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d| ≤ 1 := by
          rw [abs_mul]
          calc |((ArithmeticFunction.moebius q : ℤ) : ℝ)| * |lamMinus (A.prodPrimes / Q) D' d|
              ≤ 1 * 1 := mul_le_mul (abs_moebius_cast_le_one q)
                (abs_lamMinus_le_one _ _ _) (abs_nonneg _) (by norm_num)
            _ = 1 := one_mul 1
        calc |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|
            ≤ 1 * |A.rem (q * d)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ ≤ (3 : ℝ) ^ (q * d).primeFactors.card * |A.rem (q * d)| := by
              exact mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3))
                (abs_nonneg _)
      · rw [hG]
        simp only
        rw [if_neg hlt]
        have hzero : lamMinus (A.prodPrimes / Q) D' d = 0 := by
          by_contra hne
          by_cases hc : d ∣ A.prodPrimes / Q ∧ rdMinus D' d
          · obtain ⟨-, hrd⟩ := hc
            have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdQz hQzsq
            have hz : ∀ p ∈ d.primeFactors, (p : ℝ) < Z :=
              fun p hp => (hQpz p (RI.primeFactors_subset_of_dvd hdQz hQz0 hp)).1
            have hdl : (d : ℝ) < D' := RI.rdMinus_lt hD' hsqd hz hZ2 hrd
            have hqle : q ≤ Q := Nat.le_of_dvd hQpos hqQ
            have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
            have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
            have hdR : (0 : ℝ) ≤ (d : ℝ) := by positivity
            have hstep : ((q * d : ℕ) : ℝ) < (Q : ℝ) * D' := by
              push_cast
              calc (q : ℝ) * (d : ℝ) ≤ (Q : ℝ) * (d : ℝ) :=
                    mul_le_mul_of_nonneg_right (by exact_mod_cast hqle) hdR
                _ < (Q : ℝ) * D' := mul_lt_mul_of_pos_left hdl hQR
            exact hlt hstep
          · rw [lamMinus, if_neg hc] at hne
            exact hne rfl
        rw [hzero]
        simp
    have hsubset : (Q.divisors ×ˢ Qz.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) ⊆ (Pz A Z).divisors := by
      rw [Finset.image_subset_iff]
      rintro ⟨q, d⟩ hp
      simp only [Finset.mem_product, Nat.mem_divisors] at hp
      obtain ⟨⟨hqQ, -⟩, hdQz, -⟩ := hp
      rw [Nat.mem_divisors]
      exact ⟨by rw [← hmul]; exact Nat.mul_dvd_mul hqQ hdQz, RI.Pz_ne_zero A Z⟩
    have hGnn : ∀ m ∈ (Pz A Z).divisors,
        m ∉ (Q.divisors ×ˢ Qz.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) → 0 ≤ G m := by
      intro m _ _
      rw [hG]
      simp only
      split
      · positivity
      · norm_num
    calc (∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors,
            |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamMinus (A.prodPrimes / Q) D' d| * |A.rem (q * d)|)
        ≤ ∑ q ∈ Q.divisors, ∑ d ∈ Qz.divisors, G (q * d) :=
          Finset.sum_le_sum (fun q hq => Finset.sum_le_sum (fun d hd => hterm q hq d hd))
      _ = ∑ p ∈ Q.divisors ×ˢ Qz.divisors, G (p.1 * p.2) :=
          (Finset.sum_product Q.divisors Qz.divisors (fun p : ℕ × ℕ => G (p.1 * p.2))).symm
      _ = ∑ m ∈ (Q.divisors ×ˢ Qz.divisors).image (fun p : ℕ × ℕ => p.1 * p.2), G m :=
          (Finset.sum_image (mul_injOn_divisors hcop)).symm
      _ ≤ ∑ m ∈ (Pz A Z).divisors, G m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset hGnn
      _ = ∑ m ∈ (Pz A Z).divisors.filter (fun m : ℕ => (m : ℝ) < (Qmod A u₀ : ℝ) * D'),
            (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := by
          rw [hG]
          exact (Finset.sum_filter _ _).symm

end

end Work.ChenPlan.LinearSieve.JR2
