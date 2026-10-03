import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.two_pow_card_primeFactors_le_card_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.primitive_reps_ncard_le_four_mul_two_pow_omega

namespace Commons.NumberTheory.FriedlanderIwaniec

open scoped BigOperators
open Finset

/-- An integer whose square appears in a representation `a² + b² = n` with `n ≥ 1`
has absolute value at most `n`. -/
lemma natAbs_le_of_sq_add_sq_eq {n : ℕ} (hn : 1 ≤ n) {a b : ℤ}
    (h : a ^ 2 + b ^ 2 = (n : ℤ)) : a.natAbs ≤ n := by
  have h1 : a ^ 2 ≤ (n : ℤ) := by
    have : (0 : ℤ) ≤ b ^ 2 := sq_nonneg b
    linarith
  have h2 : ((a.natAbs ^ 2 : ℕ) : ℤ) ≤ (n : ℤ) := by
    rw [Nat.cast_pow, Int.natAbs_sq]; exact h1
  have h3 : a.natAbs ^ 2 ≤ n := by exact_mod_cast h2
  nlinarith [h3, hn, Nat.zero_le a.natAbs]

/-- The number of representations of `n ≥ 1` as a sum of two squares is at most
`4 · d(n)²`, where `d(n)` is the number of divisors of `n`.

Writing `d = gcd(a,b)` for a representation `a² + b² = n`, the reduced pair
`(a/d, b/d)` is a primitive representation of `n / d²`, so the representations are
partitioned by `d`; the prime-power expansion `d(n) = ∏ (e_p + 1)` then bounds the
number of possible `d` by `d(n)`, while each layer is controlled by the primitive
bound `4 · 2 ^ ω(n/d²) ≤ 4 · 2 ^ ω(n) ≤ 4 · d(n)`. -/
theorem ncard_two_squares_reps_le_divisors_sq (n : ℕ) (hn : 1 ≤ n) :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}).ncard ≤ 4 * (Nat.divisors n).card ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by omega
  set s : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
      (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)) with hs
  have hs_eq : ∀ p, p ∈ s → p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := by
    intro p hp; rw [hs, Finset.mem_filter] at hp; exact hp.2
  have hset : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)} : Set (ℤ × ℤ)) = ↑s := by
    ext p
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hs, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro hp
      have h1 : |p.1| ≤ (n : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast natAbs_le_of_sq_add_sq_eq hn hp
      have h2 : |p.2| ≤ (n : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast natAbs_le_of_sq_add_sq_eq hn (a := p.2) (b := p.1)
          (by rw [add_comm]; exact hp)
      exact ⟨⟨Finset.mem_Icc.mpr (abs_le.mp h1), Finset.mem_Icc.mpr (abs_le.mp h2)⟩, hp⟩
    · rintro ⟨-, hp⟩; exact hp
  rw [hset, Set.ncard_coe_finset]
  have hmap : ∀ p ∈ s, Int.gcd p.1 p.2 ∈ Nat.divisors n := by
    intro p hp
    rw [Nat.mem_divisors]
    refine ⟨?_, hn0⟩
    have hdvd1 : (Int.gcd p.1 p.2 : ℤ) ∣ p.1 := Int.gcd_dvd_left p.1 p.2
    have hdvd2 : (Int.gcd p.1 p.2 : ℤ) ∣ p.2 := Int.gcd_dvd_right p.1 p.2
    have e1 : (Int.gcd p.1 p.2 : ℤ) ∣ p.1 ^ 2 := by
      rw [pow_two]; exact dvd_mul_of_dvd_left hdvd1 p.1
    have e2 : (Int.gcd p.1 p.2 : ℤ) ∣ p.2 ^ 2 := by
      rw [pow_two]; exact dvd_mul_of_dvd_left hdvd2 p.2
    have : (Int.gcd p.1 p.2 : ℤ) ∣ (n : ℤ) := by
      rw [← hs_eq p hp]
      exact dvd_add e1 e2
    exact Int.ofNat_dvd.mp this
  have hfiber : ∀ b ∈ Nat.divisors n,
      (s.filter (fun p => Int.gcd p.1 p.2 = b)).card ≤ 4 * 2 ^ (n.primeFactors).card := by
    intro b hb
    rw [Nat.mem_divisors] at hb
    obtain ⟨hbdvd, -⟩ := hb
    have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd (by omega)
    by_cases hb2 : b ^ 2 ∣ n
    · have hb2pos : 0 < b ^ 2 := by positivity
      have hle1 : 1 ≤ n / b ^ 2 := by
        rw [Nat.le_div_iff_mul_le hb2pos, one_mul]
        exact Nat.le_of_dvd (by omega) hb2
      set T : Set (ℤ × ℤ) :=
        {q | q.1 ^ 2 + q.2 ^ 2 = ((n / b ^ 2 : ℕ) : ℤ) ∧ Int.gcd q.1 q.2 = 1} with hTdef
      have hT_bound : T.ncard ≤ 4 * 2 ^ (n.primeFactors).card := by
        have h1 := primitive_reps_ncard_le_four_mul_two_pow_omega (n / b ^ 2) hle1
        have h2 : ((n / b ^ 2).primeFactors).card ≤ (n.primeFactors).card :=
          Finset.card_le_card (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hb2) hn0)
        rw [hTdef]
        calc _ ≤ 4 * 2 ^ ((n / b ^ 2).primeFactors).card := h1
          _ ≤ 4 * 2 ^ (n.primeFactors).card :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h2) (by norm_num)
      have hTfin : T.Finite := by
        rw [hTdef]
        refine (Finset.finite_toSet (Finset.Icc (-((n / b ^ 2 : ℕ) : ℤ)) ((n / b ^ 2 : ℕ) : ℤ) ×ˢ
          Finset.Icc (-((n / b ^ 2 : ℕ) : ℤ)) ((n / b ^ 2 : ℕ) : ℤ))).subset ?_
        intro q hq
        simp only [Set.mem_ofPred_eq] at hq
        obtain ⟨hnq, -⟩ := hq
        have h1 : |q.1| ≤ (((n / b ^ 2 : ℕ)) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast natAbs_le_of_sq_add_sq_eq hle1 hnq
        have h2 : |q.2| ≤ (((n / b ^ 2 : ℕ)) : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast natAbs_le_of_sq_add_sq_eq hle1 (a := q.2) (b := q.1)
            (by rw [add_comm]; exact hnq)
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc]
        exact ⟨abs_le.mp h1, abs_le.mp h2⟩
      calc (s.filter (fun p => Int.gcd p.1 p.2 = b)).card
          = (↑(s.filter (fun p => Int.gcd p.1 p.2 = b)) : Set (ℤ × ℤ)).ncard :=
              (Set.ncard_coe_finset _).symm
        _ ≤ T.ncard := by
              apply Set.ncard_le_ncard_of_injOn
                (fun p : ℤ × ℤ => (p.1 / (b : ℤ), p.2 / (b : ℤ))) _ _ hTfin
              · intro p hp
                simp only [Finset.mem_coe, Finset.mem_filter] at hp
                obtain ⟨hps, hgcd⟩ := hp
                have hpn := hs_eq p hps
                have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
                have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
                set u : ℤ := p.1 / (b : ℤ) with hu_def
                set v : ℤ := p.2 / (b : ℤ) with hv_def
                have hu : u * (b : ℤ) = p.1 := by rw [hu_def]; exact Int.ediv_mul_cancel hd1
                have hv : v * (b : ℤ) = p.2 := by rw [hv_def]; exact Int.ediv_mul_cancel hd2
                have hbe : ((b : ℤ)) ^ 2 ≠ 0 := by
                  have : (b : ℤ) ≠ 0 := by exact_mod_cast hbpos.ne'
                  positivity
                have hnorm : u ^ 2 + v ^ 2 = ((n / b ^ 2 : ℕ) : ℤ) := by
                  have hprod : (u ^ 2 + v ^ 2) * (b : ℤ) ^ 2 = (n : ℤ) := by
                    have e1 : p.1 ^ 2 = u ^ 2 * (b : ℤ) ^ 2 := by rw [← hu]; ring
                    have e2 : p.2 ^ 2 = v ^ 2 * (b : ℤ) ^ 2 := by rw [← hv]; ring
                    rw [← hpn, e1, e2]; ring
                  have h3 : (n : ℤ) = ((n / b ^ 2 : ℕ) : ℤ) * (b : ℤ) ^ 2 := by
                    have h := Nat.div_mul_cancel hb2
                    have h' : ((n / b ^ 2 : ℕ) : ℤ) * ((b ^ 2 : ℕ) : ℤ) = (n : ℤ) := by
                      rw [← Nat.cast_mul, h]
                    rw [← h', Nat.cast_pow]
                  rw [h3] at hprod
                  exact mul_right_cancel₀ hbe hprod
                have hgc : Int.gcd u v = 1 := by
                  have h := Int.gcd_mul_right u (b : ℤ) v
                  rw [hu, hv, hgcd, Int.natAbs_natCast] at h
                  have hh : Int.gcd u v * b = 1 * b := by rw [one_mul]; exact h.symm
                  exact Nat.mul_right_cancel hbpos hh
                rw [hTdef]
                exact ⟨hnorm, hgc⟩
              · intro p hp q hq heq
                simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
                obtain ⟨hps, hgcd⟩ := hp
                obtain ⟨hqs, hgcdq⟩ := hq
                have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
                have hd1' : (b : ℤ) ∣ q.1 := by rw [← hgcdq]; exact Int.gcd_dvd_left q.1 q.2
                have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
                have hd2' : (b : ℤ) ∣ q.2 := by rw [← hgcdq]; exact Int.gcd_dvd_right q.1 q.2
                have h1 : p.1 / (b : ℤ) = q.1 / (b : ℤ) := by
                  have := congrArg Prod.fst heq; simpa using this
                have h2 : p.2 / (b : ℤ) = q.2 / (b : ℤ) := by
                  have := congrArg Prod.snd heq; simpa using this
                have hp1 : p.1 = q.1 := by
                  rw [← Int.ediv_mul_cancel hd1, h1, Int.ediv_mul_cancel hd1']
                have hp2 : p.2 = q.2 := by
                  rw [← Int.ediv_mul_cancel hd2, h2, Int.ediv_mul_cancel hd2']
                exact Prod.ext hp1 hp2
        _ ≤ 4 * 2 ^ (n.primeFactors).card := hT_bound
    · have hemp : (s.filter (fun p => Int.gcd p.1 p.2 = b)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hps, hgcd⟩ := hp
        exact hb2 (by
          have hd1 : (b : ℤ) ∣ p.1 := by rw [← hgcd]; exact Int.gcd_dvd_left p.1 p.2
          have hd2 : (b : ℤ) ∣ p.2 := by rw [← hgcd]; exact Int.gcd_dvd_right p.1 p.2
          have : ((b ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
            rw [← hs_eq p hps]; push_cast
            exact dvd_add (pow_dvd_pow_of_dvd hd1 2) (pow_dvd_pow_of_dvd hd2 2)
          exact Int.ofNat_dvd.mp this)
      rw [hemp, Finset.card_empty]
      positivity
  have hmain := Finset.card_le_mul_card_image_of_maps_to (s := s) (t := Nat.divisors n)
    (f := fun p : ℤ × ℤ => Int.gcd p.1 p.2) hmap (4 * 2 ^ (n.primeFactors).card) hfiber
  calc s.card ≤ (4 * 2 ^ (n.primeFactors).card) * (Nat.divisors n).card := hmain
    _ ≤ 4 * (Nat.divisors n).card ^ 2 := by
        have h2 : 2 ^ (n.primeFactors).card ≤ (Nat.divisors n).card :=
          two_pow_card_primeFactors_le_card_divisors (by omega)
        nlinarith [h2, Nat.zero_le (Nat.divisors n).card]

/-- The number of representations of `n` as a sum of two squares is
`O_ε(n^ε)`; needed for the lattice-point counts of §5. -/
theorem sum_two_squares_repr_le :
    ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}.ncard : ℕ) : ℝ)
        ≤ C * (n : ℝ) ^ eps := by
  intro eps heps
  obtain ⟨C', hC'pos, hC'⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow (eps / 2) (by linarith)
  refine ⟨4 * C' ^ 2, by positivity, ?_⟩
  intro n hn
  have h1 : ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}).ncard
      ≤ 4 * (Nat.divisors n).card ^ 2 := ncard_two_squares_reps_le_divisors_sq n hn
  have htau : ((Nat.divisors n).card : ℝ) ≤ C' * (n : ℝ) ^ (eps / 2) := hC' n
  have hcast : ((4 * (Nat.divisors n).card ^ 2 : ℕ) : ℝ)
      = 4 * ((Nat.divisors n).card : ℝ) ^ 2 := by push_cast; ring
  have hxsq : ((n : ℝ) ^ (eps / 2)) ^ 2 = (n : ℝ) ^ eps := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (eps / 2)) 2, ← Real.rpow_mul (by positivity)]
    congr 1; ring
  have hsq : ((Nat.divisors n).card : ℝ) ^ 2 ≤ C' ^ 2 * (n : ℝ) ^ eps := by
    calc ((Nat.divisors n).card : ℝ) ^ 2 ≤ (C' * (n : ℝ) ^ (eps / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) htau 2
      _ = C' ^ 2 * ((n : ℝ) ^ (eps / 2)) ^ 2 := by ring
      _ = C' ^ 2 * (n : ℝ) ^ eps := by rw [hxsq]
  calc ((({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}).ncard : ℕ) : ℝ)
      ≤ ((4 * (Nat.divisors n).card ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 4 * ((Nat.divisors n).card : ℝ) ^ 2 := hcast
    _ ≤ 4 * (C' ^ 2 * (n : ℝ) ^ eps) := by linarith [hsq]
    _ = 4 * C' ^ 2 * (n : ℝ) ^ eps := by ring

end Commons.NumberTheory.FriedlanderIwaniec
