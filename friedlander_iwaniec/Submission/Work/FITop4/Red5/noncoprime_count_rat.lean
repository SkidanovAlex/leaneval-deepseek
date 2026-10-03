import Mathlib
import Submission.Work.FIArea1.noncoprime_count

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Two natural numbers that are not coprime have a common prime divisor. -/
lemma exists_prime_dvd_of_not_coprime_nat {a b : ℕ} (h : ¬ Nat.Coprime a b) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ∣ b := by
  have hg : a.gcd b ≠ 1 := fun h1 => h (Nat.coprime_iff_gcd_eq_one.mpr h1)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  exact ⟨p, hp, hpd.trans (Nat.gcd_dvd_left a b), hpd.trans (Nat.gcd_dvd_right a b)⟩

/-- A positive value of the square indicator `Zint b` forces `b` to be a square. -/
lemma sq_of_Zint_pos {b : ℤ} (h : 0 < Work.FIPlan.Zint b) : ∃ c : ℤ, b = c ^ 2 :=
  Work.FIArea1.Zint_ne_zero_imp_sq b (ne_of_gt h)

/-- **The number of non-coprime `w`'s over a fixed `z`**, in the rational-coprimality form.

For `N < |z|² ≤ 2N` with `|z|²` squarefree and free of primes `≤ Pz`, at most
`400 (MN)^{1/4} (1 + √M/(Pz√N)) ω(|z|²)` elements `w` of the dyadic annulus `annM Pa` fail to
be coprime to `z` in the sense that `gcd(|w|², |z|²) > 1` while `Zint(Re wz) > 0`. -/
theorem noncoprime_count_rat (Pa : Work.FITop.Params) (z : GaussianInt)
    (hzlo : (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ))
    (hzhi : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N)
    (hsq : Squarefree (Work.FIPlan.gnorm z))
    (hnsp : ∀ p : ℕ, p.Prime → p ≤ Pa.Pz → ¬ p ∣ Work.FIPlan.gnorm z) :
    (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) ∧
          0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))).card : ℝ)
      ≤ 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  classical
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hnzR : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
  have hnz0 : Work.FIPlan.gnorm z ≠ 0 := by
    intro h0
    rw [h0] at hnzR
    exact absurd hnzR (by norm_num)
  set A : ℝ := (Pa.M * Pa.N) ^ ((1 : ℝ) / 4) with hA
  set B : ℝ := Real.sqrt Pa.M / Real.sqrt Pa.N with hB
  have hMN0 : (0 : ℝ) ≤ Pa.M * Pa.N := by nlinarith [Pa.hM1, Pa.hN1]
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hMN0 _
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- Every counted `w` shares a rational prime with `|z|²`.
  have hsub : (Work.FITop3.annM Pa).filter
        (fun w => ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) ∧
          0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))
      ⊆ (Work.FIPlan.gnorm z).primeFactors.biUnion (fun p =>
          (Work.FITop3.annM Pa).filter
            (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwann, hnc, hzint⟩ := hw
    obtain ⟨p, hpp, hpw, hpz⟩ := exists_prime_dvd_of_not_coprime_nat hnc
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · rw [Nat.mem_primeFactors]; exact ⟨hpp, hpz, hnz0⟩
    · rw [Finset.mem_filter]; exact ⟨hwann, hpw, sq_of_Zint_pos hzint⟩
  -- `count_annulus` for each prime, in the shape of the `p`-sum
  have hper : ∀ p ∈ (Work.FIPlan.gnorm z).primeFactors,
      (((Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
          ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ)
        ≤ 200 * A * (1 + B / (p : ℝ)) := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    have hlt : Pa.Pz < p := by
      by_contra hle
      exact hnsp p hpp (le_of_not_gt hle) hpd
    have hp2 : 2 < p := by have := Pa.hP2; omega
    have hmain := Work.FIArea1.count_annulus (Pa := Pa) (z := z) (p := p) hpp hp2
      hzlo hzhi hsq hpd
    have heq : 200 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)) = 200 * A * (1 + B / (p : ℝ)) := by
      rw [hA, hB]
      rw [show Real.sqrt Pa.M / ((p : ℝ) * Real.sqrt Pa.N)
            = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (p : ℝ) by ring]
    rwa [heq] at hmain
  calc (((Work.FITop3.annM Pa).filter
        (fun w => ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) ∧
          0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))).card : ℝ)
      ≤ (((Work.FIPlan.gnorm z).primeFactors.biUnion (fun p =>
          (Work.FITop3.annM Pa).filter (fun w => p ∣ Work.FIPlan.gnorm w ∧
            ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ p ∈ (Work.FIPlan.gnorm z).primeFactors, ((Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ p ∈ (Work.FIPlan.gnorm z).primeFactors, (((Work.FITop3.annM Pa).filter
          (fun w => p ∣ Work.FIPlan.gnorm w ∧ ∃ c : ℤ, Work.FIPlan.cForm w z = c ^ 2)).card : ℝ) := by
        push_cast; ring
    _ ≤ ∑ p ∈ (Work.FIPlan.gnorm z).primeFactors, 200 * A * (1 + B / (p : ℝ)) :=
        Finset.sum_le_sum hper
    _ = 200 * A * ∑ p ∈ (Work.FIPlan.gnorm z).primeFactors, (1 + B / (p : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 200 * A * (((Work.FIPlan.gnorm z).primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hPz0 : (0 : ℝ) < (Pa.Pz : ℝ) := by
          have := Pa.hP2; positivity
        calc ∑ p ∈ (Work.FIPlan.gnorm z).primeFactors, (1 + B / (p : ℝ))
            ≤ ∑ _p ∈ (Work.FIPlan.gnorm z).primeFactors, (1 + B / (Pa.Pz : ℝ)) := by
              apply Finset.sum_le_sum
              intro p hp
              obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
              have hlt : Pa.Pz < p := by
                by_contra hle
                exact hnsp p hpp (le_of_not_gt hle) hpd
              have hle : (Pa.Pz : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlt.le
              have : B / (p : ℝ) ≤ B / (Pa.Pz : ℝ) :=
                div_le_div_of_nonneg_left hB0 hPz0 hle
              linarith
          _ = ((Work.FIPlan.gnorm z).primeFactors.card : ℝ) * (1 + B / (Pa.Pz : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    _ = 200 * (A * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          * (1 + B / (Pa.Pz : ℝ))) := by ring
    _ ≤ 400 * (A * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)
          * (1 + B / (Pa.Pz : ℝ))) :=
        mul_le_mul_of_nonneg_right (by norm_num : (200 : ℝ) ≤ 400)
          (mul_nonneg (mul_nonneg hA0 (by positivity)) (by positivity))
    _ = 400 * A * (1 + B / (Pa.Pz : ℝ))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by ring
    _ = 400 * (Pa.M * Pa.N) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
        rw [hA, hB]
        rw [show Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N)
              = (Real.sqrt Pa.M / Real.sqrt Pa.N) / (Pa.Pz : ℝ) by ring]

end

end Work.FITop4.Red5
