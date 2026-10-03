/-
# `peelCorrectionW` — the exceptional-prime-divisor correction of the peeled small part

The sub-sum of the peeled linear part in which the prime variable `p` divides the shifted
modulus `c·q` has at most `ω(cq) ≤ log₂(cq+2)` terms for each `q`, each of size
`‖λ(cpq)‖ ≤ 4τ(cpq) ≤ 8τ(c)τ(q)`; hence
`Σ_{q ≤ z} Σ_{p ∣ cq} ‖λ(cpq)‖ ≤ C·τ(c)·log(c+2)·z·log(u+2)^A`.
-/
import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallAux
import Submission.Work.FIArea7.divisor_sum_Icc_le
import Submission.Work.FIArea7.normQuadEigenLe

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `τ(m·n) ≤ τ(m)·τ(n)`. -/
lemma tau_mul_le' (m n : ℕ) : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- `ω(n) ≤ log(n+2)/log 2`. -/
lemma card_primeFactors_cast_le_log (n : ℕ) :
    ((n.primeFactors.card : ℕ) : ℝ) ≤ Real.log ((n : ℝ) + 2) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : (2 : ℕ) ^ n.primeFactors.card ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [Nat.primeFactors_zero, Finset.card_empty, pow_zero]
      exact Nat.le_refl 1
    · have hprod2 : (2 : ℕ) ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
        have hconst : ∏ _p ∈ n.primeFactors, (2 : ℕ) = (2 : ℕ) ^ n.primeFactors.card :=
          Finset.prod_const (2 : ℕ)
        rw [← hconst]
        exact Finset.prod_le_prod' (fun p hp =>
          ((Nat.mem_primeFactors_of_ne_zero h.ne').mp hp).1.two_le)
      calc (2 : ℕ) ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := hprod2
        _ ≤ n := Nat.le_of_dvd h (Nat.prod_primeFactors_dvd n)
        _ ≤ n + 1 := Nat.le_succ n
  have hleR : (((2 : ℕ) ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast hle
  have hcast : (((2 : ℕ) ^ n.primeFactors.card : ℕ) : ℝ) = (2 : ℝ) ^ (n.primeFactors.card) := by
    push_cast; ring
  rw [hcast] at hleR
  have h3 : (2 : ℝ) ^ (n.primeFactors.card) ≤ (n : ℝ) + 2 := by linarith
  have h4 : Real.log ((2 : ℝ) ^ (n.primeFactors.card)) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  exact (le_div_iff₀ hlog2).mpr (by simpa using h4)

theorem peelCorrectionW :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ),
        1 ≤ c → 2 ≤ z →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
              ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
          ≤ C * (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c : ℝ) + 2) * (z : ℝ)
              * (Real.log ((u : ℝ) + 2)) ^ A := by
  obtain ⟨Ct, hCt, ht⟩ := Work.FIArea7.divisor_sum_Icc_le
  refine ⟨16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3) + 1, 2, by positivity,
    by norm_num, ?_⟩
  intro chi k c u z hc hz hchi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hτc : (0 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hznn : (0 : ℝ) ≤ (z : ℝ) := by positivity
  have hψ : ∀ w : GaussianInt, ‖Work.FIArea7.grossenChar chi k w‖ ≤ 1 :=
    fun w => Work.FIArea7.norm_grossenChar_le_one chi k hchi w
  have hlogc0 : (0 : ℝ) ≤ Real.log ((c : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlogu0 : (0 : ℝ) ≤ Real.log ((u : ℝ) + 2) := Real.log_nonneg (by linarith)
  -- the inner (over `p`) bound
  have hinner : ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
      (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
          ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
        ≤ 8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)
            * (Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2) := by
    intro q hq
    have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
    have hqne : c * q ≠ 0 := by
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1
      have : 0 < c * q := Nat.mul_pos (by omega) (by omega)
      omega
    have hcard : (((Work.FIArea7.smallCInner2EpsAux.pExcSet c u q).card : ℕ) : ℝ)
        ≤ Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2 := by
      have hsub : Work.FIArea7.smallCInner2EpsAux.pExcSet c u q ⊆ (c * q).primeFactors := by
        intro p hp
        rw [Work.FIArea7.smallCInner2EpsAux.pExcSet, Finset.mem_filter] at hp
        exact (Nat.mem_primeFactors_of_ne_zero hqne).mpr ⟨hp.2.1, hp.2.2⟩
      calc (((Work.FIArea7.smallCInner2EpsAux.pExcSet c u q).card : ℕ) : ℝ)
          ≤ (((c * q).primeFactors.card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2 :=
            card_primeFactors_cast_le_log (c * q)
    have hterm : ∀ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
        ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖
          ≤ 8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
      intro p hp
      rw [Work.FIArea7.smallCInner2EpsAux.pExcSet, Finset.mem_filter] at hp
      obtain ⟨_, hpp, _⟩ := hp
      have h1 : ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖
          ≤ 4 * (((c * (p * q)).divisors.card : ℕ) : ℝ) :=
        Work.FIArea7.normQuadEigenLe _ hψ _
      refine le_trans h1 ?_
      have h2 : (((c * (p * q)).divisors.card : ℕ) : ℝ)
          ≤ ((c.divisors.card : ℕ) : ℝ) * (((p * q).divisors.card : ℕ) : ℝ) := by
        exact_mod_cast tau_mul_le' c (p * q)
      have h3 : (((p * q).divisors.card : ℕ) : ℝ)
          ≤ ((p.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
        exact_mod_cast tau_mul_le' p q
      have hp2 : ((p.divisors.card : ℕ) : ℝ) ≤ 2 := by
        rw [Nat.Prime.divisors hpp, Finset.card_pair (Ne.symm hpp.ne_one)]
        norm_num
      have hA : (0 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      have hB : (0 : ℝ) ≤ ((q.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : 4 * (((c * (p * q)).divisors.card : ℕ) : ℝ)
          ≤ 4 * (((c.divisors.card : ℕ) : ℝ)
              * (((p.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ))) := by
        calc 4 * (((c * (p * q)).divisors.card : ℕ) : ℝ)
            ≤ 4 * (((c.divisors.card : ℕ) : ℝ) * (((p * q).divisors.card : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left h2 (by norm_num)
          _ ≤ 4 * (((c.divisors.card : ℕ) : ℝ)
                * (((p.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_left h3 hA
      have h5 : 4 * (((c.divisors.card : ℕ) : ℝ)
              * (((p.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)))
          ≤ 8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
        have hnn : (0 : ℝ) ≤ 4 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ) := by
          positivity
        have := mul_le_mul_of_nonneg_left hp2 hnn
        nlinarith [this]
      linarith [h4, h5]
    calc (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
            ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
        ≤ ∑ _p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
            (8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (((Work.FIArea7.smallCInner2EpsAux.pExcSet c u q).card : ℕ) : ℝ)
            * (8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2)
            * (8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hcard ?_
          have : (0 : ℝ) ≤ ((q.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
          positivity
      _ = 8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)
            * (Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2) := by ring
  -- the divisor sum over `q ≤ min u z`
  have hsub : Work.FIArea7.smallCInner2EpsAux.pOuterRange u z ⊆ Finset.Icc 1 (min u z) := by
    intro q hq
    have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
    rw [Finset.mem_Icc]
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1,
      le_min (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).2
        (Finset.mem_filter.mp hqmem).2⟩
  have hqsum : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        ((q.divisors.card : ℕ) : ℝ))
      ≤ Ct * (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2) :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => Nat.cast_nonneg _))
      (ht (min u z))
  have hminR : (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2)
      ≤ 2 * (z : ℝ) * Real.log ((u : ℝ) + 2) := by
    rcases le_total u z with h | h
    · have hmin : (min u z : ℕ) = u := min_eq_left h
      rw [hmin]
      have hu : (u : ℝ) ≤ (z : ℝ) := by exact_mod_cast h
      have h1 : ((u : ℝ) + 1) ≤ 2 * (z : ℝ) := by linarith
      have hnn : (0 : ℝ) ≤ Real.log ((u : ℝ) + 2) := Real.log_nonneg (by linarith)
      calc ((u : ℝ) + 1) * Real.log ((u : ℝ) + 2)
          ≤ (2 * (z : ℝ)) * Real.log ((u : ℝ) + 2) := mul_le_mul_of_nonneg_right h1 hnn
        _ = 2 * (z : ℝ) * Real.log ((u : ℝ) + 2) := by ring
    · have hmin : (min u z : ℕ) = z := min_eq_right h
      rw [hmin]
      have hzu : (z : ℝ) ≤ (u : ℝ) := by exact_mod_cast h
      have h1 : ((z : ℝ) + 1) ≤ 2 * (z : ℝ) := by linarith
      have hnn : (0 : ℝ) ≤ Real.log ((z : ℝ) + 2) := Real.log_nonneg (by linarith)
      have h2 : Real.log ((z : ℝ) + 2) ≤ Real.log ((u : ℝ) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      calc ((z : ℝ) + 1) * Real.log ((z : ℝ) + 2)
          ≤ (2 * (z : ℝ)) * Real.log ((z : ℝ) + 2) := mul_le_mul_of_nonneg_right h1 hnn
        _ ≤ (2 * (z : ℝ)) * Real.log ((u : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = 2 * (z : ℝ) * Real.log ((u : ℝ) + 2) := by ring
  have hlogcq : ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
      Real.log (((c * q : ℕ) : ℝ) + 2)
        ≤ Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2) := by
    intro q hq
    have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
    have hqu : q ≤ u := (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).2
    have hquR : (q : ℝ) ≤ (u : ℝ) := by exact_mod_cast hqu
    have h1 : ((c * q : ℕ) : ℝ) + 2 ≤ ((c : ℝ) + 2) * ((u : ℝ) + 2) := by
      push_cast
      nlinarith [hcR, hquR]
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (by positivity)] at h2
  -- assembly of the `q`-sum
  have hstep : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
          ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
            ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
      ≤ 8 * ((c.divisors.card : ℕ) : ℝ)
          * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
          * (Ct * (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2)) := by
    refine le_trans (Finset.sum_le_sum hinner) ?_
    have hpt : ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)
            * (Real.log (((c * q : ℕ) : ℝ) + 2) / Real.log 2)
        ≤ 8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)
            * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2) := by
      intro q hq
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · exact div_le_div_of_nonneg_right (hlogcq q hq) (le_of_lt hlog2)
      · have : (0 : ℝ) ≤ ((q.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
        positivity
    refine le_trans (Finset.sum_le_sum hpt) ?_
    have hsum_eq : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
          8 * ((c.divisors.card : ℕ) : ℝ) * ((q.divisors.card : ℕ) : ℝ)
            * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2))
        = 8 * ((c.divisors.card : ℕ) : ℝ)
            * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
            * (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
                ((q.divisors.card : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q hq => ?_)
      ring
    rw [hsum_eq]
    refine mul_le_mul_of_nonneg_left hqsum ?_
    have : (0 : ℝ) ≤ Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2) := by linarith
    positivity
  -- final arithmetic
  have hLu2 : Real.log 2 ≤ Real.log ((u : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hLc3 : Real.log 3 ≤ Real.log ((c : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hLupos : 0 < Real.log ((u : ℝ) + 2) := Real.log_pos (by linarith)
  have hLcpos : 0 < Real.log ((c : ℝ) + 2) := Real.log_pos (by linarith)
  have hsqu : (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) = (Real.log ((u : ℝ) + 2)) ^ 2 := Real.rpow_two _
  have hkey : (Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) * Real.log ((u : ℝ) + 2)
      ≤ (1 / Real.log 2 + 1 / Real.log 3) * Real.log ((c : ℝ) + 2)
          * (Real.log ((u : ℝ) + 2)) ^ 2 := by
    have hb1 : 1 / Real.log ((u : ℝ) + 2) ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le hlog2 hLu2
    have hb2 : 1 / Real.log ((c : ℝ) + 2) ≤ 1 / Real.log 3 :=
      one_div_le_one_div_of_le hlog3 hLc3
    have hid : (1 / Real.log ((u : ℝ) + 2) + 1 / Real.log ((c : ℝ) + 2))
          * (Real.log ((c : ℝ) + 2) * (Real.log ((u : ℝ) + 2)) ^ 2)
        = (Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) * Real.log ((u : ℝ) + 2) := by
      field_simp [ne_of_gt hLupos, ne_of_gt hLcpos] <;> ring
    rw [← hid]
    have h3 : 1 / Real.log ((u : ℝ) + 2) + 1 / Real.log ((c : ℝ) + 2)
        ≤ 1 / Real.log 2 + 1 / Real.log 3 := by linarith
    calc (1 / Real.log ((u : ℝ) + 2) + 1 / Real.log ((c : ℝ) + 2))
          * (Real.log ((c : ℝ) + 2) * (Real.log ((u : ℝ) + 2)) ^ 2)
        = ((1 / Real.log ((u : ℝ) + 2) + 1 / Real.log ((c : ℝ) + 2))
            * Real.log ((c : ℝ) + 2)) * (Real.log ((u : ℝ) + 2)) ^ 2 := by ring
      _ ≤ ((1 / Real.log 2 + 1 / Real.log 3) * Real.log ((c : ℝ) + 2))
            * (Real.log ((u : ℝ) + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (le_of_lt hLcpos))
            (by positivity)
      _ = (1 / Real.log 2 + 1 / Real.log 3) * Real.log ((c : ℝ) + 2)
            * (Real.log ((u : ℝ) + 2)) ^ 2 := by ring
  have step1 : 8 * ((c.divisors.card : ℕ) : ℝ)
        * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
        * (Ct * (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2))
      ≤ 8 * ((c.divisors.card : ℕ) : ℝ)
        * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
        * (Ct * (2 * (z : ℝ) * Real.log ((u : ℝ) + 2))) := by
    have hA : Ct * (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2)
        ≤ Ct * (2 * (z : ℝ) * Real.log ((u : ℝ) + 2)) := by
      calc Ct * (((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2)
          = Ct * ((((min u z : ℕ) : ℝ) + 1) * Real.log (((min u z : ℕ) : ℝ) + 2)) := by ring
        _ ≤ Ct * (2 * (z : ℝ) * Real.log ((u : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hminR (le_of_lt hCt)
    refine mul_le_mul_of_nonneg_left hA ?_
    have : (0 : ℝ) ≤ Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2) := by linarith
    positivity
  have step2 : 8 * ((c.divisors.card : ℕ) : ℝ)
        * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
        * (Ct * (2 * (z : ℝ) * Real.log ((u : ℝ) + 2)))
      ≤ (16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3) + 1)
          * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ 2 := by
    have heq : 8 * ((c.divisors.card : ℕ) : ℝ)
          * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) / Real.log 2)
          * (Ct * (2 * (z : ℝ) * Real.log ((u : ℝ) + 2)))
        = 16 * Ct / Real.log 2 * ((c.divisors.card : ℕ) : ℝ)
          * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) * Real.log ((u : ℝ) + 2))
          * (z : ℝ) := by ring
    rw [heq]
    have h1 : 16 * Ct / Real.log 2 * ((c.divisors.card : ℕ) : ℝ)
          * ((Real.log ((c : ℝ) + 2) + Real.log ((u : ℝ) + 2)) * Real.log ((u : ℝ) + 2))
          * (z : ℝ)
        ≤ 16 * Ct / Real.log 2 * ((c.divisors.card : ℕ) : ℝ)
          * ((1 / Real.log 2 + 1 / Real.log 3) * Real.log ((c : ℝ) + 2)
              * (Real.log ((u : ℝ) + 2)) ^ 2) * (z : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_ hznn
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hkey
    refine le_trans h1 ?_
    have heq2 : 16 * Ct / Real.log 2 * ((c.divisors.card : ℕ) : ℝ)
          * ((1 / Real.log 2 + 1 / Real.log 3) * Real.log ((c : ℝ) + 2)
              * (Real.log ((u : ℝ) + 2)) ^ 2) * (z : ℝ)
        = 16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3)
          * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2)
          * (Real.log ((u : ℝ) + 2)) ^ 2 * (z : ℝ) := by ring
    rw [heq2]
    calc 16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3)
          * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2)
          * (Real.log ((u : ℝ) + 2)) ^ 2 * (z : ℝ)
        = 16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3)
          * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ 2 := by ring
      _ ≤ (16 * Ct / Real.log 2 * (1 / Real.log 2 + 1 / Real.log 3) + 1)
          * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ hznn
          refine mul_le_mul_of_nonneg_right ?_ hlogc0
          refine mul_le_mul_of_nonneg_right ?_ hτc
          linarith
  refine le_trans hstep ?_
  rw [hsqu]
  exact le_trans step1 step2

end

end Work.FIArea7.smallCInner2EpsAux
