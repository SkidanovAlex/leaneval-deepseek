import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallAux
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallReduction
import Submission.Work.FIArea7.smallCInner2EpsAux.peelInnerW
import Submission.Work.FIArea7.smallCInner2EpsAux.peelCorrectionW

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `τ(c) ≤ τ(c·d)` (the map `e ↦ e·d` injects the divisors of `c` into those of `c·d`). -/
lemma card_divisors_le_mul_right (c d : ℕ) (hd : 1 ≤ d) :
    c.divisors.card ≤ (c * d).divisors.card := by
  by_cases h : c = 0
  · subst h
    simp
  have hdpos : 0 < d := hd
  have himg : (c.divisors.image (fun e => e * d)).card = c.divisors.card := by
    refine Finset.card_image_of_injOn (fun e1 _ e2 _ hh => ?_)
    exact Nat.eq_of_mul_eq_mul_right hdpos hh
  have hsub : c.divisors.image (fun e => e * d) ⊆ (c * d).divisors := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨e, he, rfl⟩ := hz
    rw [Nat.mem_divisors] at he ⊢
    exact ⟨mul_dvd_mul_right he.1 d, by positivity⟩
  calc c.divisors.card = (c.divisors.image (fun e => e * d)).card := himg.symm
    _ ≤ (c * d).divisors.card := Finset.card_le_card hsub

theorem peelSmallBound (h2psi : Work.FIArea7.Theorem2psi) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c d u z : ℕ)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ c → 1 ≤ d → 2 ≤ z → z ≤ u →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖Work.FIArea7.smallCInner2EpsAux.peelSmall2 u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ C * (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
                  + (((c.divisors.card : ℕ) : ℝ)) * Real.log ((c : ℝ) + 2) * (z : ℝ))
              * (Real.log ((u : ℝ) + 2)) ^ A * (K * |b - a| + 1) := by
  obtain ⟨C2, hC2, hinnerB⟩ :=
    Work.FIArea7.smallCInner2EpsAux.peelInnerW (Work.FIArea7.primeSumPsi h2psi)
  obtain ⟨C3, A3, hC3, hA3, hcorrB⟩ := Work.FIArea7.smallCInner2EpsAux.peelCorrectionW
  refine ⟨2 * C2 + C3 + 1, max A3 1, by positivity, lt_max_of_lt_left hA3, ?_⟩
  intro Pa chi k c d u z P a b K hc hd hz hzu hchi hmul hp1 hp2 hP ha hP0 hP1 hPsupp hPder
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg (deriv P 0)) (hPder 0)
  have hΔ0 : (0 : ℝ) ≤ K * |b - a| + 1 := by
    have := abs_nonneg (b - a); nlinarith
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by linarith
  have hzc : (0 : ℝ) ≤ (z : ℝ) := by linarith
  have huR : (1 : ℝ) ≤ (u : ℝ) := by
    have : 1 ≤ u := le_trans (by norm_num : 1 ≤ 2) (le_trans hz hzu)
    exact_mod_cast this
  have hτc : (0 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  have hτcd1 : (1 : ℝ) ≤ (((c * d).divisors.card : ℕ) : ℝ) := by
    have h1 : 1 ≤ (c * d).divisors.card := by
      refine Finset.card_pos.mpr ⟨1, ?_⟩
      rw [Nat.mem_divisors]
      exact ⟨one_dvd _, by positivity⟩
    exact_mod_cast h1
  have hτcdc : ((c.divisors.card : ℕ) : ℝ) ≤ (((c * d).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast card_divisors_le_mul_right c d hd
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| + 1 := by have := abs_nonneg (k : ℝ); linarith
  have hΔ1 : (1 : ℝ) ≤ K * |b - a| + 1 := by
    have := abs_nonneg (b - a); nlinarith
  -- `log(u+2) ≥ 1`
  have hlogu : (1 : ℝ) ≤ Real.log ((u : ℝ) + 2) := by
    have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
      le_of_lt ((Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three)
    refine le_trans hlog3 (Real.log_le_log (by norm_num) ?_)
    have : (3 : ℕ) ≤ u + 2 := by omega
    exact_mod_cast this
  have hlogu0 : (0 : ℝ) ≤ Real.log ((u : ℝ) + 2) := by linarith
  -- the double sum
  rw [Work.FIArea7.smallCInner2EpsAux.peelSmallReduction Pa chi k c u z P]
  have hmain : ‖∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          (if p * q ≤ u then
            Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
              * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
              * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
            else 0)‖
      ≤ (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1))
        + (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
              ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖) := by
    calc ‖∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
          ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
            (if p * q ≤ u then
              Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
              else 0)‖
        ≤ ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            ‖∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
              (if p * q ≤ u then
                Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                  * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                  * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                  * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
                else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            (2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
                * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
              + ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
                  ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖) :=
          Finset.sum_le_sum (fun q hq =>
            hinnerB chi k c d u z Pa P a b K hc hd hz hchi hmul hp1 hp2 hP ha hP0 hP1 hPsupp
              hPder q hq)
      _ = (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1))
          + (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
              ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
                ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖) :=
          Finset.sum_add_distrib
  -- the divisor sum `Σ_q q^{1/77} ≤ z²`
  have hqsub : Work.FIArea7.smallCInner2EpsAux.pOuterRange u z ⊆ Finset.Icc 1 z := by
    intro q hq
    have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
    rw [Finset.mem_Icc]
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1,
      (Finset.mem_filter.mp hqmem).2⟩
  have hqpow : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        (q : ℝ) ^ ((1 : ℝ) / 77)) ≤ (z : ℝ) ^ 2 := by
    calc (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            (q : ℝ) ^ ((1 : ℝ) / 77))
        ≤ ∑ q ∈ Finset.Icc 1 z, (q : ℝ) ^ ((1 : ℝ) / 77) :=
          Finset.sum_le_sum_of_subset_of_nonneg hqsub
            (fun q _ _ => Real.rpow_nonneg (Nat.cast_nonneg q) _)
      _ ≤ ∑ _q ∈ Finset.Icc 1 z, (z : ℝ) ^ ((1 : ℝ) / 77) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          exact Real.rpow_le_rpow (Nat.cast_nonneg q)
            (by exact_mod_cast (Finset.mem_Icc.mp hq).2) (by norm_num)
      _ = (z : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 77) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp
      _ = (z : ℝ) ^ ((78 : ℝ) / 77) := by
          have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
          calc (z : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 77)
              = (z : ℝ) ^ (1 : ℝ) * (z : ℝ) ^ ((1 : ℝ) / 77) := by rw [Real.rpow_one]
            _ = (z : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 77) :=
                (Real.rpow_add hzpos (1 : ℝ) ((1 : ℝ) / 77)).symm
            _ = (z : ℝ) ^ ((78 : ℝ) / 77) := by norm_num
      _ ≤ (z : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast (z : ℝ) 2]
          exact Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  -- the main `q`-sum
  have hqmain : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1))
      ≤ 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
          * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2) := by
    have hpt : ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
            * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
          ≤ 2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
            * ((u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77))
            * (K * |b - a| + 1) := by
      intro q hq
      have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1
      have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
      have hkey : (q : ℝ) * (((u / q : ℕ)) : ℝ) ^ ((76 : ℝ) / 77)
          ≤ (u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77) := by
        have h1 : (((u / q : ℕ)) : ℝ) ^ ((76 : ℝ) / 77)
            ≤ ((u : ℝ) / (q : ℝ)) ^ ((76 : ℝ) / 77) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (by norm_num)
        have h2 : ((u : ℝ) / (q : ℝ)) ^ ((76 : ℝ) / 77)
            = (u : ℝ) ^ ((76 : ℝ) / 77) / (q : ℝ) ^ ((76 : ℝ) / 77) :=
          Real.div_rpow (Nat.cast_nonneg u) (le_of_lt hqpos) _
        have h3 : (q : ℝ) / (q : ℝ) ^ ((76 : ℝ) / 77) = (q : ℝ) ^ ((1 : ℝ) / 77) := by
          have hs := Real.rpow_sub hqpos (1 : ℝ) ((76 : ℝ) / 77)
          rw [Real.rpow_one] at hs
          rw [← hs, show (1 : ℝ) - 76 / 77 = 1 / 77 by norm_num]
        calc (q : ℝ) * (((u / q : ℕ)) : ℝ) ^ ((76 : ℝ) / 77)
            ≤ (q : ℝ) * ((u : ℝ) / (q : ℝ)) ^ ((76 : ℝ) / 77) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt hqpos)
          _ = (u : ℝ) ^ ((76 : ℝ) / 77) * ((q : ℝ) / (q : ℝ) ^ ((76 : ℝ) / 77)) := by
              rw [h2]; ring
          _ = (u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77) := by rw [h3]
      calc 2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
            * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
          = (2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1))
              * ((q : ℝ) * (((u / q : ℕ)) : ℝ) ^ ((76 : ℝ) / 77))
              * (K * |b - a| + 1) := by push_cast; ring
        _ ≤ (2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1))
              * ((u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77))
              * (K * |b - a| + 1) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey ?_) hΔ0
            positivity
        _ = 2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77))
              * (K * |b - a| + 1) := by ring
    exact le_trans (Finset.sum_le_sum hpt) (by
      calc (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u : ℝ) ^ ((76 : ℝ) / 77) * (q : ℝ) ^ ((1 : ℝ) / 77))
              * (K * |b - a| + 1))
          = (2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (u : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1))
            * (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
                (q : ℝ) ^ ((1 : ℝ) / 77)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun q hq => ?_)
            ring
        _ ≤ (2 * C2 * (c : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (u : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1)) * (z : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_left hqpow ?_
            positivity
        _ = 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2) := by ring)
  have hcorr : (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
          ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
      ≤ C3 * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ A3 :=
    hcorrB chi k c u z hc hz hchi
  -- the final absorption
  have hA3le : A3 ≤ max A3 1 := le_max_left _ _
  have hLuA3 : (Real.log ((u : ℝ) + 2)) ^ A3
      ≤ (Real.log ((u : ℝ) + 2)) ^ (max A3 1) :=
    Real.rpow_le_rpow_of_exponent_le hlogu hA3le
  have hW2 : (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
      ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
          * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
    have h1 : (1 : ℝ) ≤ (((c * d).divisors.card : ℕ) : ℝ)
        * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) := by
      have h2 : (1 : ℝ) ≤ (Real.log ((u : ℝ) + 2)) ^ (max A3 1) :=
        Real.one_le_rpow hlogu (le_trans (le_of_lt hA3) (le_max_left A3 1))
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (((c * d).divisors.card : ℕ) : ℝ)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) :=
            mul_le_mul hτcd1 h2 (by norm_num) (by linarith)
    calc (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
        = ((d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)) * 1 := by ring
      _ ≤ ((d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1))
            * ((((c * d).divisors.card : ℕ) : ℝ)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by ring
  have hW3 : (Real.log ((u : ℝ) + 2)) ^ A3
      ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
          * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
        * (K * |b - a| + 1) := by
      have h2 : (1 : ℝ) ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1) := by
        have := mul_le_mul (mul_le_mul hdR hτcd1 (by norm_num) (by linarith)) hk1
          (by norm_num) (by positivity)
        simpa [mul_assoc] using this
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1))
              * (K * |b - a| + 1) := mul_le_mul h2 hΔ1 (by norm_num) (by linarith)
    calc (Real.log ((u : ℝ) + 2)) ^ A3
        = (Real.log ((u : ℝ) + 2)) ^ A3 * 1 := by ring
      _ ≤ (Real.log ((u : ℝ) + 2)) ^ A3
            * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (K * |b - a| + 1)) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hlogu0 _)
      _ = (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * (Real.log ((u : ℝ) + 2)) ^ A3 * (K * |b - a| + 1) := by ring
      _ ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hΔ0
          exact mul_le_mul_of_nonneg_left hLuA3 (by positivity)
  have hfinal : 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
        * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
      + C3 * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
        * (Real.log ((u : ℝ) + 2)) ^ A3
      ≤ (2 * C2 + C3 + 1) * (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
          * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
              + ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
          * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
    have hX0 : (0 : ℝ) ≤ (c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ (u : ℝ) ^ ((76 : ℝ) / 77) := Real.rpow_nonneg (by linarith) _
      positivity
    have hY0 : (0 : ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ) := by
      have : (0 : ℝ) ≤ Real.log ((c : ℝ) + 2) := Real.log_nonneg (by linarith)
      positivity
    have hC2n : (0 : ℝ) ≤ 2 * C2 := by linarith [hC2]
    have hC3n : (0 : ℝ) ≤ C3 := le_of_lt hC3
    have hterm1 : 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
          * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
        ≤ 2 * C2 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2) := by
      have hh : (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1) ≤
          (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := hW2
      calc 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
          = 2 * C2 * ((d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1))
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2) := by ring
        _ ≤ 2 * C2 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC2n) hX0
    have hterm2 : C3 * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ A3
        ≤ C3 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)) := by
      calc C3 * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
            * (Real.log ((u : ℝ) + 2)) ^ A3
          = C3 * (Real.log ((u : ℝ) + 2)) ^ A3
              * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)) := by ring
        _ ≤ C3 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
              * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW3 hC3n) hY0
    have hsum : 2 * C2 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
          + C3 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
        ≤ (2 * C2 + C3 + 1) * (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
                + ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
            * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
      have hW0 : (0 : ℝ) ≤ (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
          * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by
        have : (0 : ℝ) ≤ (Real.log ((u : ℝ) + 2)) ^ (max A3 1) := Real.rpow_nonneg hlogu0 _
        positivity
      calc 2 * C2 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
          + C3 * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
            * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
          = (2 * C2) * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2))
            + C3 * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
              * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
              * (((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))) := by ring
        _ ≤ (2 * C2 + C3 + 1) * ((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ)
              * (|(k : ℝ)| + 1) * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1))
              * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
                + ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)) := by
            have hA : 2 * C2 * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1)) * (((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)))
                ≤ (2 * C2 + C3 + 1) * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1)) * (((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2))) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            have hB : C3 * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1)) * ((((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))))
                ≤ (2 * C2 + C3 + 1) * (((d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1) * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1)) * ((((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)))) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            nlinarith [hA, hB]
        _ = (2 * C2 + C3 + 1) * (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
            * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
                + ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
            * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := by ring
    linarith [hterm1, hterm2, hsum]
  calc ‖∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          (if p * q ≤ u then
            Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
              * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
              * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
            else 0)‖
      ≤ (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            2 * C2 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1))
        + (∑ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
            ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
              ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖) := hmain
    _ ≤ 2 * C2 * (d : ℝ) * (|(k : ℝ)| + 1) * (K * |b - a| + 1)
          * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2)
        + C3 * ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ)
          * (Real.log ((u : ℝ) + 2)) ^ A3 := add_le_add hqmain hcorr
    _ ≤ (2 * C2 + C3 + 1) * (d : ℝ) * (((c * d).divisors.card : ℕ) : ℝ) * (|(k : ℝ)| + 1)
          * ((c : ℝ) * (u : ℝ) ^ ((76 : ℝ) / 77) * (z : ℝ) ^ 2
              + ((c.divisors.card : ℕ) : ℝ) * Real.log ((c : ℝ) + 2) * (z : ℝ))
          * (Real.log ((u : ℝ) + 2)) ^ (max A3 1) * (K * |b - a| + 1) := hfinal

end

end Work.FIArea7.smallCInner2EpsAux
