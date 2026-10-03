/-
# `peelInnerW` — bound for one fixed `q` of the peeled small part

For `q ≤ z` and `p` a prime `> z`, `μ(pq) = -μ(q)` and the sieve indicators split, so the inner
sum over `p` of `μ(pq)·nspInd(pq)·1[(c,pq)=1]·P(c·pq)·λ(c·pq)` equals the `q`-coefficient times a
sum of `P(cq·p)·λ(cq·p)` over the primes `max(z,Pz) < p ≤ u/q` that do not divide `c·q`.  Splitting
off the (at most `ω(cq)`) prime divisors of `c·q` and applying the shifted prime-sum estimate to
the rest gives the stated bound.
-/
import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.peelSmallAux

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The shifted (thresholded) prime-sum estimate with a smooth weight.**  From the unshifted
estimate for `Σ_{p ≤ L} P(c₀p)λ(c₀p)` deduce the same for `Σ_{t < p ≤ L}`: the two differ by the
sum over `p ≤ min(L,t)`, which is smaller. -/
lemma primeSumWeightedShifted
    {chi : GaussianInt → ℂ} {k : ℤ} {C1 : ℝ} (hC1 : 0 < C1)
    (hprim : ∀ (d c0 L : ℕ) (P : ℝ → ℝ) (a b K : ℝ), 1 ≤ d → 1 ≤ c0 → 1 ≤ L →
      (∀ z', ‖chi z'‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
      (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
      (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
      ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
      (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
      ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
          ((P ((c0 : ℝ) * (p : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * p)‖
        ≤ C1 * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
            * (K * |b - a| + 1))
    {d : ℕ} (hd : 1 ≤ d)
    (hchi : ∀ z', ‖chi z'‖ ≤ 1)
    (hmul : ∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2)
    (hp1 : ∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩)
    (hp2 : ∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩)
    (P : ℝ → ℝ) (a b K : ℝ) (hP : ContDiff ℝ 1 P) (ha : 0 ≤ a)
    (hP0 : ∀ u, 0 ≤ P u) (hP1 : ∀ u, P u ≤ 1)
    (hPsupp : ∀ u, P u ≠ 0 → a < u ∧ u ≤ b) (hPder : ∀ u, |deriv P u| ≤ K)
    (m L t : ℕ) (hm : 1 ≤ m) :
    ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime ∧ t < p),
        ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p)‖
      ≤ 2 * C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
          * (K * |b - a| + 1) := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg (deriv P 0)) (hPder 0)
  have hΔ : 0 ≤ K * |b - a| + 1 := by
    have h := abs_nonneg (b - a); nlinarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hLr : (0 : ℝ) ≤ (L : ℝ) ^ ((76 : ℝ) / 77) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hk0 : (0 : ℝ) ≤ |(k : ℝ)| + 1 := by positivity
  have hAnn : (0 : ℝ) ≤ C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) hm0) hd0) hk0
  have hmain : ∀ X : ℕ, X ≤ L →
      ‖∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime),
          ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p)‖
        ≤ C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
            * (K * |b - a| + 1) := by
    intro X hX
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · subst h0
      have hempty : (Finset.Icc 1 0 : Finset ℕ) = ∅ := Finset.Icc_eq_empty_of_lt (by norm_num)
      rw [hempty, Finset.filter_empty, Finset.sum_empty, norm_zero]
      exact mul_nonneg (mul_nonneg hAnn hLr) hΔ
    · have h := hprim d m X P a b K hd hm h0 hchi hmul hp1 hp2 hP ha hP0 hP1 hPsupp hPder
      refine le_trans h ?_
      have hXL : (X : ℝ) ≤ (L : ℝ) := by exact_mod_cast hX
      have hpow : (X : ℝ) ^ ((76 : ℝ) / 77) ≤ (L : ℝ) ^ ((76 : ℝ) / 77) :=
        Real.rpow_le_rpow (Nat.cast_nonneg X) hXL (by norm_num)
      have hstep : C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (X : ℝ) ^ ((76 : ℝ) / 77)
          ≤ C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77) :=
        mul_le_mul_of_nonneg_left hpow hAnn
      calc C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (X : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1)
          = (C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (X : ℝ) ^ ((76 : ℝ) / 77))
              * (K * |b - a| + 1) := by ring
        _ ≤ (C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77))
              * (K * |b - a| + 1) := mul_le_mul_of_nonneg_right hstep hΔ
        _ = C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1) := by ring
  have hsub : (Finset.Icc 1 (min L t)).filter (fun p => p.Prime)
      ⊆ (Finset.Icc 1 L).filter (fun p => p.Prime) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 (min_le_left _ _)⟩, hp.2⟩
  have hset : (Finset.Icc 1 L).filter (fun p => p.Prime ∧ t < p)
      = (Finset.Icc 1 L).filter (fun p => p.Prime)
          \ (Finset.Icc 1 (min L t)).filter (fun p => p.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hpp, htp⟩
      refine ⟨⟨⟨h1, h2⟩, hpp⟩, fun hc => ?_⟩
      exact (not_le.mpr htp) (le_trans hc.1.2 (min_le_right L t))
    · rintro ⟨⟨⟨h1, h2⟩, hpp⟩, hnot⟩
      refine ⟨⟨h1, h2⟩, hpp, ?_⟩
      by_contra hle
      exact hnot ⟨⟨h1, le_min h2 (not_lt.mp hle)⟩, hpp⟩
  have hdiff : (∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime ∧ t < p),
        ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p))
      = (∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
          ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p))
        - (∑ p ∈ (Finset.Icc 1 (min L t)).filter (fun p => p.Prime),
            ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p)) := by
    rw [hset]
    exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub (f := fun (p : ℕ) =>
      ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ) * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p)))
  calc ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime ∧ t < p),
        ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p)‖
      = ‖(∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
            ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p))
          - (∑ p ∈ (Finset.Icc 1 (min L t)).filter (fun p => p.Prime),
            ((P ((m : ℝ) * (p : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (m * p))‖ := by rw [hdiff]
    _ ≤ (C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
            * (K * |b - a| + 1))
          + (C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
            * (K * |b - a| + 1)) := by
        refine le_trans (norm_sub_le _ _) ?_
        exact add_le_add (hmain L le_rfl) (hmain (min L t) (min_le_left _ _))
    _ = 2 * C1 * (m : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
          * (K * |b - a| + 1) := by ring

/-- **The termwise rewrite of the peeled summand, with the smooth weight.** -/
lemma peelTermW {chi : GaussianInt → ℂ} {k : ℤ} {c u z q p : ℕ} {Pa : Work.FITop.Params}
    {P : ℝ → ℝ} (hpp : p.Prime) (hzp : z < p) :
    (if p * q ≤ u then
        Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
          * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
          * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
      else 0)
    = (if p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q then
        (-((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
            * (if Nat.Coprime c q then (1 : ℂ) else 0))
          * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
      else 0) := by
  by_cases hpq : p * q ≤ u
  · by_cases hPz : Pa.Pz < p
    · by_cases hdvd : p ∣ c * q
      · rw [if_pos hpq]
        rw [if_neg (show ¬ (p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q) from fun h => h.2.2 hdvd)]
        rcases (hpp.dvd_mul).mp hdvd with hc | hq
        · have hnc : ¬ Nat.Coprime c (p * q) := by
            intro hcon
            have h1 : p ∣ Nat.gcd c (p * q) := Nat.dvd_gcd hc (dvd_mul_right p q)
            rw [hcon.gcd_eq_one] at h1
            exact hpp.not_dvd_one h1
          rw [if_neg hnc]; ring
        · have h0 : ArithmeticFunction.moebius (p * q) = 0 := moebius_prime_mul_of_dvd hpp hq
          rw [h0]; ring
      · rw [if_pos hpq]
        rw [if_pos (show (p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q) from ⟨hpq, hPz, hdvd⟩)]
        have hfac : Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
              * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
            = -((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
                * (if Nat.Coprime c q then (1 : ℂ) else 0) := by
          calc Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
              = (ArithmeticFunction.moebius (p * q) : ℂ) * Work.FIArea7.nspInd Pa (p * q)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0) := by ring
            _ = -((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
                * (if Nat.Coprime c q then (1 : ℂ) else 0) := peelFactor_eq hpp hPz hdvd
        rw [hfac]
    · rw [if_pos hpq]
      rw [if_neg (show ¬ (p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q) from fun h => hPz h.2.1)]
      have hnsp : Work.FIArea7.nspInd Pa (p * q) = 0 := by
        unfold Work.FIArea7.nspInd Work.FIArea7.NoSmallPrimesNat
        rw [if_neg]
        intro hcon
        exact (hcon p hpp (not_lt.mp hPz)) (dvd_mul_right p q)
      rw [hnsp]; ring
  · rw [if_neg hpq]
    rw [if_neg (show ¬ (p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q) from fun h => hpq h.1)]

/-- **The bound for one fixed `q`.** -/
theorem peelInnerW
    (hprime : ∃ C : ℝ, 0 < C ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (d c0 L : ℕ) (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ d → 1 ≤ c0 → 1 ≤ L →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖∑ p ∈ (Finset.Icc 1 L).filter (fun p => p.Prime),
            ((P ((c0 : ℝ) * (p : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * p)‖
          ≤ C * (c0 : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1) * (L : ℝ) ^ ((76 : ℝ) / 77)
              * (K * |b - a| + 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (c d u z : ℕ) (Pa : Work.FITop.Params)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ c → 1 ≤ d → 2 ≤ z →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ (a' b' : ℤ), chi (⟨a' + 4 * (d : ℤ), b'⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        (∀ (a' b' : ℤ), chi (⟨a', b' + 4 * (d : ℤ)⟩ : GaussianInt) = chi ⟨a', b'⟩) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ∀ q ∈ Work.FIArea7.smallCInner2EpsAux.pOuterRange u z,
        ‖∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
            (if p * q ≤ u then
              Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
                * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
                * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
              else 0)‖
          ≤ 2 * C * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
              * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
            + ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
                ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
  obtain ⟨C1, hC1, hprim⟩ := hprime
  refine ⟨C1, hC1, ?_⟩
  intro chi k c d u z Pa P a b K hc hd hz hchi hmul hp1 hp2 hP ha hP0 hP1 hPsupp hPder q hq
  have hqmem : q ∈ (Finset.Icc 1 u).filter (fun q => q ≤ z) := hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hqmem).1).1
  have hqz : q ≤ z := (Finset.mem_filter.mp hqmem).2
  have hqpos : 0 < q := hq1
  have hcq1 : 1 ≤ c * q := Nat.mul_pos (by omega) hqpos
  set α : ℂ := -((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
      * (if Nat.Coprime c q then (1 : ℂ) else 0) with hα
  have hα1 : ‖α‖ ≤ 1 := by
    have h1 : ‖-((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
      rw [norm_neg, Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have h2 : ‖Work.FIArea7.nspInd Pa q‖ ≤ 1 := Work.FIArea7.norm_nspInd_le_one Pa q
    have h3 : ‖(if Nat.Coprime c q then (1 : ℂ) else 0)‖ ≤ 1 := by
      by_cases h : Nat.Coprime c q
      · rw [if_pos h]; norm_num
      · rw [if_neg h]; norm_num
    rw [hα]
    calc ‖-((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
            * (if Nat.Coprime c q then (1 : ℂ) else 0)‖
        = ‖-((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ * ‖Work.FIArea7.nspInd Pa q‖
            * ‖(if Nat.Coprime c q then (1 : ℂ) else 0)‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  -- step 1: termwise rewrite
  have hstep1 : (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
        (if p * q ≤ u then
          Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
            * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
            * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
          else 0))
      = ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          (if p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q then
            α * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
          else 0) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp' : p ∈ (Finset.Icc 1 u).filter (fun p => p.Prime ∧ z < p) := hp
    obtain ⟨hpp, hzp⟩ := (Finset.mem_filter.mp hp').2
    exact peelTermW (chi := chi) (k := k) (Pa := Pa) (P := P) (c := c) (u := u) (z := z)
      (q := q) (p := p) hpp hzp
  -- step 2: factor out the `q`-coefficient
  have hstep2 : (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
          (if p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q then
            α * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
          else 0))
      = α * ∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z).filter
            (fun p => p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q),
          ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    by_cases hC : p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q
    · simp only [if_pos hC]; ring
    · simp only [if_neg hC]
  -- step 3: reindex to `p ≤ u/q`
  have hstep3 : (Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z).filter
        (fun p => p * q ≤ u ∧ Pa.Pz < p ∧ ¬ p ∣ c * q)
      = (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter (fun p => ¬ p ∣ c * q) := by
    ext p
    simp only [Work.FIArea7.smallCInner2EpsAux.pPrimeSet,
      Work.FIArea7.smallCInner2EpsAux.pRangeSet, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6, h7⟩
      exact ⟨⟨⟨h1, (Nat.le_div_iff_mul_le hqpos).mpr h5⟩, h3, max_lt_iff.mpr ⟨h4, h6⟩⟩, h7⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      obtain ⟨h4a, h4b⟩ := max_lt_iff.mp h4
      exact ⟨⟨⟨h1, le_trans h2 (Nat.div_le_self u q)⟩, h3, h4a⟩,
        (Nat.le_div_iff_mul_le hqpos).mp h2, h4b, h5⟩
  -- step 4: the pruned sum
  have hprune : ‖∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
        (fun p => ¬ p ∣ c * q),
        ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖
      ≤ 2 * C1 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
        + ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
            ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
    have hAB : (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
        (fun p => ¬ p ∣ c * q) ⊆ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q :=
      Finset.filter_subset _ _
    have hBAE : Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q
          \ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter (fun p => ¬ p ∣ c * q)
        ⊆ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q := by
      intro p hp
      have hpB : p ∈ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q :=
        (Finset.mem_sdiff.mp hp).1
      have hpA : p ∉ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
          (fun p => ¬ p ∣ c * q) := (Finset.mem_sdiff.mp hp).2
      have hpB' : p ∈ (Finset.Icc 1 (u / q)).filter (fun p => p.Prime ∧ max z Pa.Pz < p) := hpB
      rw [Finset.mem_filter] at hpB'
      have hdvd : p ∣ c * q := by
        by_contra hnd
        exact hpA (Finset.mem_filter.mpr ⟨hpB, hnd⟩)
      rw [Work.FIArea7.smallCInner2EpsAux.pExcSet, Finset.mem_filter]
      exact ⟨hpB'.1, hpB'.2.1, hdvd⟩
    have hsplit : (∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
          (fun p => ¬ p ∣ c * q),
          ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q)))
        = (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q,
            ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q)))
          - (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q
                \ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
                    (fun p => ¬ p ∣ c * q),
              ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))) := by
      have h := Finset.sum_sdiff hAB
        (f := fun p => ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q)))
      refine eq_sub_iff_add_eq.mpr ?_
      rw [add_comm]
      exact h
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · have hshift := primeSumWeightedShifted (chi := chi) (k := k) hC1 (hprim chi k)
        hd hchi hmul hp1 hp2 P a b K hP ha hP0 hP1 hPsupp hPder (c * q) (u / q) (max z Pa.Pz)
        (by simpa using hcq1)
      have hcongr : (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q,
            ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q)))
          = ∑ p ∈ (Finset.Icc 1 (u / q)).filter (fun p => p.Prime ∧ max z Pa.Pz < p),
              ((P (((c * q : ℕ) : ℝ) * (p : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) ((c * q) * p) := by
        rw [Work.FIArea7.smallCInner2EpsAux.pRangeSet]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have h1 : ((c : ℝ) * ((p * q : ℕ) : ℝ)) = (((c * q : ℕ) : ℝ) * (p : ℝ)) := by
          push_cast; ring
        have h2 : c * (p * q) = (c * q) * p := by ring
        rw [h1, h2]
      rw [hcongr]
      exact hshift
    · refine le_trans (norm_sum_le _ _) ?_
      calc (∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q
              \ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
                  (fun p => ¬ p ∣ c * q),
            ‖((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖)
          ≤ ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
              ‖((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hBAE (fun p _ _ => norm_nonneg _)
        _ ≤ ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
              ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            rw [norm_mul]
            calc ‖((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)‖
                  * ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖
                ≤ 1 * ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
                  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP0 _)]
                  exact hP1 _
              _ = ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ :=
                  one_mul _
  calc ‖∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pPrimeSet u z,
        (if p * q ≤ u then
          Work.FIArea7.nspInd Pa (p * q) * (ArithmeticFunction.moebius (p * q) : ℂ)
            * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
            * ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))
          else 0)‖
      = ‖α * ∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
            (fun p => ¬ p ∣ c * q),
          ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
        rw [hstep1, hstep2, hstep3]
    _ ≤ 1 * ‖∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
            (fun p => ¬ p ∣ c * q),
          ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hα1 (norm_nonneg _)
    _ = ‖∑ p ∈ (Work.FIArea7.smallCInner2EpsAux.pRangeSet u z Pa.Pz q).filter
            (fun p => ¬ p ∣ c * q),
          ((P ((c : ℝ) * ((p * q : ℕ) : ℝ)) : ℝ) : ℂ)
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := one_mul _
    _ ≤ 2 * C1 * ((c * q : ℕ) : ℝ) * (d : ℝ) * (|(k : ℝ)| + 1)
          * ((u / q : ℕ) : ℝ) ^ ((76 : ℝ) / 77) * (K * |b - a| + 1)
        + ∑ p ∈ Work.FIArea7.smallCInner2EpsAux.pExcSet c u q,
            ‖Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * (p * q))‖ := hprune

end

end Work.FIArea7.smallCInner2EpsAux
