/-
  Companion paper, §9: the estimate (9.11) `E₁ ≪ A(x)L^{-1}(log x)^{-2^17}`.

  Recall (companion §9, after (9.10))

      `E = ∑♭_ν ∑♭_{d ≤ D} |r_{[ν²,d]}(t)|`,

  split into the part `E₁` with `ν ≤ L` and the part `E₂` with `ν > L`.  Here we prove the
  `E₁`-part: every product `[ν²,d]` with `ν, d` squarefree is *cubefree*, and every `k` has at
  most `τ(k)` representations `k = [ν²,d]` with `ν, d` squarefree
  (commons: `Commons.NumberTheory.Lcm.card_lcm_sq_eq_le_tau`), whence

      `E₁ = ∑_{ν ≤ L} ∑♭_{d ≤ D} |r_{[ν²,d]}(t)| ≤ ∑_{k ≤ D L², k cubefree} τ(k)·|r_k(t)|`,

  which is the companion's `(R′₃)` — so the hypothesis of `E1_le` below is exactly the
  conclusion of `(R₃) ⟹ (R′₃)`.
-/
import Mathlib
import Submission.ASP.S9a
import Submission.Commons.NumberTheory.Lcm.card_lcm_sq_eq_le_tau

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- `k` is cubefree: every prime occurs in `k` with exponent at most two. -/
abbrev CubefreeN (k : ℕ) : Prop := ∀ p ∈ k.primeFactors, k.factorization p ≤ 2

/-- `[ν²,d]` is cubefree whenever `ν` and `d` are squarefree. -/
lemma cubefreeN_lcm_sq {ν d : ℕ} (hν : Squarefree ν) (hd : Squarefree d) :
    CubefreeN (Nat.lcm (ν ^ 2) d) := by
  intro p hp
  have hν0 : ν ≠ 0 := hν.ne_zero
  have hd0 : d ≠ 0 := hd.ne_zero
  have h2 : ν ^ 2 ≠ 0 := pow_ne_zero _ hν0
  have hle : (Nat.lcm (ν ^ 2) d).factorization p
      = max ((ν ^ 2).factorization p) (d.factorization p) := by
    rw [Nat.factorization_lcm h2 hd0]
    rfl
  have hνle : ν.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hν0).mp hν p
  have hdle : d.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hd0).mp hd p
  have hpow : (ν ^ 2).factorization p = 2 * ν.factorization p := by
    rw [Nat.factorization_pow]
    simp
  rw [hle, hpow]
  omega

/-- **Companion §9, (9.11)**: the part `E₁` of `E` (the terms with `ν ≤ L`) is bounded by the
`(R′₃)`-type sum over cubefree moduli. -/
theorem E1_le (r : ℕ → ℕ → ℝ) (t D L : ℕ) {X : ℝ}
    (hR3 : (∑ k ∈ (Finset.Icc 1 (D * L ^ 2)).filter (fun k => CubefreeN k),
        (k.divisors.card : ℝ) * |r k t|) ≤ X) :
    (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|) ≤ X := by
  classical
  set S : Finset (ℕ × ℕ) := ((Finset.Icc 1 L).filter Squarefree) ×ˢ
    ((Finset.Icc 1 D).filter Squarefree) with hS
  have hL : (∑ ν ∈ (Finset.Icc 1 L).filter Squarefree,
        ∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |r (Nat.lcm (ν ^ 2) d) t|)
      = ∑ p ∈ S, |r (Nat.lcm (p.1 ^ 2) p.2) t| := by
    rw [hS, Finset.sum_product]
  rw [hL]
  -- the fibre decomposition over `k = [ν²,d]`
  have hmaps : ∀ p ∈ S, Nat.lcm (p.1 ^ 2) p.2 ∈
      (Finset.Icc 1 (D * L ^ 2)).filter (fun k => CubefreeN k) := by
    intro p hp
    rw [hS, Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hsf1 : Squarefree p.1 := (Finset.mem_filter.mp hp1).2
    have hsf2 : Squarefree p.2 := (Finset.mem_filter.mp hp2).2
    have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).1
    have h1L : p.1 ≤ L := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).2
    have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).1
    have h2D : p.2 ≤ D := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, cubefreeN_lcm_sq hsf1 hsf2⟩
    · have hp1sq : 1 ≤ p.1 ^ 2 := by nlinarith
      exact le_trans hp1sq (Nat.le_of_dvd (by positivity)
        (Nat.dvd_lcm_left (p.1 ^ 2) p.2))
    · calc Nat.lcm (p.1 ^ 2) p.2 ≤ p.1 ^ 2 * p.2 :=
          Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
        _ ≤ L ^ 2 * D := Nat.mul_le_mul (Nat.pow_le_pow_left h1L 2) h2D
        _ = D * L ^ 2 := by ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => |r (Nat.lcm (p.1 ^ 2) p.2) t|)]
  refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) hR3
  have hcongr : (∑ p ∈ S.filter (fun p => Nat.lcm (p.1 ^ 2) p.2 = k),
        |r (Nat.lcm (p.1 ^ 2) p.2) t|)
      = ∑ p ∈ S.filter (fun p => Nat.lcm (p.1 ^ 2) p.2 = k), |r k t| := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(Finset.mem_filter.mp hp).2]
  rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.filter (fun p => Nat.lcm (p.1 ^ 2) p.2 = k)).card ≤ k.divisors.card := by
    rcases eq_or_ne k 0 with rfl | hk
    · have hempty : S.filter (fun p => Nat.lcm (p.1 ^ 2) p.2 = 0) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Finset.mem_filter, hS, Finset.mem_product] at hp
        obtain ⟨⟨hp1, hp2⟩, hlcm⟩ := hp
        have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).1
        have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).1
        have hpos : 0 < Nat.lcm (p.1 ^ 2) p.2 := by positivity
        omega
      rw [hempty]
      simp
    · refine le_trans (Finset.card_le_card ?_)
        (Commons.NumberTheory.Lcm.card_lcm_sq_eq_le_tau k)
      intro p hp
      rw [Finset.mem_filter, hS, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hpk⟩ := hp
      have hsf1 : Squarefree p.1 := (Finset.mem_filter.mp hp1).2
      have hsf2 : Squarefree p.2 := (Finset.mem_filter.mp hp2).2
      have h1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp1).1).1
      have h2 : 1 ≤ p.2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1, ?_⟩,
        Finset.mem_Icc.mpr ⟨h2, ?_⟩⟩, hsf1, hsf2, hpk⟩
      · rw [← hpk]
        refine Nat.le_of_dvd (by positivity) (dvd_trans ?_ (Nat.dvd_lcm_left (p.1 ^ 2) p.2))
        rw [pow_two]
        exact dvd_mul_right p.1 p.1
      · rw [← hpk]
        exact Nat.le_of_dvd (by positivity) (Nat.dvd_lcm_right (p.1 ^ 2) p.2)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (abs_nonneg _)

end

end Submission.ASP
