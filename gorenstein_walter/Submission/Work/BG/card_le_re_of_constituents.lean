import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **The number of distinct irreducible constituents of `χ` with multiplicity `≥ 1` is at
most the degree `χ(1)`.**

Decompose the genuine character `χ` as `χ = ∑_{a ∈ Irr} m_a · a` with multiplicities
`m_a = ⟨χ, a⟩ ∈ ℕ` (`IsCharacter.exists_natFinsupp_eq_sum`).  Evaluating at `1` and taking real
parts gives `(χ 1).re = ∑_{a} m_a · (a 1).re`, a sum of non-negative terms.  For `a ∈ s` we have
`m_a = (⟨χ, a⟩).re ≥ 1` (so `a` occurs in the support) and `(a 1).re ≥ 1` (the degree of an
irreducible character is a positive integer), whence the `s`-indexed sub-sum already dominates
`s.card`. -/
theorem card_le_re_of_constituents {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (χ : OddOrder.RepresentationTheory.ClassFunction K ℂ)
    (hχ : OddOrder.RepresentationTheory.IsCharacter χ)
    (s : Finset (OddOrder.RepresentationTheory.ClassFunction K ℂ))
    (hs : ∀ a ∈ s, OddOrder.RepresentationTheory.IsIrreducibleCharacter a)
    (hmul : ∀ a ∈ s, 1 ≤ (OddOrder.RepresentationTheory.ClassFunction.inner χ a).re) :
    (s.card : ℝ) ≤ (χ 1).re := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hχ.exists_natFinsupp_eq_sum
  -- evaluation of a finite sum of class functions at `1`
  have hsum_apply : ∀ (t : Finset (ClassFunction K ℂ))
      (F : ClassFunction K ℂ → ClassFunction K ℂ),
      (∑ a ∈ t, F a) 1 = ∑ a ∈ t, (F a) 1 := by
    intro t F
    induction t using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  -- the real-part decomposition of `χ(1)`
  have hχ1 : (χ 1).re = ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := by
    have hval : χ 1 = ∑ a ∈ m.support, (m a : ℂ) * (a 1) := by
      rw [hsum, hsum_apply]
      exact Finset.sum_congr rfl fun a _ => ClassFunction.smul_apply _ _ _
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  -- every element of `s` occurs in the support with multiplicity `≥ 1`
  have hm_ge : ∀ a ∈ s, 1 ≤ m a := by
    intro a ha
    have hcoe := hcoeff a (hs a ha)
    have hre : (m a : ℝ) = (ClassFunction.inner χ a).re := by
      rw [← hcoe, Complex.natCast_re]
    have : (1 : ℝ) ≤ (m a : ℝ) := by rw [hre]; exact hmul a ha
    exact_mod_cast this
  have hmem_supp : ∀ a ∈ s, a ∈ m.support := fun a ha =>
    Finsupp.mem_support_iff.mpr (by have := hm_ge a ha; omega)
  -- each irreducible degree `(a 1).re` is at least `1`
  have hdeg : ∀ a ∈ m.support, (1 : ℝ) ≤ (a 1).re := by
    intro a ha
    have ha_mem : a ∈ irreducibleCharacters K := hsupp (Finset.mem_coe.mpr ha)
    obtain ⟨d, hdpos, hd1⟩ :=
      irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha_mem⟩ : IrreducibleCharacter K)
    have hd1' : a (1 : K) = (d : ℂ) := hd1
    rw [hd1', Complex.natCast_re]
    have : (1 : ℕ) ≤ d := by omega
    exact_mod_cast this
  -- each summand is non-negative
  have hterm_nn : ∀ a ∈ m.support, (0 : ℝ) ≤ (m a : ℝ) * (a 1).re := fun a ha =>
    mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (hdeg a ha))
  -- `s.card` is dominated by the `s`-indexed sub-sum
  have step1 : (s.card : ℝ) ≤ ∑ a ∈ s, (m a : ℝ) * (a 1).re := by
    have hcard : (s.card : ℝ) = ∑ a ∈ s, (1 : ℝ) := by simp
    rw [hcard]
    refine Finset.sum_le_sum fun a ha => ?_
    have h1 : (1 : ℝ) ≤ (m a : ℝ) := by exact_mod_cast hm_ge a ha
    have h2 : (1 : ℝ) ≤ (a 1).re := hdeg a (hmem_supp a ha)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (m a : ℝ) * (a 1).re := mul_le_mul h1 h2 (by norm_num) (by linarith)
  -- and the sub-sum is dominated by the full sum over the support
  have step2 : ∑ a ∈ s, (m a : ℝ) * (a 1).re
      ≤ ∑ a ∈ m.support, (m a : ℝ) * (a 1).re :=
    Finset.sum_le_sum_of_subset_of_nonneg hmem_supp fun a ha _ => hterm_nn a ha
  calc (s.card : ℝ) ≤ ∑ a ∈ s, (m a : ℝ) * (a 1).re := step1
    _ ≤ ∑ a ∈ m.support, (m a : ℝ) * (a 1).re := step2
    _ = (χ 1).re := hχ1.symm

end Work.BG
