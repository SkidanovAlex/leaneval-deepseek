import Mathlib

set_option linter.unusedVariables false

namespace Commons.RingTheory.Valuation

theorem exists_monic_splits_separable_valuation {F : Type*} [Field F] (C : ValuationSubring F)
    (d : F) (hd : d ≠ 0) (hdv : C.valuation d < 1) (n : ℕ) (hn : 0 < n) :
    ∃ h : Polynomial F, h.Monic ∧ h.Splits ∧ h.Separable ∧ h.natDegree = n ∧
      (∀ a : F, h.IsRoot a → C.valuation a ≤ 1) := by
  have hdC : d ∈ C := (C.valuation_le_one_iff d).1 (le_of_lt hdv)
  have hval_lt : ∀ k : ℕ, 0 < k → C.valuation (d ^ k) < 1 := by
    intro k hk
    rw [map_pow]
    exact pow_lt_one₀ (zero_le : (0 : C.ValueGroup) ≤ C.valuation d) hdv hk.ne'
  have key_le : ∀ k l : ℕ, 0 < k → k ≤ l → d ^ k = d ^ l → k = l := by
    intro k l _ hkl hdkl
    have hdecomp : d ^ l = d ^ k * d ^ (l - k) := by
      rw [← pow_add]; congr 1; omega
    rw [hdecomp] at hdkl
    have hone : d ^ (l - k) = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero k hd)
      rw [mul_one]
      exact hdkl.symm
    rcases Nat.eq_zero_or_pos (l - k) with h0 | hpos
    · omega
    · have h1 : C.valuation (d ^ (l - k)) = 1 := by rw [hone, map_one]
      have h2 := hval_lt (l - k) hpos
      rw [h1] at h2
      exact absurd h2 (lt_irrefl 1)
  have hkey : ∀ k l : ℕ, 0 < k → 0 < l → d ^ k = d ^ l → k = l := by
    intro k l hk hl hkl
    rcases le_total k l with h | h
    · exact key_le k l hk h hkl
    · exact (key_le l k hl h hkl.symm).symm
  refine ⟨∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (d ^ (i + 1))), ?_, ?_, ?_, ?_, ?_⟩
  · exact Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  · refine Polynomial.Splits.prod (fun i _ => ?_)
    simpa only [sub_eq_add_neg, Polynomial.C_neg] using Polynomial.Splits.X_add_C (-(d ^ (i + 1)))
  · rw [Polynomial.separable_prod_X_sub_C_iff']
    intro i _ j _ hij
    exact Nat.succ.inj (hkey (i + 1) (j + 1) (Nat.succ_pos i) (Nat.succ_pos j) hij)
  · rw [Polynomial.natDegree_prod (s := Finset.range n)
      (f := fun i => (Polynomial.X - Polynomial.C (d ^ (i + 1)) : Polynomial F))
      (fun i _ => Polynomial.X_sub_C_ne_zero _)]
    have hdeg : ∀ x ∈ Finset.range n,
        (Polynomial.X - Polynomial.C (d ^ (x + 1)) : Polynomial F).natDegree = 1 :=
      fun x _ => Polynomial.natDegree_X_sub_C _
    rw [Finset.sum_congr rfl hdeg]
    simp
  · intro a ha
    rw [Polynomial.isRoot_prod] at ha
    obtain ⟨i, _, hri⟩ := ha
    rw [Polynomial.root_X_sub_C] at hri
    rw [← hri]
    exact (C.valuation_le_one_iff (d ^ (i + 1))).2 (pow_mem hdC (i + 1))

end Commons.RingTheory.Valuation
