import Mathlib

namespace Work.Horn

/-- **Characterisation of a polynomial all of whose critical points are zeros.**

If every root of the derivative of a nonzero complex polynomial `P` is also a root of `P`,
then `P` has exactly one root (with multiplicity).  Equivalently `P` is a nonzero constant
multiple of `(X - a)^n`.

The proof is a counting argument:  if `a₁, …, a_k` are the distinct roots of `P`, then each
`aᵢ` is a root of `P'` of multiplicity `mᵢ - 1` (`mᵢ = rootMultiplicity aᵢ P`), so the roots of
`P'` that lie among the roots of `P` contribute `Σ (mᵢ - 1) = natDegree P - k` to the total
number `natDegree P - 1` of roots of `P'`.  Every root of `P'` is a root of `P` by hypothesis,
so `natDegree P - 1 = natDegree P - k`, whence `k = 1`. -/
theorem existsUnique_root_of_roots_derivative {P : Polynomial ℂ} (hP : P ≠ 0)
    (h : ∀ z : ℂ, (Polynomial.derivative P).IsRoot z → P.IsRoot z) :
    ∃! z : ℂ, P.IsRoot z := by
  classical
  by_cases hdeg : P.natDegree = 0
  · -- `P` is a nonzero constant: its derivative vanishes, so the hypothesis forces `P = 0`.
    exfalso
    have hder0 : Polynomial.derivative P = 0 := Polynomial.derivative_eq_zero.mpr hdeg
    have hroot : (Polynomial.derivative P).IsRoot 0 := by
      rw [hder0]; simp [Polynomial.IsRoot]
    have hP0 : P.IsRoot 0 := h 0 hroot
    have hc0 : P.coeff 0 = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hP0
      simpa [Polynomial.IsRoot] using hP0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, hc0, Polynomial.C_0] at hP
    exact hP rfl
  · have hdegpos : 0 < P.natDegree := Nat.pos_of_ne_zero hdeg
    have hPder_ne : Polynomial.derivative P ≠ 0 := Polynomial.derivative_ne_zero.mpr hdeg
    have hsplit : P.Splits := IsAlgClosed.splits P
    have hsplit' : (Polynomial.derivative P).Splits := IsAlgClosed.splits _
    -- Roots of `P'` are roots of `P`, hence lie in `P.roots`.
    have hsub : (Polynomial.derivative P).roots.toFinset ⊆ P.roots.toFinset := by
      intro a ha
      rw [Multiset.mem_toFinset] at ha ⊢
      exact (Polynomial.mem_roots hP).mpr (h a ((Polynomial.mem_roots hPder_ne).mp ha))
    -- Each root of `P'` that is a root of `P` has multiplicity one less in `P'` than in `P`.
    have hcount_le : ∀ a ∈ (Polynomial.derivative P).roots.toFinset,
        Multiset.count a (Polynomial.derivative P).roots ≤ Multiset.count a P.roots - 1 := by
      intro a ha
      have hra : (Polynomial.derivative P).IsRoot a :=
        (Polynomial.mem_roots hPder_ne).mp (Multiset.mem_toFinset.mp ha)
      rw [Polynomial.count_roots (p := Polynomial.derivative P), Polynomial.count_roots (p := P),
        Polynomial.derivative_rootMultiplicity_of_root (h a hra)]
    -- `card P'.roots ≤ Σ_{a ∈ roots P} (count a P - 1)`.
    have hle : (Polynomial.derivative P).roots.card
        ≤ ∑ a ∈ P.roots.toFinset, (Multiset.count a P.roots - 1) := by
      calc (Polynomial.derivative P).roots.card
          = ∑ a ∈ (Polynomial.derivative P).roots.toFinset,
              Multiset.count a (Polynomial.derivative P).roots :=
            (Multiset.toFinset_sum_count_eq _).symm
        _ ≤ ∑ a ∈ (Polynomial.derivative P).roots.toFinset,
              (Multiset.count a P.roots - 1) := Finset.sum_le_sum hcount_le
        _ ≤ ∑ a ∈ P.roots.toFinset, (Multiset.count a P.roots - 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => Nat.zero_le _)
    -- `Σ_{a ∈ roots P} (count a P - 1) + (number of distinct roots of P) = natDegree P`.
    have hsum : ∑ a ∈ P.roots.toFinset, (Multiset.count a P.roots - 1) + P.roots.toFinset.card
        = P.natDegree := by
      have hstep : ∀ a ∈ P.roots.toFinset,
          (Multiset.count a P.roots - 1) + 1 = Multiset.count a P.roots := by
        intro a ha
        have h1 : 1 ≤ Multiset.count a P.roots := by
          rw [Polynomial.count_roots (p := P)]
          exact (Polynomial.rootMultiplicity_pos hP).mpr
            ((Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp ha))
        exact Nat.sub_add_cancel h1
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib, hsplit.natDegree_eq_card_roots,
        ← Multiset.toFinset_sum_count_eq]
      exact Finset.sum_congr rfl fun a ha => hstep a ha
    have hchain : (Polynomial.derivative P).roots.card + P.roots.toFinset.card ≤ P.natDegree := by
      calc (Polynomial.derivative P).roots.card + P.roots.toFinset.card
          ≤ (∑ a ∈ P.roots.toFinset, (Multiset.count a P.roots - 1)) + P.roots.toFinset.card :=
            Nat.add_le_add_right hle _
        _ = P.natDegree := hsum
    have hcard' : (Polynomial.derivative P).roots.card = P.natDegree - 1 := by
      rw [← hsplit'.natDegree_eq_card_roots, Polynomial.natDegree_derivative]
    -- `natDegree P - 1 + k ≤ natDegree P` forces `k = 1`.
    have hT1 : P.roots.toFinset.card = 1 := by
      have hle' : (P.natDegree - 1) + P.roots.toFinset.card ≤ P.natDegree := by
        rw [← hcard']; exact hchain
      have hTpos : 0 < P.roots.toFinset.card := by
        obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (hsplit.roots_ne_zero hdeg)
        exact Finset.card_pos.mpr ⟨a, by rwa [Multiset.mem_toFinset]⟩
      omega
    obtain ⟨a, ha_mem, ha_uniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hT1
    exact ⟨a, (Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp ha_mem),
      fun z hz => ha_uniq z (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hz))⟩

end Work.Horn
