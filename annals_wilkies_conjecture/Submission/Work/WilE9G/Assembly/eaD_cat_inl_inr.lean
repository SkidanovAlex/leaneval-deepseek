import Mathlib
import Submission.Work.WilE7.SubPfAux.unionSet_set

/-!
  WilE9G / Assembly — the symbolic derivative `eaD` is compatible with the chain
  concatenation `EAChain.cat`.

  Concatenating the chains `c₁` and `c₂` (`Work.WilE7.EAChain.cat c₁ c₂ : EAChain k (r₁+r₂)`)
  places the `exp`-atoms of `c₁` at the positions `Fin.castAdd r₂ ·` and those of `c₂` at the
  positions `Fin.natAdd r₁ ·`.  The inclusions `Work.WilE7.EAPoly.inl` (resp. `.inr`) view a
  polynomial of the `r₁`-chain (resp. the `r₂`-chain) as a polynomial of the concatenation by
  reindexing only the atom variables, along `Sum.map id (Fin.castAdd r₂)`
  (resp. `Sum.map id (Fin.natAdd r₁)`).

  The content of this file is that the symbolic derivative `eaD` *sits over* this reindexing:

  * `eaD (cat c₁ c₂) l (inl Q) = inl (eaD c₁ l Q)`,
  * `eaD (cat c₁ c₂) l (inr Q) = inr (eaD c₂ l Q)`.

  Both the `x`-part (`pderiv (Sum.inl l)`) and the atom part (the sum over `Fin (r₁+r₂)`) of
  `eaD` reduce to the corresponding expression of the smaller chain: the atom directions that
  belong to the *other* chain are not in the range of the reindexing, so their contribution
  vanishes (`MvPolynomial.pderiv_eq_zero_of_notMem_vars` together with
  `MvPolynomial.mem_vars_rename`).  The two sums over `Fin (r₁+r₂)` are split with
  `Fin.sum_univ_add`.
-/

namespace Work.WilE9G.Assembly

open WilkiesDesign WilkiesDesign.E Work.WilE7

/-- `Sum.map id (Fin.castAdd r₂)` is injective. -/
private lemma inj_castAdd_map {k r₁ r₂ : ℕ} :
    Function.Injective (Sum.map (id : Fin k → Fin k) (Fin.castAdd r₂ : Fin r₁ → Fin (r₁ + r₂))) := by
  rw [Sum.map_injective]
  exact ⟨Function.injective_id, Fin.castAdd_injective r₁ r₂⟩

/-- `Sum.map id (Fin.natAdd r₁)` is injective. -/
private lemma inj_natAdd_map {k r₁ r₂ : ℕ} :
    Function.Injective (Sum.map (id : Fin k → Fin k) (Fin.natAdd r₁ : Fin r₂ → Fin (r₁ + r₂))) := by
  rw [Sum.map_injective]
  exact ⟨Function.injective_id, Fin.natAdd_injective r₂ r₁⟩

/-- The atom part of `eaD (cat c₁ c₂) l (inl Q)` equals the atom part of `eaD c₁ l Q`
under the reindexing `Sum.map id (Fin.castAdd r₂)`: the atoms of `c₂` contribute `0` because
their directions are outside the range of that reindexing. -/
private lemma cat_sum_inl {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (Q : EAPoly k r₁) (l : Fin k) :
    (∑ j : Fin (r₁ + r₂), MvPolynomial.C ((EAChain.cat c₁ c₂).a j l) * MvPolynomial.X (Sum.inr j)
        * MvPolynomial.pderiv (Sum.inr j)
            (MvPolynomial.rename (Sum.map id (Fin.castAdd r₂)) Q))
      = MvPolynomial.rename (Sum.map id (Fin.castAdd r₂))
          (∑ j : Fin r₁, MvPolynomial.C (c₁.a j l) * MvPolynomial.X (Sum.inr j)
            * MvPolynomial.pderiv (Sum.inr j) Q) := by
  rw [Fin.sum_univ_add, map_sum]
  -- the `c₂`-atoms contribute nothing: their directions are not in the range of the reindexing
  have h2 : (∑ j₂ : Fin r₂, MvPolynomial.C ((EAChain.cat c₁ c₂).a (Fin.natAdd r₁ j₂) l)
        * MvPolynomial.X (Sum.inr (Fin.natAdd r₁ j₂))
        * MvPolynomial.pderiv (Sum.inr (Fin.natAdd r₁ j₂))
            (MvPolynomial.rename (Sum.map id (Fin.castAdd r₂)) Q)) = 0 := by
    apply Finset.sum_eq_zero
    intro j₂ _
    have hz : MvPolynomial.pderiv (Sum.inr (Fin.natAdd r₁ j₂))
        (MvPolynomial.rename (Sum.map id (Fin.castAdd r₂)) Q) = 0 := by
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      intro hmem
      obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename (Sum.map id (Fin.castAdd r₂)) Q hmem
      cases i with
      | inl a => simp at hi
      | inr b =>
        simp only [Sum.map_inr, Sum.inr.injEq] at hi
        have hval := congrArg Fin.val hi
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        have := b.isLt
        omega
    rw [hz, mul_zero]
  rw [h2, add_zero]
  -- the `c₁`-atoms are carried over by the reindexing
  apply Finset.sum_congr rfl
  intro j₁ _
  rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
      (MvPolynomial.pderiv_rename inj_castAdd_map (Sum.inr j₁) Q).symm]
  simp [EAChain.cat]

/-- The atom part of `eaD (cat c₁ c₂) l (inr Q)` equals the atom part of `eaD c₂ l Q`
under the reindexing `Sum.map id (Fin.natAdd r₁)`: now it is the atoms of `c₁` that contribute
`0`. -/
private lemma cat_sum_inr {k r₁ r₂ : ℕ} (c₁ : EAChain k r₁) (c₂ : EAChain k r₂)
    (Q : EAPoly k r₂) (l : Fin k) :
    (∑ j : Fin (r₁ + r₂), MvPolynomial.C ((EAChain.cat c₁ c₂).a j l) * MvPolynomial.X (Sum.inr j)
        * MvPolynomial.pderiv (Sum.inr j)
            (MvPolynomial.rename (Sum.map id (Fin.natAdd r₁)) Q))
      = MvPolynomial.rename (Sum.map id (Fin.natAdd r₁))
          (∑ j : Fin r₂, MvPolynomial.C (c₂.a j l) * MvPolynomial.X (Sum.inr j)
            * MvPolynomial.pderiv (Sum.inr j) Q) := by
  rw [Fin.sum_univ_add, map_sum]
  -- the `c₁`-atoms contribute nothing
  have h1 : (∑ j₁ : Fin r₁, MvPolynomial.C ((EAChain.cat c₁ c₂).a (Fin.castAdd r₂ j₁) l)
        * MvPolynomial.X (Sum.inr (Fin.castAdd r₂ j₁))
        * MvPolynomial.pderiv (Sum.inr (Fin.castAdd r₂ j₁))
            (MvPolynomial.rename (Sum.map id (Fin.natAdd r₁)) Q)) = 0 := by
    apply Finset.sum_eq_zero
    intro j₁ _
    have hz : MvPolynomial.pderiv (Sum.inr (Fin.castAdd r₂ j₁))
        (MvPolynomial.rename (Sum.map id (Fin.natAdd r₁)) Q) = 0 := by
      apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
      intro hmem
      obtain ⟨i, -, hi⟩ := MvPolynomial.mem_vars_rename (Sum.map id (Fin.natAdd r₁)) Q hmem
      cases i with
      | inl a => simp at hi
      | inr b =>
        simp only [Sum.map_inr, Sum.inr.injEq] at hi
        have hval := congrArg Fin.val hi
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        have := b.isLt
        omega
    rw [hz, mul_zero]
  rw [h1, zero_add]
  -- the `c₂`-atoms are carried over by the reindexing
  apply Finset.sum_congr rfl
  intro j₂ _
  rw [map_mul, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X,
      (MvPolynomial.pderiv_rename inj_natAdd_map (Sum.inr j₂) Q).symm]
  simp [EAChain.cat]

theorem eaD_cat_inl_inr {k r₁ r₂ : ℕ} (c₁ : WilkiesDesign.E.EAChain k r₁)
    (c₂ : WilkiesDesign.E.EAChain k r₂) :
    (∀ (Q : WilkiesDesign.E.EAPoly k r₁) (l : Fin k),
        WilkiesDesign.E.eaD (Work.WilE7.EAChain.cat c₁ c₂) l
          (Work.WilE7.EAPoly.inl Q) = Work.WilE7.EAPoly.inl (WilkiesDesign.E.eaD c₁ l Q)) ∧
    (∀ (Q : WilkiesDesign.E.EAPoly k r₂) (l : Fin k),
        WilkiesDesign.E.eaD (Work.WilE7.EAChain.cat c₁ c₂) l
          (Work.WilE7.EAPoly.inr Q) = Work.WilE7.EAPoly.inr (WilkiesDesign.E.eaD c₂ l Q)) := by
  constructor
  · intro Q l
    simp only [WilkiesDesign.E.eaD, Work.WilE7.EAPoly.inl]
    rw [map_add]
    congr 1
    · exact MvPolynomial.pderiv_rename inj_castAdd_map (Sum.inl l) Q
    · exact cat_sum_inl c₁ c₂ Q l
  · intro Q l
    simp only [WilkiesDesign.E.eaD, Work.WilE7.EAPoly.inr]
    rw [map_add]
    congr 1
    · exact MvPolynomial.pderiv_rename inj_natAdd_map (Sum.inl l) Q
    · exact cat_sum_inr c₁ c₂ Q l

end Work.WilE9G.Assembly
