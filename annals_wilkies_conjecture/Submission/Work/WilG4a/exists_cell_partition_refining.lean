import Mathlib
import Submission.Work.Wilkies.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilG4a
open WilkiesDesign

/-! ## Elementary facts about the frozen `IsCylDecomp`

`WilkiesDesign.IsCylDecomp n C` is the frozen notion of a cylindrical decomposition of
`ℝⁿ`: a finite set `C` of nonempty cells, pairwise disjoint, covering `ℝⁿ`, whose
projections along the first `n` coordinates again form a cylindrical decomposition.  For the
refinement statement below we only need the three "pointwise" consequences: every member is
a cell, distinct members are disjoint, and the members cover the whole space.  These are
extracted by induction on the dimension, unfolding `IsCylDecomp` once at each step. -/

/-- Every member of a cylindrical decomposition is a cell. -/
theorem cylDecomp_isCell (n : ℕ) {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) : ∀ κ ∈ C, WilkiesDesign.IsCell n κ := by
  induction n with
  | zero =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    intro κ hκ
    rw [h] at hκ
    simp only [Finset.mem_singleton] at hκ
    subst hκ
    exact WilkiesDesign.IsCell.zero
  | succ n ih =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    exact fun κ hκ => (h.1 κ hκ).1

/-- Distinct members of a cylindrical decomposition are disjoint. -/
theorem cylDecomp_disjoint (n : ℕ) {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) :
    ∀ ⦃κ κ'⦄, κ ∈ C → κ' ∈ C → κ ≠ κ' → Disjoint κ κ' := by
  induction n with
  | zero =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    intro κ κ' hκ hκ' hne
    rw [h] at hκ hκ'
    simp only [Finset.mem_singleton] at hκ hκ'
    subst hκ; subst hκ'
    exact absurd rfl hne
  | succ n ih =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    exact fun κ κ' hκ hκ' hne => h.2.1 hκ hκ' hne

/-- The members of a cylindrical decomposition cover the whole space. -/
theorem cylDecomp_exists_mem (n : ℕ) {C : Finset (Set (Fin n → ℝ))}
    (h : WilkiesDesign.IsCylDecomp n C) (z : Fin n → ℝ) : ∃ κ ∈ C, z ∈ κ := by
  induction n with
  | zero =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    refine ⟨Set.univ, ?_, trivial⟩
    rw [h]
    simp
  | succ n ih =>
    simp only [WilkiesDesign.IsCylDecomp] at h
    exact h.2.2.1 z

/-! ## Refining a finite family by a cell partition

Given a sharply o-minimal structure `S` with sharp cell decomposition, any finite family
`X : ι → Set (Fin n → ℝ)` of `Ω F D`-definable sets is refined by a *partition of `ℝⁿ` into
cells of a single `Ω a (c.eval D)`-format*, whose number is bounded polynomially in `D` and
`card ι`.  This is `SharpCD` with the `Finset` of cells replaced by an explicit enumeration
`Fin m → Set (Fin n → ℝ)`, the three defining properties of a cylindrical decomposition
(each member a cell, pairwise disjoint, covering) spelled out, and the refinement condition
written in the `Disjoint … ∨ … ⊆` form. -/
theorem exists_cell_partition_refining (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (F n : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D : ℕ) (ι : Type) [Fintype ι] (X : ι → Set (Fin n → ℝ)),
        (∀ i, X i ∈ S.Ω F D n) →
        ∃ (m : ℕ), m ≤ MvPolynomial.eval ![D, Fintype.card ι] b ∧
          ∃ κ : Fin m → Set (Fin n → ℝ),
            (∀ σ, κ σ ∈ S.Ω a (c.eval D) n) ∧
            (∀ σ, WilkiesDesign.IsCell n (κ σ)) ∧
            (∀ z : Fin n → ℝ, ∃ σ, z ∈ κ σ) ∧
            (∀ σ σ' : Fin m, σ ≠ σ' → Disjoint (κ σ) (κ σ')) ∧
            (∀ (i : ι) (σ : Fin m), Disjoint (κ σ) (X i) ∨ κ σ ⊆ X i) := by
  obtain ⟨a, b, c, H⟩ := hcd F n
  refine ⟨a, b, c, ?_⟩
  intro D ι _ X hX
  -- Reindex the family along `ι ≃ Fin (card ι)` so that `SharpCD` applies.
  let e2 : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Y : Fin (Fintype.card ι) → Set (Fin n → ℝ) := fun j => X (e2.symm j)
  have hY : ∀ j, Y j ∈ S.Ω F D n := fun j => hX (e2.symm j)
  obtain ⟨C, hcdC, href, hcard, hmem⟩ := H D (Fintype.card ι) Y hY
  -- Enumerate the finite set `C` of cells by `Fin (card C)`.
  let e : ↥C ≃ Fin (Fintype.card ↥C) := Fintype.equivFin ↥C
  let κ : Fin (Fintype.card ↥C) → Set (Fin n → ℝ) := fun σ => (e.symm σ).val
  have hκC : ∀ σ, κ σ ∈ C := fun σ => (e.symm σ).prop
  refine ⟨Fintype.card ↥C, ?_, κ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe]; exact hcard
  · intro σ; exact hmem (κ σ) (hκC σ)
  · intro σ; exact cylDecomp_isCell n hcdC (κ σ) (hκC σ)
  · intro z
    obtain ⟨c', hc', hz⟩ := cylDecomp_exists_mem n hcdC z
    refine ⟨e ⟨c', hc'⟩, ?_⟩
    have h1 : κ (e ⟨c', hc'⟩) = c' := by simp [κ]
    rw [h1]; exact hz
  · intro σ σ' hne
    have hκinj : Function.Injective κ := by
      intro σ σ' h
      have h' : (e.symm σ : ↥C) = e.symm σ' := Subtype.ext h
      have := congrArg e h'
      simpa using this
    exact cylDecomp_disjoint n hcdC (hκC σ) (hκC σ') (fun hh => hne (hκinj hh))
  · intro i σ
    have hYj : Y (e2 i) = X i := by simp [Y, e2]
    rcases href (e2 i) (κ σ) (hκC σ) with hsub | hdis
    · exact Or.inr (hYj ▸ hsub)
    · exact Or.inl (hYj ▸ hdis)

end Work.WilG4a
