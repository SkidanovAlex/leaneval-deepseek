import Mathlib
import Submission.Work.LT.good_base_defs

namespace Work.LT

open GB

/-- A sparse subspace of dimension `m` admits `m` small vectors spanning it: take a linearly
independent subset of the spanning set of small vectors; it is a basis, hence has `m` elements. -/
lemma exists_small_span_of_isSparse {D : ℕ} {α : ℝ} {m : ℕ}
    {V : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (hsp : GB.IsSparse α V) (hdim : GB.frk V = m) :
    ∃ t : Fin m → ↥(GB.smallVecs α D),
      Submodule.span (ZMod 2) (Set.range (fun i => (t i : Fin D → ZMod 2))) = V := by
  classical
  obtain ⟨S, hS, hspan⟩ := hsp
  obtain ⟨b, hbS, hspanb, hli⟩ := exists_linearIndependent (ZMod 2) S
  have hspanbV : Submodule.span (ZMod 2) b = V := hspanb.trans hspan
  have hbfin : b.Finite := Set.toFinite b
  have : Fintype b := hbfin.fintype
  have hli' : LinearIndepOn (ZMod 2) id b := hli
  have h := finrank_span_set_eq_card (R := ZMod 2) (s := b) hli'
  rw [hspanbV] at h
  have h1 : b.toFinset.card = m := h.symm.trans hdim
  have hcardf : Fintype.card b = m := by
    rw [← Set.toFinset_card]
    exact h1
  let e : b ≃ Fin m := Fintype.equivFinOfCardEq hcardf
  let t : Fin m → ↥(GB.smallVecs α D) := fun i =>
    ⟨((e.symm i : b) : Fin D → ZMod 2), by rw [GB.mem_smallVecs]; exact hS _ (hbS (e.symm i).2)⟩
  refine ⟨t, ?_⟩
  have hrange : Set.range (fun i : Fin m => (t i : Fin D → ZMod 2)) = b := by
    have hcomp : (fun i : Fin m => (t i : Fin D → ZMod 2)) =
        (Subtype.val : b → (Fin D → ZMod 2)) ∘ e.symm := rfl
    rw [hcomp, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ, Subtype.range_val]
  rw [hrange]
  exact hspanbV

/-- The number of `α`-sparse subspaces of dimension `m` is at most `|smallVecs α D|^m`: any such `V` is spanned by `m` small vectors (finite spanning set, then a basis inside it, each basis vector small), so the span map on `m`-tuples of `smallVecs α D` is onto that set. -/
theorem gb_card_sparse_submodule {D : ℕ} (α : ℝ) (m : ℕ) :
    (Nat.card {V : Submodule (ZMod 2) (Fin D → ZMod 2) // GB.IsSparse α V ∧ GB.frk V = m} : ℝ) ≤
      ((GB.smallVecs α D).card : ℝ) ^ m := by
  classical
  let A := Fin m → ↥(GB.smallVecs α D)
  let g : A → Submodule (ZMod 2) (Fin D → ZMod 2) :=
    fun t => Submodule.span (ZMod 2) (Set.range (fun i => (t i : Fin D → ZMod 2)))
  have hfin : (Set.range g).Finite := by
    rw [← Set.image_univ]
    exact Set.finite_univ.image g
  have hsub : {V : Submodule (ZMod 2) (Fin D → ZMod 2) |
      GB.IsSparse α V ∧ GB.frk V = m} ⊆ Set.range g := by
    rintro V ⟨hsp, hdim⟩
    obtain ⟨t, ht⟩ := exists_small_span_of_isSparse hsp hdim
    exact ⟨t, ht⟩
  have hle1 : Nat.card {V : Submodule (ZMod 2) (Fin D → ZMod 2) //
      GB.IsSparse α V ∧ GB.frk V = m} ≤ Nat.card (Set.range g) :=
    Nat.card_mono hfin hsub
  have hle2 : Nat.card (Set.range g) ≤ Nat.card A :=
    Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
  have hA : Nat.card A = (GB.smallVecs α D).card ^ m := by
    simp only [A]
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hmain : Nat.card {V : Submodule (ZMod 2) (Fin D → ZMod 2) //
      GB.IsSparse α V ∧ GB.frk V = m} ≤ (GB.smallVecs α D).card ^ m :=
    hle1.trans (hle2.trans_eq hA)
  have := Nat.cast_le (α := ℝ).mpr hmain
  simpa [Nat.cast_pow] using this

end Work.LT
