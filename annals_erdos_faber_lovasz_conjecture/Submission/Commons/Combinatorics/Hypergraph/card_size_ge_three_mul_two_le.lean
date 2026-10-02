import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Combinatorics.Hypergraph

/-- In a linear hypergraph on `Fin n` all of whose edges have at least two
vertices, twice the number of edges of size at least three containing a fixed
vertex `w` is at most `n - 1 - d`, where `d` is the number of size-two edges
of `𝓗` containing `w`.

Indeed, every edge `e` of size at least three through `w` has at least two
vertices other than `w`; all of them lie outside `{w}` and outside the
neighbours of `w` in the 2-shadow (a vertex `x` with `{w,x} ∈ 𝓗` cannot lie in
`e`, since `{w,x}` and `e` would then be two distinct edges sharing two
vertices), and each vertex outside can occur in at most one such `e`. -/
theorem card_size_ge_three_mul_two_le {n : ℕ} (𝓗 : Set (Set (Fin n)))
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ e.ncard) (w : Fin n) :
    2 * ({e ∈ 𝓗 | w ∈ e ∧ 3 ≤ e.ncard}.ncard : ℝ) ≤
      (n : ℝ) - 1 - ({e ∈ 𝓗 | w ∈ e ∧ e.ncard = 2}.ncard : ℝ) := by
  classical
  let A : Set (Set (Fin n)) := {e ∈ 𝓗 | w ∈ e ∧ 3 ≤ e.ncard}
  let B : Set (Set (Fin n)) := {e ∈ 𝓗 | w ∈ e ∧ e.ncard = 2}
  let N2 : Set (Fin n) := {x | {w, x} ∈ 𝓗}
  let S : Set (Fin n) := ⋃ i : ↥A, ((i : Set (Fin n)) \ {w})
  change 2 * (A.ncard : ℝ) ≤ (n : ℝ) - 1 - (B.ncard : ℝ)
  have memB : ∀ e, e ∈ B ↔ e ∈ 𝓗 ∧ w ∈ e ∧ e.ncard = 2 := fun e => Iff.rfl
  have memN2 : ∀ x, x ∈ N2 ↔ {w, x} ∈ 𝓗 := fun x => Iff.rfl
  -- A vertex in the 2-shadow of `w` is distinct from `w`.
  have hN2_ne : ∀ x ∈ N2, x ≠ w := by
    intro x hx h
    have hb := hbig ({w, x} : Set (Fin n)) hx
    have hsing : ({w, x} : Set (Fin n)) = {w} := by rw [h]; simp
    rw [hsing, Set.ncard_singleton] at hb
    omega
  -- The punctured edges `e \ {w}` for `e ∈ A` are pairwise disjoint.
  have hdisj : Pairwise (Function.onFun Disjoint (fun i : ↥A => ((i : Set (Fin n)) \ {w}))) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_sdiff] at hx hx'
    have hne : (i : Set (Fin n)) ≠ (j : Set (Fin n)) := fun h => hij (Subtype.ext h)
    have hsub := hlin (i : Set (Fin n)) i.2.1 (j : Set (Fin n)) j.2.1 hne
    exact hx.2 (hsub ⟨hx.1, hx'.1⟩ ⟨i.2.2.1, j.2.2.1⟩)
  have hfin : ∀ i : ↥A, ((i : Set (Fin n)) \ {w}).Finite := fun i => Set.toFinite _
  have hS_card : S.ncard = ∑ i : ↥A, ((i : Set (Fin n)) \ {w}).ncard := by
    rw [Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]
  have hterm : ∀ i ∈ (Finset.univ : Finset ↥A), (2:ℕ) ≤ ((i : Set (Fin n)) \ {w}).ncard := by
    intro i _
    have h3 : 3 ≤ (i : Set (Fin n)).ncard := i.2.2.2
    rw [Set.ncard_sdiff_singleton_of_mem i.2.2.1]
    omega
  have hcardA : Fintype.card ↥A = A.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  -- Each edge of `A` contributes at least two vertices of `S`.
  have h2A : 2 * A.ncard ≤ S.ncard := by
    rw [hS_card]
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset ↥A)
      (fun i => ((i : Set (Fin n)) \ {w}).ncard) 2 hterm
    rw [Finset.card_univ, hcardA, nsmul_eq_mul] at h
    simp only [Nat.cast_id] at h
    calc 2 * A.ncard = A.ncard * 2 := by ring
      _ ≤ _ := h
  -- `S` avoids `w` and the 2-shadow of `w`.
  have hSsub : S ⊆ ({w} ∪ N2)ᶜ := by
    intro x hx
    rw [show S = ⋃ i : ↥A, ((i : Set (Fin n)) \ {w}) from rfl, Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    rw [Set.mem_sdiff] at hxi
    rw [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨hxi.2, ?_⟩
    intro hxN2
    have hxw : x ≠ w := fun h => hxi.2 (by rw [h]; exact Set.mem_singleton w)
    have hpair : ({w, x} : Set (Fin n)).ncard = 2 := Set.ncard_pair (Ne.symm hxw)
    have hne : ({w, x} : Set (Fin n)) ≠ (i : Set (Fin n)) := by
      intro h
      have hc : ({w, x} : Set (Fin n)).ncard = (i : Set (Fin n)).ncard := by rw [h]
      have h3 : 3 ≤ (i : Set (Fin n)).ncard := i.2.2.2
      rw [← hc, hpair] at h3
      omega
    have hsub := hlin ({w, x} : Set (Fin n)) hxN2 (i : Set (Fin n)) i.2.1 hne
    exact hxw (hsub ⟨by simp, i.2.2.1⟩ ⟨by simp, hxi.1⟩).symm
  have hdisjSN2 : Disjoint S N2 := by
    rw [Set.disjoint_left]
    intro x hxS hxN2
    exact (hSsub hxS) (Or.inr hxN2)
  -- The size-two edges through `w` are in bijection with the 2-shadow.
  let ψ : Fin n → Set (Fin n) := fun x => {w, x}
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hxy' : ({w, x} : Set (Fin n)) = {w, y} := hxy
    have hx : x ∈ ({w, y} : Set (Fin n)) := by rw [← hxy']; simp
    have hy : y ∈ ({w, x} : Set (Fin n)) := by rw [hxy']; simp
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx
    · rcases hy with hy | hy
      · exact hx.trans hy.symm
      · exact hy.symm
    · exact hx
  have hψmem : ∀ x ∈ N2, ψ x ∈ B := by
    intro x hx
    have hxw : x ≠ w := hN2_ne x hx
    refine ⟨hx, ?_, ?_⟩
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · exact Set.ncard_pair (Ne.symm hxw)
  have hB_image : B = ψ '' N2 := by
    ext e
    constructor
    · intro he
      rw [memB] at he
      obtain ⟨heH, hwe, hec⟩ := he
      have h1 : (e \ {w}).ncard = 1 := by
        rw [Set.ncard_sdiff_singleton_of_mem hwe, hec]
      have hne : (e \ {w}).Nonempty := by
        rw [← Set.ncard_pos, h1]; norm_num
      obtain ⟨x, hx⟩ := hne
      rw [Set.mem_sdiff] at hx
      have hxw : x ≠ w := fun h => hx.2 (by rw [h]; exact Set.mem_singleton w)
      have hpair : ({w, x} : Set (Fin n)) = e := by
        refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite e)
        · intro y hy
          rcases hy with hy | hy
          · rw [hy]; exact hwe
          · rw [hy]; exact hx.1
        · rw [Set.ncard_pair (Ne.symm hxw), hec]
      refine ⟨x, ?_, ?_⟩
      · rw [memN2, hpair]; exact heH
      · exact hpair
    · rintro ⟨x, hx, rfl⟩
      exact hψmem x hx
  have hB_card : B.ncard = N2.ncard := by
    rw [hB_image, Set.ncard_image_of_injective N2 hψinj]
  -- `S ∪ N2` lies in the complement of `{w}`.
  have hUniv : (S ∪ N2).ncard ≤ n - 1 := by
    have hsub : S ∪ N2 ⊆ ({w} : Set (Fin n))ᶜ := by
      intro x hx
      rcases hx with hx | hx
      · intro hw
        exact (hSsub hx) (Or.inl hw)
      · intro hw
        exact hN2_ne x hx (Set.mem_singleton_iff.mp hw)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hcompl : (({w} : Set (Fin n))ᶜ).ncard = n - 1 := by
      rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_fin]
    rw [hcompl] at hle
    exact hle
  have hmain : 2 * A.ncard + B.ncard ≤ n - 1 := by
    rw [hB_card]
    calc 2 * A.ncard + N2.ncard ≤ S.ncard + N2.ncard := Nat.add_le_add_right h2A _
      _ = (S ∪ N2).ncard := (Set.ncard_union_eq hdisjSN2).symm
      _ ≤ n - 1 := hUniv
  have hn1 : 1 ≤ n := by have := w.isLt; omega
  have hcast : 2 * (A.ncard : ℝ) + (B.ncard : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : ((2 * A.ncard + B.ncard : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmain
    rw [Nat.cast_sub hn1] at h1
    push_cast at h1
    linarith
  linarith [hcast]

end Commons.Combinatorics.Hypergraph