import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

open Classical
open scoped BigOperators

/-- Chain of equalities around a square, B-form: a pointwise dispute of a B-edge yields a pointwise
dispute of one of the other three edges of the square.  (Transpose of `pdispA_far`.) -/
lemma pdispB_far_chain {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) (i j : Fin Δ)
    (h : pdispB B W v i j) :
    pdispA A W v i j ∨ pdispB B W (nA A v i) i j ∨ pdispA A W (nB B v j) i j := by
  by_contra hc
  simp only [pdispA, pdispB, view, not_or, not_ne_iff] at hc h
  obtain ⟨h1, h2, h3⟩ := hc
  rw [nA_nB] at h2
  exact h (h1.trans (h2.trans h3.symm))

/-- **Claim 4.10 in the B-direction (local distance)**, the transpose of `lr_claim410_A`: if the
B-edge through `v` in direction `j` is disputed, then the column `j` of the view at `v` and of its
B-neighbour `nB B v j` are two distinct words of `CA` (hypothesis `hrowA`), differing in
`≥ δ0 * Δ` rows (hypothesis `hdA`); each such row `i` gives either the parallel B-edge
(pointwise dispute `pdispB B W (nA A v i) i j`), or an A-edge at `v` (`pdispA A W v i j`) or at
`nB B v j` (`pdispA A W (nB B v j) i j`). -/
theorem lr_claim410_B {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 : ℝ)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hrowA : ∀ v : Vtx G, ∀ j : Fin Δ, (fun i => view W v (i, j)) ∈ CA)
    (hdA : ∀ x ∈ CA, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (v : Vtx G) (j : Fin Δ) (h : dispBE B W v j) :
    δ0 * Δ ≤ ((Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j)).card : ℝ)
      + (rA A W v : ℝ) + (rA A W (nB B v j) : ℝ) := by
  set cv : Fin Δ → ZMod 2 := fun i => view W v (i, j) with hcv
  set cn : Fin Δ → ZMod 2 := fun i => view W (nB B v j) (i, j) with hcn
  have hcvC : cv ∈ CA := hrowA v j
  have hcnC : cn ∈ CA := hrowA (nB B v j) j
  have hne : cv ≠ cn := by
    obtain ⟨i, hi⟩ := h
    exact fun hh => hi (congrFun hh i)
  have hxmem : cv - cn ∈ CA := CA.sub_mem hcvC hcnC
  have hxne : cv - cn ≠ 0 := by
    intro hh; exact hne (sub_eq_zero.mp hh)
  have hbound : δ0 * Δ ≤ (hammingNorm (cv - cn) : ℝ) := hdA _ hxmem hxne
  have hD : hammingNorm (cv - cn) =
      (Finset.univ.filter (fun i : Fin Δ => cv i ≠ cn i)).card := by
    rw [hammingNorm]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero]
  have hDsub : (Finset.univ.filter (fun i : Fin Δ => cv i ≠ cn i)) ⊆
      (Finset.univ.filter (fun i : Fin Δ => dispAE A W v i))
      ∪ (Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j))
      ∪ (Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    rcases pdispB_far_chain A B W v i j hi with h1 | h1 | h1
    · exact Or.inl (Or.inl ⟨j, h1⟩)
    · exact Or.inl (Or.inr ⟨i, h1⟩)
    · exact Or.inr ⟨j, h1⟩
  have hcard : (Finset.univ.filter (fun i : Fin Δ => cv i ≠ cn i)).card ≤
      ((Finset.univ.filter (fun i : Fin Δ => dispAE A W v i)).card)
      + ((Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j)).card)
      + ((Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i)).card) := by
    calc (Finset.univ.filter (fun i : Fin Δ => cv i ≠ cn i)).card
        ≤ ((Finset.univ.filter (fun i : Fin Δ => dispAE A W v i))
            ∪ (Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j))
            ∪ (Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i))).card :=
          Finset.card_le_card hDsub
      _ ≤ (((Finset.univ.filter (fun i : Fin Δ => dispAE A W v i))
            ∪ (Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j))).card
            + (Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i)).card) :=
          Finset.card_union_le _ _
      _ ≤ (((Finset.univ.filter (fun i : Fin Δ => dispAE A W v i)).card
            + (Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j)).card)
            + (Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i)).card) :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
  calc δ0 * Δ ≤ (hammingNorm (cv - cn) : ℝ) := hbound
    _ = ((Finset.univ.filter (fun i : Fin Δ => cv i ≠ cn i)).card : ℝ) := by rw [hD]
    _ ≤ (↑(((Finset.univ.filter (fun i : Fin Δ => dispAE A W v i)).card)
            + ((Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j)).card)
            + ((Finset.univ.filter (fun i : Fin Δ => dispAE A W (nB B v j) i)).card)) : ℝ) :=
          by exact_mod_cast hcard
    _ = ((Finset.univ.filter (fun i : Fin Δ => dispBE B W (nA A v i) j)).card : ℝ)
          + (rA A W v : ℝ) + (rA A W (nB B v j) : ℝ) := by
        simp only [rA]
        push_cast
        ring

end Work.LT
