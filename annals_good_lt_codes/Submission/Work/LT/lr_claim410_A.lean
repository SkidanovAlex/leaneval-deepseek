import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

open Classical

/-- **Claim 4.10 in the A-direction (local distance).** If the A-edge through `v` in direction `i`
is disputed, then the row `i` of the view at `v` and the row `i` of the view at its A-neighbour
`nA A v i` are two distinct words of `CB` (hypothesis `hrowB`), hence differ in at least
`δ0 * Δ` columns (hypothesis `hdB`; use `Submodule.sub_mem`, `sub_ne_zero`, and
`hammingNorm y = #{j | y j ≠ 0}`). For each such column `j`, one of the other three edges of the
square `(v,i,j)` is pointwise disputed (`pdispA_far`): the parallel A-edge (pointwise dispute
`pdispA A W (nB B v j) i j`, giving the first term), the B-edge at `v` (`pdispB B W v i j`) or the
B-edge at `nA A v i` (`pdispB B W (nA A v i) i j`), the last two giving the other two terms. -/
theorem lr_claim410_A {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 : ℝ)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2))
    (hrowB : ∀ v : Vtx G, ∀ i : Fin Δ, (fun j => view W v (i, j)) ∈ CB)
    (hdB : ∀ x ∈ CB, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (v : Vtx G) (i : Fin Δ) (h : dispAE A W v i) :
    δ0 * Δ ≤ ((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i)).card : ℝ)
      + (rB B W v : ℝ) + (rB B W (nA A v i) : ℝ) := by
  -- The two rows (of the view at `v` and of the view at `nA A v i`) as words of length `Δ`.
  set rv : Fin Δ → ZMod 2 := fun j => view W v (i, j) with hrv
  set rn : Fin Δ → ZMod 2 := fun j => view W (nA A v i) (i, j) with hrn
  have hrvC : rv ∈ CB := hrowB v i
  have hrnC : rn ∈ CB := hrowB (nA A v i) i
  -- The dispute says the two rows differ.
  have hne : rv ≠ rn := by
    obtain ⟨j, hj⟩ := h
    exact fun hh => hj (congrFun hh j)
  -- Hence their difference is a nonzero word of `CB`, of Hamming weight `≥ δ0 * Δ`.
  have hxmem : rv - rn ∈ CB := CB.sub_mem hrvC hrnC
  have hxne : rv - rn ≠ 0 := sub_ne_zero.mpr hne
  have hbound : δ0 * Δ ≤ (hammingNorm (rv - rn) : ℝ) := hdB _ hxmem hxne
  -- Hamming weight of the difference = number of columns where the rows differ.
  have hD : hammingNorm (rv - rn) =
      (Finset.univ.filter (fun j : Fin Δ => rv j ≠ rn j)).card := by
    rw [hammingNorm]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, sub_ne_zero]
  -- Each column where the rows differ produces one of the three other disputed edges
  -- of the square `(v,i,j)`.
  have hDsub : (Finset.univ.filter (fun j : Fin Δ => rv j ≠ rn j)) ⊆
      (Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i))
      ∪ (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j))
      ∪ (Finset.univ.filter (fun j : Fin Δ => dispBE B W (nA A v i) j)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
    rcases pdispA_far A B W v i j hj with h1 | h2 | h3
    · exact Or.inl (Or.inr ⟨i, h1⟩)
    · exact Or.inl (Or.inl ⟨j, h2⟩)
    · exact Or.inr ⟨i, h3⟩
  have hcard : (Finset.univ.filter (fun j : Fin Δ => rv j ≠ rn j)).card ≤
      ((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i)).card)
      + (rB B W v) + (rB B W (nA A v i)) := by
    calc (Finset.univ.filter (fun j : Fin Δ => rv j ≠ rn j)).card
        ≤ ((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i))
            ∪ (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j))
            ∪ (Finset.univ.filter (fun j : Fin Δ => dispBE B W (nA A v i) j))).card :=
          Finset.card_le_card hDsub
      _ ≤ (((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i))
            ∪ (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j))).card
            + (Finset.univ.filter (fun j : Fin Δ => dispBE B W (nA A v i) j)).card) :=
          Finset.card_union_le _ _
      _ ≤ (((Finset.univ.filter (fun j : Fin Δ => dispAE A W (nB B v j) i)).card
            + (Finset.univ.filter (fun j : Fin Δ => dispBE B W v j)).card)
            + (Finset.univ.filter (fun j : Fin Δ => dispBE B W (nA A v i) j)).card) :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = _ := rfl
  calc δ0 * Δ ≤ (hammingNorm (rv - rn) : ℝ) := hbound
    _ = ((Finset.univ.filter (fun j : Fin Δ => rv j ≠ rn j)).card : ℝ) := by rw [hD]
    _ ≤ _ := by exact_mod_cast hcard

end Work.LT
