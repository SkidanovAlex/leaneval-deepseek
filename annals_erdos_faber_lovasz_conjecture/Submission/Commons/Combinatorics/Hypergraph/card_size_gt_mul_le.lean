import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

namespace Commons.Combinatorics.Hypergraph

/-- In a linear hypergraph on `Fin n`, the number of edges of size at least
`r + 1` containing a fixed vertex `w`, counted with multiplicity `r`, is at
most `n - 1`.

Each such edge contains at least `r` vertices other than `w`, and each of
those vertices lies in at most one edge through `w`. -/
theorem card_size_gt_mul_le {n : ℕ} (𝓗 : Set (Set (Fin n)))
    (hlin : ∀ e₁ ∈ 𝓗, ∀ e₂ ∈ 𝓗, e₁ ≠ e₂ → (e₁ ∩ e₂).Subsingleton)
    (r : ℕ) (w : Fin n) :
    ({e ∈ 𝓗 | w ∈ e ∧ r < e.ncard}.ncard : ℝ) * (r : ℝ) ≤ (n : ℝ) - 1 := by
  classical
  set S : Set (Set (Fin n)) := {e ∈ 𝓗 | w ∈ e ∧ r < e.ncard} with hS
  have hmem : ∀ e : ↥S,
      (e : Set (Fin n)) ∈ 𝓗 ∧ w ∈ (e : Set (Fin n)) ∧ r < (e : Set (Fin n)).ncard :=
    fun e => e.2
  suffices hnat : S.ncard * r ≤ n - 1 by
    rw [← Nat.cast_mul]
    rw [← Nat.cast_pred (show 0 < n by have hw := w.isLt; omega)]
    exact Nat.cast_le.mpr hnat
  let g : ↥S → Finset (Fin n) := fun e => Finset.univ.filter (fun v => v ∈ (e : Set (Fin n)) ∧ v ≠ w)
  have hg_eq : ∀ e : ↥S, ((g e : Finset (Fin n)) : Set (Fin n)) = (e : Set (Fin n)) \ {w} := by
    intro e; ext v; simp [g]
  have hg_card : ∀ e : ↥S, r ≤ (g e).card := by
    intro e
    obtain ⟨_, hw, hr⟩ := hmem e
    rw [← Set.ncard_coe_finset (g e), hg_eq e, Set.ncard_sdiff_singleton_of_mem hw]
    exact Nat.le_sub_one_of_lt hr
  have hdisj : (↑(Finset.univ : Finset ↥S) : Set ↥S).PairwiseDisjoint g := by
    intro e₁ _ e₂ _ hne
    change Disjoint (g e₁) (g e₂)
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have hv1' : v ∈ (e₁ : Set (Fin n)) ∧ v ≠ w := by have := hv1; simpa [g] using this
    have hv2' : v ∈ (e₂ : Set (Fin n)) ∧ v ≠ w := by have := hv2; simpa [g] using this
    obtain ⟨he₁𝓗, hw₁, _⟩ := hmem e₁
    obtain ⟨he₂𝓗, hw₂, _⟩ := hmem e₂
    have hne' : (e₁ : Set (Fin n)) ≠ (e₂ : Set (Fin n)) := fun h => hne (Subtype.ext h)
    have hss := hlin (e₁ : Set (Fin n)) he₁𝓗 (e₂ : Set (Fin n)) he₂𝓗 hne'
    exact hv1'.2 (hss ⟨hv1'.1, hv2'.1⟩ ⟨hw₁, hw₂⟩)
  have hbU : (Finset.univ.biUnion g).card = ∑ e : ↥S, (g e).card :=
    Finset.card_biUnion hdisj
  have hsub : Finset.univ.biUnion g ⊆ Finset.univ.erase w := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨e, -, hve⟩ := hv
    have hve' : v ∈ (e : Set (Fin n)) ∧ v ≠ w := by have := hve; simpa [g] using this
    rw [Finset.mem_erase]
    exact ⟨hve'.2, Finset.mem_univ v⟩
  have hcard_bU : (Finset.univ.biUnion g).card ≤ n - 1 := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hlower : Fintype.card ↥S * r ≤ ∑ e : ↥S, (g e).card := by
    have h1 : ∑ e : ↥S, (r : ℕ) ≤ ∑ e : ↥S, (g e).card :=
      Finset.sum_le_sum (fun e _ => hg_card e)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  calc S.ncard * r = Fintype.card ↥S * r := by rw [Set.fintypeCard_eq_ncard]
    _ ≤ ∑ e : ↥S, (g e).card := hlower
    _ = (Finset.univ.biUnion g).card := hbU.symm
    _ ≤ n - 1 := hcard_bU

end Commons.Combinatorics.Hypergraph