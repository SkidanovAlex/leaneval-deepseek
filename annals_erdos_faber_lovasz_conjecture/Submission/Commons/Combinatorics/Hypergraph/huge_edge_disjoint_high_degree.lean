import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Combinatorics.Hypergraph

/-- If `𝓗` is a linear hypergraph (any two edges meet in at most one vertex) on a finite type `V`,
every edge of `𝓗` has at least two vertices, some edge `e ∈ 𝓗` has at least `4` vertices, `v ∈ e`,
and `v` lies in `|V| - 1` or `|V| - 2` edges of `𝓗`, then we reach a contradiction.

The proof counts the sets `f \ {v}` for the edges `f` through `v`: they are pairwise disjoint
subsets of `{v}ᶜ`, so their total cardinality is at most `|V| - 1`. On the other hand each of them is
non-empty and the one belonging to `e` has at least three elements, so their total cardinality is at
least `(#{edges through v} - 1) + 3 = #{edges through v} + 2`. Since the number of edges through `v`
is `|V| - 1` or `|V| - 2`, this bound is impossible. -/
theorem huge_edge_disjoint_high_degree {V : Type*} [Fintype V] [DecidableEq V]
    (𝓗 : Set (Set V))
    (hlin : 𝓗.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton)
    (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) {e : Set V} (he : e ∈ 𝓗) (he4 : 4 ≤ e.ncard)
    {v : V} (hv : v ∈ e)
    (hdeg : {f ∈ 𝓗 | v ∈ f}.ncard = Fintype.card V - 1 ∨
      {f ∈ 𝓗 | v ∈ f}.ncard = Fintype.card V - 2) :
    False := by
  classical
  let S : Set (Set V) := {f ∈ 𝓗 | v ∈ f}
  have hdegS : S.ncard = Fintype.card V - 1 ∨ S.ncard = Fintype.card V - 2 := hdeg
  have hSfin : S.Finite := Set.toFinite S
  have hmem : ∀ f : Set V, f ∈ S ↔ f ∈ 𝓗 ∧ v ∈ f := fun f => Iff.rfl
  -- the sets `f \ {v}` for `f ∈ S` are pairwise disjoint
  have hdisj : S.PairwiseDisjoint (fun f => f \ {v}) := by
    intro f₁ hf₁ f₂ hf₂ hne
    change Disjoint (f₁ \ {v}) (f₂ \ {v})
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨hf₁𝓗, hv₁⟩ := (hmem f₁).mp hf₁
    obtain ⟨hf₂𝓗, hv₂⟩ := (hmem f₂).mp hf₂
    have hsub : (f₁ ∩ f₂).Subsingleton := hlin hf₁𝓗 hf₂𝓗 hne
    have hxv : x = v := hsub ⟨hx₁.1, hx₂.1⟩ ⟨hv₁, hv₂⟩
    exact hx₁.2 hxv
  have hfin : ∀ f ∈ S, (f \ {v}).Finite := fun f _ => Set.toFinite _
  have hcount := hSfin.ncard_biUnion hfin hdisj
  set E : Finset (Set V) := hSfin.toFinset with hEdef
  have hEcard : E.card = S.ncard := by
    rw [hEdef]; exact (Set.ncard_eq_toFinset_card S hSfin).symm
  have hmemE : ∀ f : Set V, f ∈ E ↔ f ∈ S := by
    intro f; rw [hEdef]; exact Set.Finite.mem_toFinset hSfin
  have hcountF : (⋃ f ∈ S, f \ {v}).ncard = ∑ f ∈ E, (f \ {v}).ncard := by
    rw [hcount]
    exact finsum_mem_eq_finite_toFinset_sum (fun f => (f \ {v}).ncard) hSfin
  -- the union sits inside `{v}ᶜ`, whose cardinality is `|V| - 1`
  have hsubc : (⋃ f ∈ S, f \ {v}) ⊆ ({v}ᶜ : Set V) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨f, hfS, hxf⟩ := hx
    exact hxf.2
  have hcompl_ncard : ({v}ᶜ : Set V).ncard = Fintype.card V - 1 := by
    rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card]
  have hsum_le : ∑ f ∈ E, (f \ {v}).ncard ≤ Fintype.card V - 1 := by
    rw [← hcountF]
    exact le_trans (Set.ncard_le_ncard hsubc) (le_of_eq hcompl_ncard)
  -- our distinguished edge `e` belongs to `E`
  have heS : e ∈ S := (hmem e).mpr ⟨he, hv⟩
  have heE : e ∈ E := (hmemE e).mpr heS
  -- every `f \ {v}` is non-empty
  have hge1 : ∀ f ∈ E, 1 ≤ (f \ {v}).ncard := by
    intro f hf
    have hfS : f ∈ S := (hmemE f).mp hf
    obtain ⟨hf𝓗, hvf⟩ := (hmem f).mp hfS
    have h2 : 2 ≤ f.ncard := hno f hf𝓗
    rw [Set.ncard_sdiff_singleton_of_mem hvf]
    omega
  -- `e \ {v}` has at least three elements
  have he3 : 3 ≤ (e \ {v}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hv]
    omega
  have hsplit := Finset.add_sum_erase E (fun f => (f \ {v}).ncard) heE
  have herase_ge : (E.erase e).card ≤ ∑ f ∈ E.erase e, (f \ {v}).ncard := by
    have := Finset.card_nsmul_le_sum (E.erase e) (fun f => (f \ {v}).ncard) 1
      (fun f hf => hge1 f (Finset.mem_of_mem_erase hf))
    simpa using this
  have hcarte : (E.erase e).card + 1 = E.card := Finset.card_erase_add_one heE
  have hsum_ge : E.card + 2 ≤ ∑ f ∈ E, (f \ {v}).ncard := by
    omega
  omega

end Commons.Combinatorics.Hypergraph
