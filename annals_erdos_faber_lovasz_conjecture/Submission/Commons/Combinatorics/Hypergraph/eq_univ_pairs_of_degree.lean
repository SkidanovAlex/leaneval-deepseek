import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Combinatorics.Hypergraph

/-- If `𝓗` is a linear hypergraph (any two edges meet in at most one vertex), every edge of `𝓗`
has at least two vertices, and some vertex `v` lies in exactly `|V| - 1` edges of `𝓗`, then every
pair `{v, w}` with `w ≠ v` is an edge of `𝓗`.

The proof is a counting argument: the sets `e \ {v}`, for the `|V| - 1` edges `e` through `v`, are
pairwise disjoint non-empty subsets of the `(|V| - 1)`-element set `{v}ᶜ`. Their number equals the
size of the ambient set, so each of them is a singleton and their union is all of `{v}ᶜ`. -/
theorem eq_univ_pairs_of_degree (V : Type*) [Fintype V] [DecidableEq V] (𝓗 : Set (Set V))
    (hlin : 𝓗.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton)
    (hno : ∀ e ∈ 𝓗, 2 ≤ e.ncard) {v : V}
    (hdeg : {e ∈ 𝓗 | v ∈ e}.ncard = Fintype.card V - 1) :
    ∀ w : V, w ≠ v → ({v, w} : Set V) ∈ 𝓗 := by
  classical
  let S : Set (Set V) := {e ∈ 𝓗 | v ∈ e}
  have hdegS : S.ncard = Fintype.card V - 1 := hdeg
  have hSfin : S.Finite := Set.toFinite S
  have hmem : ∀ e : Set V, e ∈ S ↔ e ∈ 𝓗 ∧ v ∈ e := fun e => Iff.rfl
  -- the sets `e \ {v}` for `e ∈ S` are pairwise disjoint
  have hdisj : S.PairwiseDisjoint (fun e => e \ {v}) := by
    intro e₁ he₁ e₂ he₂ hne
    change Disjoint (e₁ \ {v}) (e₂ \ {v})
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨he₁𝓗, hv₁⟩ := (hmem e₁).mp he₁
    obtain ⟨he₂𝓗, hv₂⟩ := (hmem e₂).mp he₂
    have hsub : (e₁ ∩ e₂).Subsingleton := hlin he₁𝓗 he₂𝓗 hne
    have hxv : x = v := hsub ⟨hx₁.1, hx₂.1⟩ ⟨hv₁, hv₂⟩
    exact hx₁.2 hxv
  have hfin : ∀ e ∈ S, (e \ {v}).Finite := fun e _ => Set.toFinite _
  have hcount := hSfin.ncard_biUnion hfin hdisj
  set E : Finset (Set V) := hSfin.toFinset with hEdef
  have hEcard : E.card = S.ncard := by
    rw [hEdef]; exact (Set.ncard_eq_toFinset_card S hSfin).symm
  have hmemE : ∀ e : Set V, e ∈ E ↔ e ∈ S := by
    intro e; rw [hEdef]; exact Set.Finite.mem_toFinset hSfin
  have hcountF : (⋃ e ∈ S, e \ {v}).ncard = ∑ e ∈ E, (e \ {v}).ncard := by
    rw [hcount]
    exact finsum_mem_eq_finite_toFinset_sum (fun e => (e \ {v}).ncard) hSfin
  -- the union sits inside `{v}ᶜ`, whose cardinality is `|V| - 1 = E.card`
  have hsubc : (⋃ e ∈ S, e \ {v}) ⊆ ({v}ᶜ : Set V) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨e, heS, hxe⟩ := hx
    exact hxe.2
  have hcompl_ncard : ({v}ᶜ : Set V).ncard = Fintype.card V - 1 := by
    rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card]
  have hle_union : (⋃ e ∈ S, e \ {v}).ncard ≤ E.card := by
    have h1 : (⋃ e ∈ S, e \ {v}).ncard ≤ ({v}ᶜ : Set V).ncard := Set.ncard_le_ncard hsubc
    rw [hcompl_ncard, ← hdegS, ← hEcard] at h1
    exact h1
  -- each `e \ {v}` is non-empty, hence has cardinality at least one
  have hge1 : ∀ e ∈ E, 1 ≤ (e \ {v}).ncard := by
    intro e he
    have heS : e ∈ S := (hmemE e).mp he
    obtain ⟨he𝓗, hve⟩ := (hmem e).mp heS
    have h2 : 2 ≤ e.ncard := hno e he𝓗
    rw [Set.ncard_sdiff_singleton_of_mem hve]
    omega
  have hlower : E.card ≤ ∑ e ∈ E, (e \ {v}).ncard := by
    have := Finset.card_nsmul_le_sum E (fun e => (e \ {v}).ncard) 1 hge1
    simpa using this
  have hsum_le : ∑ e ∈ E, (e \ {v}).ncard ≤ E.card := by
    rw [← hcountF]; exact hle_union
  -- squeezing: the total is exactly `E.card`
  have hsum : ∑ e ∈ E, (e \ {v}).ncard = E.card := le_antisymm hsum_le hlower
  -- hence every `e \ {v}` is a singleton
  have hcardE : ∀ e ∈ E, (e \ {v}).ncard = 1 := by
    intro e he
    have hge1e : 1 ≤ (e \ {v}).ncard := hge1 e he
    by_contra hne
    have h2 : 2 ≤ (e \ {v}).ncard := by omega
    have hsplit := Finset.add_sum_erase E (fun e' => (e' \ {v}).ncard) he
    have herase_ge : (E.erase e).card ≤ ∑ e' ∈ E.erase e, (e' \ {v}).ncard := by
      have := Finset.card_nsmul_le_sum (E.erase e) (fun e' => (e' \ {v}).ncard) 1
        (fun e' he' => hge1 e' (Finset.mem_of_mem_erase he'))
      simpa using this
    have hcarte : (E.erase e).card + 1 = E.card := Finset.card_erase_add_one he
    have hpos : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
    omega
  have hcardS : ∀ e ∈ S, (e \ {v}).ncard = 1 := fun e he => hcardE e ((hmemE e).mpr he)
  -- so the union covers all of `{v}ᶜ`
  have hunion : (⋃ e ∈ S, e \ {v}) = ({v}ᶜ : Set V) := by
    apply Set.eq_of_subset_of_ncard_le hsubc
    rw [hcompl_ncard, hcountF, hsum, hEcard, hdegS]
  intro w hwv
  have hwmem : w ∈ ({v}ᶜ : Set V) := by simpa using hwv
  rw [← hunion] at hwmem
  rw [Set.mem_iUnion₂] at hwmem
  obtain ⟨e, heS, hwe⟩ := hwmem
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hcardS e heS)
  have haw : a = w := by
    have : w ∈ ({a} : Set V) := by rw [← ha]; exact hwe
    exact (Set.mem_singleton_iff.mp this).symm
  rw [haw] at ha
  have hv : v ∈ e := ((hmem e).mp heS).2
  have h1 : insert v (e \ {v}) = e := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hv]
  have heq : e = {v, w} := by
    rw [← h1, ha]
  rw [← heq]
  exact ((hmem e).mp heS).1

end Commons.Combinatorics.Hypergraph