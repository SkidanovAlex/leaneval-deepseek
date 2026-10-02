import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder

set_option maxHeartbeats 1000000

namespace Commons.Combinatorics.Hypergraph

open scoped Classical

/-- In a linear hypergraph `𝓗` (any two distinct edges meet in at most one vertex)
all of whose edges have at least two vertices, if a vertex `v` lies in exactly
`|V| - 2` edges then at most two vertices `w` fail to be joined to `v` by an edge
`{v, w}` of the hypergraph. -/
theorem ncard_notAdj_le_two_of_degree (V : Type*) [Fintype V] [DecidableEq V]
    (𝓗 : Set (Set V))
    (hlin : 𝓗.Pairwise fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton)
    (hno : ∀ e ∈ 𝓗, 2 ≤ e.ncard) {v : V}
    (hdeg : {e ∈ 𝓗 | v ∈ e}.ncard = Fintype.card V - 2) :
    {w : V | w ≠ v ∧ ({v, w} : Set V) ∉ 𝓗}.ncard ≤ 2 := by
  classical
  let ι := {e : Set V // e ∈ 𝓗 ∧ v ∈ e}
  let part : ι → Set V := fun e => (e.1 : Set V) \ {v}
  let P : ι → Prop := fun i => 2 ≤ (part i).ncard
  let S : Set V := {w : V | w ≠ v ∧ ({v, w} : Set V) ∉ 𝓗}
  have hι : Fintype.card ι = Fintype.card V - 2 := by
    have h1 : Fintype.card ι = ({e : Set V | e ∈ 𝓗 ∧ v ∈ e} : Set (Set V)).ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.card_coe_set_eq _
    rw [h1]
    convert hdeg using 2
  have hpart_ge1 : ∀ i : ι, 1 ≤ (part i).ncard := by
    intro i
    have hve : v ∈ (i.1 : Set V) := i.2.2
    have h2 : 2 ≤ (i.1 : Set V).ncard := hno i.1 i.2.1
    have h3 : (part i).ncard + 1 = (i.1 : Set V).ncard := Set.ncard_sdiff_singleton_add_one hve
    omega
  have hdisj : Pairwise (Function.onFun Disjoint part) := by
    intro i j hij
    show Disjoint (part i) (part j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    simp only [part, Set.mem_sdiff, Set.mem_singleton_iff] at hxi hxj
    obtain ⟨hxi1, hxiv⟩ := hxi
    obtain ⟨hxj1, hxjv⟩ := hxj
    have hne : (i.1 : Set V) ≠ j.1 := fun h => hij (Subtype.ext h)
    have hsub : ((i.1 : Set V) ∩ j.1).Subsingleton := hlin i.2.1 j.2.1 hne
    have hxv : x = v := hsub ⟨hxi1, hxj1⟩ ⟨i.2.2, j.2.2⟩
    exact hxiv hxv
  have hUnion_card : (⋃ i : ι, part i).ncard = ∑ i : ι, (part i).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) hdisj, finsum_eq_sum_of_fintype]
  have hUnion_sub : (⋃ i : ι, part i) ⊆ ({v}ᶜ : Set V) := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hxi⟩ := hx
    simp only [part, Set.mem_sdiff, Set.mem_singleton_iff] at hxi
    exact hxi.2
  have hcompl : ({v}ᶜ : Set V).ncard = Fintype.card V - 1 := by
    rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card]
  have hSsum_le : (∑ i : ι, (part i).ncard) ≤ Fintype.card V - 1 := by
    rw [← hUnion_card]
    calc (⋃ i : ι, part i).ncard ≤ ({v}ᶜ : Set V).ncard := Set.ncard_le_ncard hUnion_sub
      _ = Fintype.card V - 1 := hcompl
  let J := {i : ι // P i}
  let Jc := {i : ι // ¬ P i}
  have hSumsplit : (∑ i : J, (part i.1).ncard) + (∑ i : Jc, (part i.1).ncard)
      = ∑ i : ι, (part i).ncard :=
    Fintype.sum_subtype_add_sum_subtype P (fun i => (part i).ncard)
  have hSumJ_ge : Fintype.card J * 2 ≤ ∑ i : J, (part i.1).ncard := by
    calc Fintype.card J * 2 = ∑ _i : J, (2:ℕ) := by
          simp [Finset.sum_const, Finset.card_univ, mul_comm]
      _ ≤ ∑ i : J, (part i.1).ncard := Finset.sum_le_sum (fun i _ => i.2)
  have hSumJc_ge : Fintype.card Jc ≤ ∑ i : Jc, (part i.1).ncard := by
    calc Fintype.card Jc = ∑ _i : Jc, (1:ℕ) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ ≤ ∑ i : Jc, (part i.1).ncard := Finset.sum_le_sum (fun i _ => hpart_ge1 i.1)
  have hcard : Fintype.card J + Fintype.card Jc = Fintype.card ι := by
    have h := Fintype.sum_subtype_add_sum_subtype P (fun _ : ι => (1:ℕ))
    have e1 : (∑ _i : J, (1:ℕ)) = Fintype.card J := by simp [Finset.sum_const, Finset.card_univ]
    have e2 : (∑ _i : Jc, (1:ℕ)) = Fintype.card Jc := by simp [Finset.sum_const, Finset.card_univ]
    have e3 : (∑ _i : ι, (1:ℕ)) = Fintype.card ι := by simp [Finset.sum_const, Finset.card_univ]
    rw [e1, e2, e3] at h
    exact h
  have hSsum_lower : Fintype.card ι + Fintype.card J ≤ ∑ i : ι, (part i).ncard := by
    have h1 := hSumJ_ge; have h2 := hSumJc_ge; have h3 := hSumsplit; have h4 := hcard
    omega
  have hc1 : Fintype.card J ≤ 1 := by
    have h1 := hSsum_lower; have h2 := hSsum_le; have h3 := hι
    omega
  have hS_sub : S ⊆ (({v}ᶜ : Set V) \ (⋃ i : ι, part i)) ∪ (⋃ i : J, part i.1) := by
    intro w hw
    simp only [S] at hw
    obtain ⟨hwv, hwH⟩ := hw
    by_cases hmem : w ∈ ⋃ i : ι, part i
    · right
      rw [Set.mem_iUnion] at hmem ⊢
      obtain ⟨i, hwi⟩ := hmem
      have hPi : P i := by
        by_contra hnp
        have hge := hpart_ge1 i
        have hlt : (part i).ncard < 2 := not_le.mp hnp
        have hone : (part i).ncard = 1 := by omega
        obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hone
        have haeq : a = w := by
          have h2 : w = a := by
            have h3 : w ∈ ({a} : Set V) := ha ▸ hwi
            rwa [Set.mem_singleton_iff] at h3
          exact h2.symm
        have hpart_w : part i = ({w} : Set V) := by rw [haeq] at ha; exact ha
        have hv : v ∈ (i.1 : Set V) := i.2.2
        have hw_in : w ∈ (i.1 : Set V) := Set.sdiff_subset hwi
        have hEq : (i.1 : Set V) = ({v, w} : Set V) := by
          apply Set.Subset.antisymm
          · intro x hx
            by_cases hxv : x = v
            · rw [hxv]; simp
            · have hxpart : x ∈ part i := by
                simp only [part, Set.mem_sdiff, Set.mem_singleton_iff]
                exact ⟨hx, hxv⟩
              rw [hpart_w, Set.mem_singleton_iff] at hxpart
              subst hxpart
              simp
          · intro x hx
            rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with hxv | hxw
            · rwa [hxv]
            · rwa [hxw]
        exact hwH (hEq ▸ i.2.1)
      exact ⟨⟨i, hPi⟩, hwi⟩
    · left
      exact ⟨hwv, hmem⟩
  have hU2card : (⋃ i : J, part i.1).ncard = ∑ i : J, (part i.1).ncard := by
    have hdisjJ : Pairwise (Function.onFun Disjoint (fun i : J => part i.1)) := by
      intro i j hij
      exact hdisj (fun h => hij (Subtype.ext h))
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) hdisjJ, finsum_eq_sum_of_fintype]
  have hS_le : S.ncard ≤
      (Fintype.card V - 1 - (∑ i : ι, (part i).ncard)) + ∑ i : J, (part i.1).ncard := by
    calc S.ncard ≤ ((({v}ᶜ : Set V) \ (⋃ i : ι, part i)) ∪ (⋃ i : J, part i.1)).ncard :=
          Set.ncard_le_ncard hS_sub
      _ ≤ (({v}ᶜ : Set V) \ (⋃ i : ι, part i)).ncard + (⋃ i : J, part i.1).ncard :=
          Set.ncard_union_le _ _
      _ = (Fintype.card V - 1 - (∑ i : ι, (part i).ncard)) + ∑ i : J, (part i.1).ncard := by
          rw [Set.ncard_sdiff hUnion_sub, hcompl, hUnion_card, hU2card]
  have hSumJ_le : (∑ i : J, (part i.1).ncard) ≤ (∑ i : ι, (part i).ncard) - Fintype.card Jc := by
    have h1 := hSumsplit; have h2 := hSumJc_ge
    omega
  show S.ncard ≤ 2
  have h1 := hS_le; have h2 := hSumJ_le
  have h3 : Fintype.card Jc = Fintype.card ι - Fintype.card J := Fintype.card_subtype_compl P
  have h4 := hc1; have h5 := hι; have h6 := hSsum_le; have h7 := hSumsplit
  have h8 := hSumJc_ge; have h9 := hcard
  omega

end Commons.Combinatorics.Hypergraph