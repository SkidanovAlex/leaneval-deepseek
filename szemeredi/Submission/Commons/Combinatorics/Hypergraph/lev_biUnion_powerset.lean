import Mathlib.Data.Finset.Powerset

namespace Commons.Combinatorics.Hypergraph

/-- The core computation: first taking the `n`-smaller subsets of `e`, then the `1`-smaller
subsets of those, is the same as taking the `(n+1)`-smaller subsets of `e`. -/
private lemma powerset_filter_step {ι : Type*} [DecidableEq ι] (e : Finset ι) (n : ℕ) :
    (e.powerset.filter (fun f => f.card + n = e.card)).biUnion
        (fun f => f.powerset.filter (fun g => g.card + 1 = f.card))
      = e.powerset.filter (fun g => g.card + (n + 1) = e.card) := by
  ext g
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨f, ⟨hfsub, hfcard⟩, gsub, gcard⟩
    exact ⟨gsub.trans hfsub, by omega⟩
  · rintro ⟨gsub, gcard⟩
    have hlt : g.card < e.card := by omega
    obtain ⟨x, hxe, hxg⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨insert x g, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Finset.insert_subset_iff.mpr ⟨hxe, gsub⟩
    · rw [Finset.card_insert_of_notMem hxg]; omega
    · intro y hy; exact Finset.mem_insert.mpr (Or.inr hy)
    · rw [Finset.card_insert_of_notMem hxg]

/-- Base case: taking the `0`-smaller subsets of every member of `Hd` recovers `Hd`. -/
private lemma biUnion_powerset_zero {ι : Type*} [DecidableEq ι] (Hd : Finset (Finset ι)) :
    Hd.biUnion (fun e => e.powerset.filter (fun f => f.card + 0 = e.card)) = Hd := by
  apply Finset.Subset.antisymm
  · intro g hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨e, heH, hge⟩ := hg
    rw [Finset.mem_filter, Finset.mem_powerset] at hge
    have hge' : g = e := Finset.eq_of_subset_of_card_le hge.1 (by omega)
    rw [hge']
    exact heH
  · intro g hg
    rw [Finset.mem_biUnion]
    refine ⟨g, hg, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl g, by omega⟩

theorem lev_biUnion_powerset {ι : Type*} [DecidableEq ι] (Hd : Finset (Finset ι)) (n : ℕ) :
    Nat.rec Hd (fun _ H => H.biUnion (fun e => e.powerset.filter (fun f => f.card + 1 = e.card))) n
      = Hd.biUnion (fun e => e.powerset.filter (fun f => f.card + n = e.card)) := by
  induction n with
  | zero =>
    change Hd = Hd.biUnion (fun e => e.powerset.filter (fun f => f.card + 0 = e.card))
    exact (biUnion_powerset_zero Hd).symm
  | succ n ih =>
    change (@Nat.rec (fun _ => Finset (Finset ι)) Hd
              (fun _ (H : Finset (Finset ι)) =>
                H.biUnion (fun e => e.powerset.filter (fun f => f.card + 1 = e.card))) n).biUnion
        (fun e => e.powerset.filter (fun f => f.card + 1 = e.card))
        = Hd.biUnion (fun e => e.powerset.filter (fun f => f.card + (n + 1) = e.card))
    rw [ih, Finset.biUnion_biUnion]
    apply Finset.biUnion_congr rfl
    intro a _
    exact powerset_filter_step a n

end Commons.Combinatorics.Hypergraph