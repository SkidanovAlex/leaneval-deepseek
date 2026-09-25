import Mathlib

namespace Work.LT

/-- In `ZMod 2` the only nonzero element is `1`. -/
private lemma zmodTwo_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  have hlt := ZMod.val_lt x
  have h0 : x.val ≠ 0 := fun hh => h ((ZMod.val_eq_zero x).mp hh)
  have h1 : x.val = 1 := by omega
  calc x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    _ = ((1 : ℕ) : ZMod 2) := by rw [h1]
    _ = 1 := by norm_num

/-- The support (set of nonzero coordinates) of the indicator function of a finset is that
finset. -/
private lemma zmodTwo_support_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) :
    Finset.univ.filter (fun i => (if i ∈ s then (1 : ZMod 2) else 0) ≠ 0) = s := by
  ext i
  by_cases h : i ∈ s <;> simp [h]

/-- The number of vectors `v : ι → ZMod 2` of Hamming weight at most `w` equals `∑_{k=0}^{w} (|ι| choose k)`. -/
theorem gb_count_card_eq_sum_choose {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℕ) :
    (Finset.univ.filter (fun v : ι → ZMod 2 => hammingNorm v ≤ w)).card =
      ∑ k ∈ Finset.range (w + 1), (Fintype.card ι).choose k := by
  -- Step 1: a vector over `ZMod 2` is determined by its support, and every support occurs.
  have h1 : (Finset.univ.filter (fun v : ι → ZMod 2 => hammingNorm v ≤ w)).card
      = (Finset.univ.filter (fun s : Finset ι => s.card ≤ w)).card := by
    refine Finset.card_bij (fun v _ => Finset.univ.filter (fun i => v i ≠ 0)) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv
    · intro v1 _ v2 _ heq
      funext i
      have hiff : (v1 i ≠ 0) ↔ (v2 i ≠ 0) := by
        have := congrArg (fun (s : Finset ι) => i ∈ s) heq
        simpa [Finset.mem_filter] using this
      by_cases h : v1 i = 0
      · have h2 : v2 i = 0 := by
          by_contra hv2
          exact (hiff.mpr hv2) h
        rw [h, h2]
      · rw [zmodTwo_eq_one_of_ne_zero h, zmodTwo_eq_one_of_ne_zero (hiff.mp h)]
    · intro s hs
      refine ⟨fun i => if i ∈ s then 1 else 0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        rw [show hammingNorm (fun i => if i ∈ s then (1 : ZMod 2) else 0)
              = (Finset.univ.filter
                  (fun i => (if i ∈ s then (1 : ZMod 2) else 0) ≠ 0)).card from rfl,
            zmodTwo_support_indicator s]
        exact hs
      · exact zmodTwo_support_indicator s
  -- Step 2: the subsets of `ι` of size at most `w` are the disjoint union, over `k ≤ w`, of
  -- the subsets of size exactly `k`, which number `(|ι| choose k)`.
  have h2 : (Finset.univ.filter (fun s : Finset ι => s.card ≤ w)).card
      = ∑ k ∈ Finset.range (w + 1), (Fintype.card ι).choose k := by
    have hU : (Finset.univ : Finset (Finset ι)) = (Finset.univ : Finset ι).powerset := by
      ext s; simp [Finset.mem_powerset]
    rw [hU]
    have hdisj : (↑(Finset.range (w + 1)) : Set ℕ).PairwiseDisjoint
        (fun k => (Finset.univ : Finset ι).powersetCard k) :=
      ((Finset.univ : Finset ι).pairwise_disjoint_powersetCard.set_pairwise _)
    have hEq : (Finset.univ : Finset ι).powerset.filter (fun s => s.card ≤ w)
        = (Finset.range (w + 1)).disjiUnion
            (fun k => (Finset.univ : Finset ι).powersetCard k) hdisj := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_disjiUnion,
        Finset.mem_range, Finset.mem_powersetCard, Finset.mem_powerset]
      constructor
      · rintro ⟨-, hs⟩
        exact ⟨s.card, Nat.lt_succ_of_le hs, Finset.subset_univ s, rfl⟩
      · rintro ⟨k, hk, hsk, hcard⟩
        exact ⟨hsk, by rw [hcard]; exact Nat.lt_succ_iff.mp hk⟩
    rw [hEq, Finset.card_disjiUnion]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [h1, h2]

end Work.LT
