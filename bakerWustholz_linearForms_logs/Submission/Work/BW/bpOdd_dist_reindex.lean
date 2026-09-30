import Mathlib
import Submission.Work.BW.bpOddDefs
import Submission.Work.BW.bpOddL1_reindex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Split the product over the `d`-range `Icc (-P) Q` (with `0` erased) into its positive part
`1 ≤ d ≤ Q` and negative part `-(P) ≤ d ≤ -1`; the two intervals are disjoint. -/
lemma bpOdd_split_erase {η : ℝ} (P Q : ℕ) :
    ∏ d ∈ (Finset.Icc (-(P:ℤ)) (Q:ℤ)).erase 0, (2*|(d:ℝ)| - η)
      = (∏ d ∈ Finset.Icc (1:ℤ) (Q:ℤ), (2*|(d:ℝ)| - η))
        * (∏ d ∈ Finset.Icc (-(P:ℤ)) (-1:ℤ), (2*|(d:ℝ)| - η)) := by
  have hset : (Finset.Icc (-(P:ℤ)) (Q:ℤ)).erase 0
      = Finset.Icc (1:ℤ) (Q:ℤ) ∪ Finset.Icc (-(P:ℤ)) (-1:ℤ) := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨hd0, h1, h2⟩
      rcases lt_or_gt_of_ne hd0 with h | h
      · right; omega
      · left; omega
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, by omega, h2⟩
      · exact ⟨by omega, h1, by omega⟩
  have hdisj : Disjoint (Finset.Icc (1:ℤ) (Q:ℤ)) (Finset.Icc (-(P:ℤ)) (-1:ℤ)) := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hset, Finset.prod_union hdisj]

/-- The positive half: reindexing `d ∈ Icc 1 Q` by `d = t+1` gives `∏_{t<Q}(2t+2-η)`. -/
lemma bpOdd_pos_range {η : ℝ} (Q : ℕ) :
    (∏ d ∈ Finset.Icc (1:ℤ) (Q:ℤ), (2*|(d:ℝ)| - η))
      = ∏ t ∈ Finset.range Q, (2*(t:ℝ) + 2 - η) := by
  refine Finset.prod_bij' (fun d _ => (d - 1).toNat) (fun t _ => (t:ℤ) + 1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [Finset.mem_range]
    have hto : (((d - 1).toNat : ℤ)) = d - 1 := Int.toNat_of_nonneg (by omega)
    have : (((d - 1).toNat : ℤ)) < (Q:ℤ) := by omega
    exact_mod_cast this
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_Icc]
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    have hto : (((d - 1).toNat : ℤ)) = d - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · intro t ht
    simp only [Finset.mem_range] at ht
    rw [show ((t:ℤ) + 1 - 1) = (t:ℤ) by ring, Int.toNat_natCast]
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    have hto : (((d - 1).toNat : ℤ)) = d - 1 := Int.toNat_of_nonneg (by omega)
    have hcast : ((d - 1).toNat : ℝ) = (d:ℝ) - 1 := by
      rw [← Int.cast_natCast (R := ℝ), hto]
      push_cast
      ring
    have hdpos : (0:ℝ) ≤ (d:ℝ) := by
      have : (0:ℤ) ≤ d := by omega
      exact_mod_cast this
    rw [hcast, abs_of_nonneg hdpos]
    ring

/-- The negative half: `d ∈ Icc (-(P)) (-1)` maps to `Icc 1 P` by `d ↦ -d`, reducing to the
positive half. -/
lemma bpOdd_neg_range {η : ℝ} (P : ℕ) :
    (∏ d ∈ Finset.Icc (-(P:ℤ)) (-1:ℤ), (2*|(d:ℝ)| - η))
      = ∏ t ∈ Finset.range P, (2*(t:ℝ) + 2 - η) := by
  rw [← bpOdd_pos_range (η := η) P]
  refine Finset.prod_bij' (fun d _ => -d) (fun d _ => -d) ?_ ?_ ?_ ?_ ?_
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd; ring
  · intro d hd; ring
  · intro d hd; simp only [Int.cast_neg, abs_neg]

/-- Reindexing the product of distances: with `l = 2i₀+1`, `−m ≤ i₀ ≤ m−1`, the map
`k ↦ (k−l)/2` is a bijection from `(oddIdx (2m)).erase l` onto `(Icc (−P) Q).erase 0`,
`P = m+i₀`, `Q = m−1−i₀`, sending `|k − l|` to `2|d|`; splitting the `d > 0` from the `d < 0`
half (reindexing `d ↦ −d`) and shifting `d ↦ d+1` turns it into `bpG η P Q`. -/
theorem bpOdd_dist_reindex {η : ℝ} {m : ℕ} (hm : 1 ≤ m) {i₀ : ℤ} (hi : -(m:ℤ) ≤ i₀)
    (hi' : i₀ ≤ (m:ℤ) - 1) :
    bpG η (((m:ℤ) - 1 - i₀).toNat) (((m:ℤ) + i₀).toNat)
      = ∏ k ∈ (oddIdx (2*m)).erase (2*i₀+1), (|(k:ℝ) - ((2*i₀+1 : ℤ) : ℝ)| - η) := by
  rw [bpOddL1_reindex hm hi hi']
  rw [bpOdd_split_erase]
  rw [bpOdd_pos_range (η := η), bpOdd_neg_range (η := η)]
  unfold bpG
  rfl

end Work.BW
