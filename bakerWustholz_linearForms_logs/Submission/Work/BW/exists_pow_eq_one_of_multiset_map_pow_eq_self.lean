import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem exists_pow_eq_one_of_multiset_map_pow_eq_self {t : Multiset ℂ} {p : ℕ} (hp : 1 < p)
    (h : t.map (fun z => z ^ p) = t) {z : ℂ} (hz : z ∈ t) (hz0 : z ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  classical
  -- if an element lies in t then so does its p-th power
  have hclos : ∀ a ∈ t, a ^ p ∈ t := by
    intro a ha
    rw [← h]
    exact Multiset.mem_map.mpr ⟨a, ha, rfl⟩
  -- all iterates of the p-th power map applied to z remain in t
  have hmem : ∀ k : ℕ, z ^ (p ^ k) ∈ t := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
      have heq : z ^ (p ^ (k + 1)) = (z ^ (p ^ k)) ^ p := by
        rw [pow_succ, pow_mul]
      rw [heq]
      exact hclos _ ih
  -- finiteness: two distinct iterates coincide
  obtain ⟨x, hx, y, hy, hxy, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (t.card + 1)) (t := t.toFinset)
      (f := fun k => z ^ (p ^ k))
      (by rw [Finset.card_range]
          exact lt_of_le_of_lt (Multiset.toFinset_card_le t) (Nat.lt_succ_self t.card))
      (fun k _ => Multiset.mem_toFinset.mpr (hmem k))
  have hij : min x y < max x y := min_lt_max.mpr hxy
  have hfij : z ^ (p ^ min x y) = z ^ (p ^ max x y) := by
    rcases le_total x y with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]; exact hf
    · rw [min_eq_right hle, max_eq_left hle]; exact hf.symm
  refine ⟨p ^ max x y - p ^ min x y, Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hp hij), ?_⟩
  have hle : p ^ min x y ≤ p ^ max x y :=
    Nat.pow_le_pow_right (by omega) min_le_max
  have key : z ^ (p ^ max x y) = z ^ (p ^ min x y) * z ^ (p ^ max x y - p ^ min x y) := by
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_cancel' hle).symm
  have ha : z ^ (p ^ min x y) ≠ 0 := pow_ne_zero _ hz0
  have hmul : z ^ (p ^ min x y) * z ^ (p ^ max x y - p ^ min x y) =
      z ^ (p ^ min x y) * 1 := by
    rw [← key, mul_one]
    exact hfij.symm
  exact mul_left_cancel₀ ha hmul

end Work.BW
