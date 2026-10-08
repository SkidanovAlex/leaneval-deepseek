import Mathlib

namespace Work.L2F.Dihedral

/-- The two-torsion of `ZMod m`: an element `t` with `t + t = 0` is either `0` or the
"half" element `m / 2` (in particular, when `m` is odd only `0` occurs, while for even `m`
the two-torsion is `{0, m / 2}`). -/
lemma zmod_add_self_eq_zero_or_eq_half {m : ℕ} (t : ZMod m) (h : t + t = 0) :
    t = 0 ∨ t = ((m / 2 : ℕ) : ZMod m) := by
  have hneg : -t = t := by rwa [neg_eq_iff_add_eq_zero]
  rcases (ZMod.neg_eq_self_iff t).mp hneg with h0 | h2
  · exact Or.inl h0
  · -- `2 * t.val = m`, so `t.val = m / 2` (and `m = 0` forces `t = 0`).
    rcases eq_or_ne m 0 with rfl | hm
    · left
      have ht : t.val = 0 := by omega
      exact (ZMod.val_eq_zero t).mp ht
    · right
      have : NeZero m := ⟨hm⟩
      have hval : m / 2 = t.val := by omega
      rw [← ZMod.natCast_zmod_val t, hval]

lemma centralizer_sr_subset {m : ℕ} {i : ZMod m} {x : DihedralGroup m}
    (hx : x ∈ Subgroup.centralizer ({DihedralGroup.sr i} : Set (DihedralGroup m))) :
    x ∈ ({1, DihedralGroup.r ((m / 2 : ℕ) : ZMod m), DihedralGroup.sr i,
        DihedralGroup.sr (i + ((m / 2 : ℕ) : ZMod m))} : Set (DihedralGroup m)) := by
  -- `x` commutes with the reflection `sr i`.
  have hcomm : DihedralGroup.sr i * x = x * DihedralGroup.sr i :=
    hx (DihedralGroup.sr i) (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases x with k | k
  · -- `x = r k`: from `sr i * r k = r k * sr i` we get `i + k = i - k`, i.e. `k = -k`.
    have h1 : i + k = i - k := by simpa using hcomm
    have hk : k = -k := by
      have h1' : i + k = i + (-k) := by simpa [sub_eq_add_neg] using h1
      exact add_left_cancel h1'
    have hkk : k + k = 0 := (eq_neg_iff_add_eq_zero).mp hk
    rcases zmod_add_self_eq_zero_or_eq_half k hkk with h0 | h2
    · left; rw [h0]; rfl
    · right; left; rw [h2]
  · -- `x = sr k`: from `sr i * sr k = sr k * sr i` we get `k - i = i - k = -(k - i)`.
    have h1 : k - i = i - k := by simpa using hcomm
    have ht : k - i = -(k - i) := h1.trans (neg_sub k i).symm
    have htt : (k - i) + (k - i) = 0 := (eq_neg_iff_add_eq_zero).mp ht
    rcases zmod_add_self_eq_zero_or_eq_half (k - i) htt with h0 | h2
    · right; right; left
      rw [sub_eq_zero.mp h0]
    · right; right; right
      rw [sub_eq_iff_eq_add.mp h2, add_comm]

end Work.L2F.Dihedral
