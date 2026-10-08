import Mathlib
import Submission.Work.Dihedral.Defs
import Submission.Work.CORE4.L2PAux.v2_four_closure_pair

/-!
# A non-cyclic `2`-subgroup of a dihedral group contains a Klein four-subgroup

Let `Q ≤ DihedralGroup n` be a `2`-group which is not cyclic.  We show that `Q` contains a
subgroup `W` of order `4` all of whose elements are involutions.

The argument is purely about the dihedral structure `D_n = ⟨r, s | s² = 1, s r s = r⁻¹⟩`:

* `Q` cannot be contained in the cyclic rotation subgroup `⟨r⟩` (a subgroup of a cyclic group is
  cyclic), so we may choose a reflection `s ∈ Q \ ⟨r⟩`; then `s² = 1`.
* Writing `R = Q ⊓ ⟨r⟩`, the decomposition `Q = R ∪ s·R` holds, so `R = ⊥` would force
  `Q ≤ ⟨s⟩`, i.e. `Q` cyclic — a contradiction.  Hence `R ≠ ⊥`.
* As `R` is a subgroup of the `2`-group `Q`, it is a `2`-group; being nontrivial it has a nontrivial
  element and hence an involution `ζ ∈ R`.
* The reflection `s` inverts the rotations, so it inverts `ζ`; as `ζ² = 1` it centralizes `ζ`.
  Thus `⟨ζ, s⟩ ≤ Q` is a Klein four-subgroup, by `v2_four_closure_pair`.
-/

namespace Work.CORE4.L2PAux

open Work.Dihedral

/-- Conjugation by a reflection inverts a rotation of `DihedralGroup n`. -/
private lemma v2_sr_conj_rot_eq_inv {n : ℕ} (t : ZMod n) {x : DihedralGroup n}
    (hx : x ∈ rot n) : (DihedralGroup.sr t) * x * (DihedralGroup.sr t)⁻¹ = x⁻¹ := by
  obtain ⟨j, rfl⟩ := mem_rot.mp hx
  rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
    DihedralGroup.inv_r]
  congr 1
  ring

/-- In a `2`-group, every nontrivial element has a power which is a nontrivial involution. -/
private lemma v2_exists_involution_of_pow_eq_one {G : Type*} [Group G] (h : IsPGroup 2 G)
    (x : G) (hx : x ≠ 1) : ∃ y : G, y ^ 2 = 1 ∧ y ≠ 1 := by
  classical
  have hx' : ∃ k : ℕ, x ^ 2 ^ k = 1 := h x
  let k := Nat.find hx'
  have hk : x ^ 2 ^ k = 1 := Nat.find_spec hx'
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, pow_one] at hk
      exact absurd hk hx
    · exact h0
  have hkmin : x ^ 2 ^ (k - 1) ≠ 1 := fun hc =>
    Nat.find_min hx' (by omega : k - 1 < k) hc
  refine ⟨x ^ 2 ^ (k - 1), ?_, hkmin⟩
  rw [← pow_mul]
  have hpow : 2 ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow, hk]

theorem v2_dihedral_two_subgroup_has_four {n : ℕ} (Q : Subgroup (DihedralGroup n))
    (hQ : IsPGroup 2 Q) (hnc : ¬ IsCyclic Q) :
    ∃ W : Subgroup (DihedralGroup n), W ≤ Q ∧ Nat.card W = 4 ∧ ∀ w ∈ W, w ^ 2 = 1 := by
  classical
  -- `Q` is not contained in the cyclic rotation subgroup.
  have hnotle : ¬ Q ≤ rot n := by
    intro hle
    exact hnc (isCyclic_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  -- Pick a reflection `s` in `Q`.
  obtain ⟨s, hsQ, hsnotrot⟩ : ∃ s ∈ Q, s ∉ rot n := by
    by_contra hcon
    exact hnotle fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩
  obtain ⟨i, hi⟩ := notMem_rot.mp hsnotrot
  have hs2 : s ^ 2 = 1 := by rw [hi, pow_two, DihedralGroup.sr_mul_self]
  have hs22 : s * s = 1 := by simpa [pow_two] using hs2
  have hs1 : s ≠ 1 := fun h => hsnotrot (h ▸ Subgroup.one_mem _)
  -- The rotation part `Q ⊓ ⟨r⟩` is nontrivial, else `Q ≤ ⟨s⟩` would be cyclic.
  have hRne : Q ⊓ rot n ≠ ⊥ := by
    intro hbot
    have hQle : Q ≤ Subgroup.zpowers s := by
      have hd : Q ≤ (Q ⊓ rot n) ⊔ Subgroup.zpowers s := by
        intro x hx
        by_cases hxr : x ∈ rot n
        · exact Subgroup.mem_sup_left ⟨hx, hxr⟩
        · obtain ⟨j, hj⟩ := notMem_rot.mp hxr
          have hmem : s * x ∈ Q ⊓ rot n :=
            ⟨mul_mem hsQ hx, by rw [hi, hj, DihedralGroup.sr_mul_sr]; exact r_mem_rot _⟩
          have hxs : x = s * (s * x) := by rw [← mul_assoc, hs22, one_mul]
          rw [hxs]
          exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
            (Subgroup.mem_sup_left hmem)
      rwa [hbot, bot_sup_eq] at hd
    exact hnc (isCyclic_of_injective (Subgroup.inclusion hQle)
      (Subgroup.inclusion_injective hQle))
  have hR2 : IsPGroup 2 ↥(Q ⊓ rot n) := hQ.to_le inf_le_left
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  -- An involution `y` in the rotation part, coerced to `DihedralGroup n`.
  obtain ⟨y, hy2, hy1⟩ := v2_exists_involution_of_pow_eq_one hR2 z hz1
  have hζ2 : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) ^ 2 = 1 := by
    simpa using congrArg (Subgroup.subtype (Q ⊓ rot n)) hy2
  have hζ1 : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) ≠ 1 :=
    fun h => hy1 (Subtype.ext h)
  have hζQ : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) ∈ Q := (y : ↥(Q ⊓ rot n)).2.1
  have hζrot : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) ∈ rot n := (y : ↥(Q ⊓ rot n)).2.2
  -- The reflection `s` inverts the involution `ζ`, hence centralizes it.
  have hconj : s * ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) * s⁻¹
      = ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) := by
    rw [hi, v2_sr_conj_rot_eq_inv i hζrot]
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hζ2)
  have hcomm : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) * s
      = s * ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) := by
    have h : (s * ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) * s⁻¹) * s
        = ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) * s := by rw [hconj]
    rw [mul_assoc, inv_mul_cancel, mul_one] at h
    exact h.symm
  have hζs : ((y : ↥(Q ⊓ rot n)) : DihedralGroup n) ≠ s := fun h => hsnotrot (h ▸ hζrot)
  obtain ⟨hcard, hsq⟩ :=
    v2_four_closure_pair _ _ hζ2 hs2 hcomm hζ1 hs1 hζs
  exact ⟨Subgroup.closure ({((y : ↥(Q ⊓ rot n)) : DihedralGroup n), s} : Set (DihedralGroup n)),
    by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hζQ
      · exact hsQ,
    hcard, hsq⟩

end Work.CORE4.L2PAux
