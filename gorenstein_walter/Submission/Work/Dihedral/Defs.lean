/-
# Dihedral 2-group combinatorics (area A1 of the Gorenstein–Walter development)

`DihedralGroup n` (Mathlib) has order `2n`, with elements `r i`, `sr i` for `i : ZMod n`.

Conventions and interface used by the rest of `Work.Dihedral`:

* `Work.Dihedral.rot n` is the rotation subgroup `⟨r⟩ ≤ DihedralGroup n`;
* `Work.Dihedral.rotHom n : Multiplicative (ZMod n) →* DihedralGroup n` is `i ↦ r i`;
* `Work.Dihedral.rotEquiv n : Multiplicative (ZMod n) ≃* rot n`;
* `Work.Dihedral.maxSub0/maxSub1 n` are the two non-rotation maximal subgroups
  `⟨r 2, sr 0⟩`, `⟨r 2, sr 1⟩` of `DihedralGroup (2^k)`;
* `Work.Dihedral.centerElem k` is the unique involution `r (2^(k-1))` of the rotation subgroup of
  `DihedralGroup (2^k)`.
-/
import Mathlib

namespace Work.Dihedral

open DihedralGroup

variable {n : ℕ}

/-! ## The rotation subgroup `⟨r⟩` -/

/-- `i ↦ r i` as a homomorphism `Multiplicative (ZMod n) →* DihedralGroup n`. -/
def rotHom (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun i := r (Multiplicative.toAdd i)
  map_one' := rfl
  map_mul' i j := by rw [r_mul_r]; rfl

@[simp] lemma rotHom_apply (n : ℕ) (i : Multiplicative (ZMod n)) :
    rotHom n i = r (Multiplicative.toAdd i) := rfl

lemma rotHom_injective (n : ℕ) : Function.Injective (rotHom n) := by
  intro i j h
  rw [rotHom_apply, rotHom_apply] at h
  exact Multiplicative.toAdd.injective (DihedralGroup.r.inj h)

/-- The rotation subgroup `⟨r⟩` of `DihedralGroup n`. -/
def rot (n : ℕ) : Subgroup (DihedralGroup n) := (rotHom n).range

lemma mem_rot {x : DihedralGroup n} : x ∈ rot n ↔ ∃ i : ZMod n, x = r i := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨Multiplicative.toAdd i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd i, rfl⟩

lemma eq_r_or_sr (x : DihedralGroup n) : (∃ i : ZMod n, x = r i) ∨ ∃ i : ZMod n, x = sr i := by
  cases x with
  | r i => exact Or.inl ⟨i, rfl⟩
  | sr i => exact Or.inr ⟨i, rfl⟩

lemma sr_ne_r (i j : ZMod n) : (sr i : DihedralGroup n) ≠ r j := by
  intro h
  injection h

lemma notMem_rot {x : DihedralGroup n} : x ∉ rot n ↔ ∃ i : ZMod n, x = sr i := by
  rw [mem_rot]
  constructor
  · intro h
    rcases eq_r_or_sr x with ⟨i, hi⟩ | hsr
    · exact absurd ⟨i, hi⟩ h
    · exact hsr
  · rintro ⟨i, rfl⟩ ⟨j, hj⟩
    exact sr_ne_r i j hj

@[simp] lemma r_mem_rot (i : ZMod n) : (r i : DihedralGroup n) ∈ rot n := mem_rot.mpr ⟨i, rfl⟩

@[simp] lemma sr_notMem_rot (i : ZMod n) : (sr i : DihedralGroup n) ∉ rot n :=
  notMem_rot.mpr ⟨i, rfl⟩

lemma rot_eq_zpowers_r_one (n : ℕ) [NeZero n] :
    rot n = Subgroup.zpowers (r (1 : ZMod n) : DihedralGroup n) := by
  ext x
  rw [mem_rot, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨(i.val : ℤ), ?_⟩
    rw [r_zpow, one_mul]
    congr 1
    push_cast
    exact ZMod.natCast_zmod_val i
  · rintro ⟨k, hk⟩
    exact ⟨(k : ZMod n), by rw [← hk, r_zpow, one_mul]⟩

lemma nat_card_rot [NeZero n] : Nat.card (rot n) = n := by
  rw [rot_eq_zpowers_r_one, Nat.card_zpowers, orderOf_r_one]

instance instIsCyclicRot (n : ℕ) : IsCyclic (rot n) :=
  isCyclic_of_surjective (rotHom n).rangeRestrict (rotHom n).rangeRestrict_surjective

variable (n) in
/-- `Multiplicative (ZMod n) ≃* ⟨r⟩`. -/
noncomputable def rotEquiv : Multiplicative (ZMod n) ≃* rot n :=
  MulEquiv.ofBijective ((rotHom n).rangeRestrict) (by
    refine ⟨fun i j h => rotHom_injective n (congrArg Subtype.val h),
      (rotHom n).rangeRestrict_surjective⟩)

@[simp] lemma rotEquiv_apply (i : Multiplicative (ZMod n)) :
    (rotEquiv n i : DihedralGroup n) = r (Multiplicative.toAdd i) := rfl

@[simp] lemma coe_rotEquiv_symm (i : ZMod n) :
    ((rotEquiv n).symm ⟨r i, r_mem_rot i⟩ : Multiplicative (ZMod n)) =
      Multiplicative.ofAdd i := by
  apply (rotEquiv n).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

/-! ## Multiplication rules for `r` and `sr` -/

lemma sr_mul_sr_mem_rot (i j : ZMod n) : sr i * sr j ∈ rot n := by
  rw [sr_mul_sr]; exact r_mem_rot _

lemma sr_mul_r_mem_notMem (i j : ZMod n) : sr i * r j ∉ rot n := by
  rw [sr_mul_r]; exact sr_notMem_rot _

lemma r_mul_sr_mem_notMem (i j : ZMod n) : r i * sr j ∉ rot n := by
  rw [r_mul_sr]; exact sr_notMem_rot _

/-! ## Conjugation action on the reflections -/

/-- Conjugation by `r t` acts on the reflections by `sr i ↦ sr (i - 2 * t)`. -/
lemma r_conj_sr (t i : ZMod n) :
    (r t : DihedralGroup n) * sr i * (r t)⁻¹ = sr (i - 2 * t) := by
  rw [inv_r, r_mul_sr, sr_mul_r]
  congr 1
  ring

/-- Conjugation by an element outside `⟨r⟩` fixes the reflections. -/
lemma sr_conj_sr (t i : ZMod n) :
    (sr t : DihedralGroup n) * sr i * (sr t)⁻¹ = sr (2 * t - i) := by
  rw [inv_sr, sr_mul_sr, r_mul_sr]
  congr 1
  ring

/-- `rot n` is normal in `DihedralGroup n`. -/
lemma rot_normal (n : ℕ) : (rot n).Normal where
  conj_mem := by
    intro x hx g
    rcases eq_r_or_sr x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases eq_r_or_sr g with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · rw [r_mul_r, inv_r, r_mul_r]; exact r_mem_rot _
      · rw [sr_mul_r, inv_sr, sr_mul_sr]; exact r_mem_rot _
    · exact absurd hx (sr_notMem_rot i)

/-! ## The three maximal subgroups -/

/-- The subgroup `⟨r 2, sr 0⟩`. -/
def maxSub0 (n : ℕ) : Subgroup (DihedralGroup n) :=
  Subgroup.closure ({r (2 : ZMod n), sr (0 : ZMod n)} : Set (DihedralGroup n))

/-- The subgroup `⟨r 2, sr 1⟩`. -/
def maxSub1 (n : ℕ) : Subgroup (DihedralGroup n) :=
  Subgroup.closure ({r (2 : ZMod n), sr (1 : ZMod n)} : Set (DihedralGroup n))

lemma maxSub0_le (n : ℕ) : maxSub0 n ≤ rot n ⊔ Subgroup.zpowers (sr (0 : ZMod n)) := by
  rw [maxSub0, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_sup_left (r_mem_rot _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

lemma maxSub1_le (n : ℕ) : maxSub1 n ≤ rot n ⊔ Subgroup.zpowers (sr (1 : ZMod n)) := by
  rw [maxSub1, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.mem_sup_left (r_mem_rot _)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

/-- The unique involution `r (2^(k-1))` in the rotation subgroup of `DihedralGroup (2^k)`. -/
def centerElem (k : ℕ) : DihedralGroup (2 ^ k) :=
  r (((2 ^ (k - 1) : ℕ)) : ZMod (2 ^ k))

@[simp] lemma centerElem_def (k : ℕ) :
    centerElem k = (r (((2 ^ (k - 1) : ℕ)) : ZMod (2 ^ k)) : DihedralGroup (2 ^ k)) := rfl

end Work.Dihedral
