import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.Dihedral.Defs

/-!
# Abelian subgroups of a dihedral group

`Work.DSTR.dihedralAbelianRank`: every abelian subgroup of `DihedralGroup n` is cyclic or has
order at most `4`.

The argument is the classical one.  Write `DihedralGroup n` with its rotation subgroup
`⟨r⟩ = Work.Dihedral.rot n` (cyclic of order `n`) and its reflections `sr i`.

* If an abelian subgroup `A` contains no reflection then `A ≤ ⟨r⟩`, hence cyclic (a subgroup of a
  cyclic group is cyclic).
* Otherwise `A` contains a reflection `sr c`.  Then every rotation `r j ∈ A` satisfies
  `2 * j = 0` in `ZMod n` (commuting `r j` with `sr c` gives `c - j = c + j`), and every
  reflection `sr j ∈ A` satisfies `2 * (j - c) = 0` (`sr j * sr c = r (c - j)` must be a rotation
  of `A` commuting with `sr c`).  So the map
  `x ↦ (index of x, 0/1)` injects `A` into `{j : ZMod n // 2 * j = 0} × Fin 2`, and the solution
  set of `2 * j = 0` in `ZMod n` is `{0, n/2}`, of cardinality `≤ 2`.  Hence `|A| ≤ 4`.
-/

namespace Work.DSTR

open DihedralGroup

/-! ## Two elementary commutation computations in `DihedralGroup n` -/

/-- If a rotation commutes with the reflection `sr c`, then its index is killed by `2`. -/
lemma two_mul_eq_zero_of_rot_comm_sr {n : ℕ} (c j : ZMod n)
    (h : (r j : DihedralGroup n) * sr c = sr c * r j) : 2 * j = 0 := by
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h
  have h' : c - j = c + j := DihedralGroup.sr.inj h
  have hneg : -j = j := by
    apply add_left_cancel (a := c)
    simpa [sub_eq_add_neg] using h'
  have h2 : j + j = 0 := neg_eq_iff_add_eq_zero.mp hneg
  simpa [two_mul] using h2

/-- If two reflections commute, then the difference of their indices is killed by `2`. -/
lemma two_mul_sub_eq_zero_of_sr_comm_sr {n : ℕ} (c j : ZMod n)
    (h : (sr j : DihedralGroup n) * sr c = sr c * sr j) : 2 * (j - c) = 0 := by
  rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr] at h
  have h' : c - j = j - c := DihedralGroup.r.inj h
  have hneg : -(j - c) = j - c := by
    rw [neg_sub]; exact h'
  have h2 : (j - c) + (j - c) = 0 := neg_eq_iff_add_eq_zero.mp hneg
  simpa [two_mul] using h2

/-- In `ZMod n`, the solutions of `2 * j = 0` are `0` and `n / 2`. -/
lemma zmod_two_mul_eq_zero (n : ℕ) (j : ZMod n) (h : 2 * j = 0) :
    j = 0 ∨ j = ((n / 2 : ℕ) : ZMod n) := by
  have ha : -j = j := by
    have : j + j = 0 := by rw [← two_mul]; exact h
    exact neg_eq_iff_add_eq_zero.mpr this
  rcases (ZMod.neg_eq_self_iff j).mp ha with h0 | h2
  · exact Or.inl h0
  · right
    rcases eq_zero_or_neZero n with rfl | hn
    · have : j = 0 := (ZMod.val_eq_zero j).mp (by omega)
      simpa using this
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn.out
      have hval : j.val = n / 2 := by omega
      refine ZMod.val_injective n ?_
      rw [hval, ZMod.val_natCast]
      exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The set of indices in `ZMod n` killed by `2`. -/
def zmodTwoTorsion (n : ℕ) : Set (ZMod n) := {j | 2 * j = 0}

/-- The map `r j ↦ (j, 0)`, `sr j ↦ (j - c, 1)`. -/
def dihPair {n : ℕ} (c : ZMod n) : DihedralGroup n → ZMod n × Fin 2
  | .r j => (j, 0)
  | .sr j => (j - c, 1)

lemma dihPair_injective {n : ℕ} (c : ZMod n) : Function.Injective (dihPair c) := by
  intro x y h
  cases x with
  | r j =>
    cases y with
    | r k =>
      simp only [dihPair, Prod.mk.injEq] at h
      rw [h.1]
    | sr k => simp [dihPair] at h
  | sr j =>
    cases y with
    | r k => simp [dihPair] at h
    | sr k =>
      simp only [dihPair, Prod.mk.injEq] at h
      obtain ⟨h1, _⟩ := h
      rw [sub_left_inj.mp h1]

/-- `zmodTwoTorsion n` has at most two elements (it is `{0, n / 2}`). -/
lemma injective_zmodTwoTorsion_fin2 (n : ℕ) : Function.Injective
    (fun j : ↥(zmodTwoTorsion n) => if (j : ZMod n) = 0 then (0 : Fin 2) else 1) := by
  intro j k hjk
  beta_reduce at hjk
  have hj := zmod_two_mul_eq_zero n (j : ZMod n) j.2
  have hk := zmod_two_mul_eq_zero n (k : ZMod n) k.2
  by_cases hj0 : (j : ZMod n) = 0
  · have hk0 : (k : ZMod n) = 0 := by
      by_contra hk0
      rw [ite_eq_left hj0, ite_eq_right hk0] at hjk
      exact absurd hjk (by decide)
    exact Subtype.ext (by rw [hj0, hk0])
  · have hk0 : (k : ZMod n) ≠ 0 := by
      intro hk0
      rw [ite_eq_right hj0, ite_eq_left hk0] at hjk
      exact absurd hjk (by decide)
    rw [Subtype.ext_iff]
    rw [hj.resolve_left hj0, hk.resolve_left hk0]

lemma natCard_zmodTwoTorsion_le_two (n : ℕ) : Nat.card ↥(zmodTwoTorsion n) ≤ 2 := by
  have := Nat.card_le_card_of_injective _ (injective_zmodTwoTorsion_fin2 n)
  simpa using this

instance finite_zmodTwoTorsion (n : ℕ) : Finite ↥(zmodTwoTorsion n) :=
  Finite.of_injective _ (injective_zmodTwoTorsion_fin2 n)

/-- Every abelian subgroup of `DihedralGroup n` is cyclic or of order at most `4`.  Raw input of the DSTR leaves `DS3` and `DS5`. -/
theorem dihedralAbelianRank : Work.GW2.DihedralAbelianRankProp := by
  intro n A hA
  by_cases hrefl : ∃ i : ZMod n, (sr i : DihedralGroup n) ∈ A
  · -- `A` contains a reflection: bound its order by `4`.
    right
    obtain ⟨c, hc⟩ := hrefl
    have hrot : ∀ j : ZMod n, (r j : DihedralGroup n) ∈ A → 2 * j = 0 := by
      intro j hj
      have h1 := hA.is_comm.comm (⟨r j, hj⟩ : ↥A) ⟨sr c, hc⟩
      exact two_mul_eq_zero_of_rot_comm_sr c j (by simpa using congrArg Subtype.val h1)
    have href : ∀ j : ZMod n, (sr j : DihedralGroup n) ∈ A → 2 * (j - c) = 0 := by
      intro j hj
      have h1 := hA.is_comm.comm (⟨sr j, hj⟩ : ↥A) ⟨sr c, hc⟩
      exact two_mul_sub_eq_zero_of_sr_comm_sr c j (by simpa using congrArg Subtype.val h1)
    have hmem : ∀ x : DihedralGroup n, x ∈ A → (dihPair c x).1 ∈ zmodTwoTorsion n := by
      intro x hx
      cases x with
      | r j => exact hrot j hx
      | sr j => exact href j hx
    let F : ↥A → ↥(zmodTwoTorsion n) × Fin 2 := fun a =>
      (⟨(dihPair c (a : DihedralGroup n)).1, hmem a.1 a.2⟩,
        (dihPair c (a : DihedralGroup n)).2)
    have hF : Function.Injective F := by
      intro a b hab
      have h1 : (F a).1 = (F b).1 := congrArg Prod.fst hab
      have h2 : (F a).2 = (F b).2 := congrArg Prod.snd hab
      have h3 : dihPair c (a : DihedralGroup n) = dihPair c (b : DihedralGroup n) :=
        Prod.ext (Subtype.ext_iff.mp h1) h2
      exact Subtype.ext (dihPair_injective c h3)
    have hcard : Nat.card ↥A ≤ Nat.card ↥(zmodTwoTorsion n) * 2 := by
      have := Nat.card_le_card_of_injective F hF
      rw [Nat.card_prod] at this
      simpa using this
    calc Nat.card ↥A ≤ Nat.card ↥(zmodTwoTorsion n) * 2 := hcard
      _ ≤ 2 * 2 := Nat.mul_le_mul_right 2 (natCard_zmodTwoTorsion_le_two n)
      _ = 4 := by norm_num
  · -- `A` contains no reflection, so `A ≤ ⟨r⟩` is cyclic.
    left
    have hle : A ≤ Work.Dihedral.rot n := by
      intro x hx
      by_contra hxr
      rw [Work.Dihedral.notMem_rot] at hxr
      obtain ⟨i, hi⟩ := hxr
      exact hrefl ⟨i, hi ▸ hx⟩
    exact Subgroup.isCyclic_of_le hle

end Work.DSTR
