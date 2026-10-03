/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The conjugates of the base group by `t^u` inside an HNN extension

For the HNN extension `E = HNNExtension G A B φ` with stable letter `t = tt`, the
`t^u`-conjugate `t ^ u * of y * t ^ (-u)` of a base-group element `y` lies in the image of `G`
inside `E` exactly when `y` lies in `toSubgroup A B u` (which is `A` for `u = 1` and `B` for
`u = -1`). This is the HNN-extension analogue of the fact that the only elements of `G`
conjugated into `G` by an element of a stable letter are those in `A` (resp. `B`), and it is the
ingredient that makes the `t`-length well behaved at a step towards the stable letter.
-/
import Mathlib
import Submission.Work.ORBassSerre.HNN.Defs

namespace Work.ORBassSerre.HNN

open HNNExtension

theorem tconjMemRange {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}
    (u : ℤˣ) (y : G) :
    Work.ORBassSerre.HNN.tpow u * Work.ORBassSerre.HNN.ofE y * Work.ORBassSerre.HNN.tpow (-u) ∈
      (Work.ORBassSerre.HNN.ofE (A := A) (B := B) (φ := φ)).range ↔
      y ∈ HNNExtension.toSubgroup A B u := by
  constructor
  · -- If `t^u * of y * t^(-u) = of z`, apply the equality theorem for reduced words to the two
    -- reduced words `of 1 * (t^(-u) * of z)` and `of y * (t^(-u) * of 1)`, which represent the
    -- same element. The `head` of the first is `1`, so `w₁.head⁻¹ * w₂.head = y` is the
    -- group element sitting between the first and the second `t`-letter.
    rintro ⟨z, hz⟩
    set w₁ : RedWord (A := A) (B := B) :=
      { head := 1, toList := [(-u, z)], chain := List.isChain_singleton _ }
    set w₂ : RedWord (A := A) (B := B) :=
      { head := y, toList := [(-u, 1)], chain := List.isChain_singleton _ }
    have hprod : NormalWord.ReducedWord.prod φ w₁ = NormalWord.ReducedWord.prod φ w₂ := by
      have hz' : Work.ORBassSerre.HNN.ofE z =
          (HNNExtension.t : HNNExtension G A B φ) ^ (u : ℤ) * Work.ORBassSerre.HNN.ofE y *
            (HNNExtension.t : HNNExtension G A B φ) ^ (-(u : ℤ)) := by
        simpa [Work.ORBassSerre.HNN.tpow, Units.val_neg] using hz
      have hgz : (HNNExtension.t : HNNExtension G A B φ) ^ (-(u : ℤ)) *
            Work.ORBassSerre.HNN.ofE z =
          Work.ORBassSerre.HNN.ofE y *
            (HNNExtension.t : HNNExtension G A B φ) ^ (-(u : ℤ)) := by
        rw [hz']
        group
      simpa [NormalWord.ReducedWord.prod, w₁, w₂, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, map_one, one_mul, mul_one, Units.val_neg] using hgz
    have key := (HNNExtension.ReducedWord.map_fst_eq_and_of_prod_eq φ hprod).2
    have hmem := key (-u) (by simp [w₁])
    simpa [w₁, w₂] using hmem
  · -- Both cases are the defining relations of the HNN extension.
    intro hy
    rcases Int.units_eq_one_or u with rfl | rfl
    · have hyA : y ∈ A := by simpa using hy
      refine MonoidHom.mem_range.mpr ⟨(φ ⟨y, hyA⟩ : B), ?_⟩
      rw [Work.ORBassSerre.HNN.tpow_one, Work.ORBassSerre.HNN.tpow_neg_one,
        HNNExtension.t_mul_of ⟨y, hyA⟩, mul_assoc, mul_inv_cancel, mul_one]
    · have hyB : y ∈ B := by simpa using hy
      refine MonoidHom.mem_range.mpr ⟨(φ.symm ⟨y, hyB⟩ : A), ?_⟩
      simp only [neg_neg]
      rw [Work.ORBassSerre.HNN.tpow_neg_one, Work.ORBassSerre.HNN.tpow_one,
        HNNExtension.inv_t_mul_of ⟨y, hyB⟩, mul_assoc, inv_mul_cancel, mul_one]

end Work.ORBassSerre.HNN
