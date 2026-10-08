/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.Deps

/-!
# The quadratic conjugation identity `ConjNormalQuadratic`

Setting `H := U.map (QuotientGroup.mk' V)` (the image of the normal subgroup `U` in `M ⧸ V`)
and `ā := QuotientGroup.mk' V a`, the statement says that the inner automorphism
`c := MulAut.conjNormal ā` of `H` fixes the element `c y * y⁻¹` for every `y ∈ H`.

The mathematical content is the double-commutator hypothesis `⁅⁅K, A⁆, A⁆ = ⊥`: it forces
every element of `⁅K, A⁆` to commute with every element of `A`
(`Subgroup.commutator_eq_bot_iff_le_centralizer`).  Since `y` lifts to some `u ∈ U ≤ K`, the
element `c y * y⁻¹` is the image of the genuine commutator `⁅a, u⁆ ∈ U` (using `⁅a, u⁆ * u = a u a⁻¹`),
which lies in `⁅K, A⁆`; hence it is fixed by conjugation by `a ∈ A`.
-/

open scoped commutatorElement

namespace Work.PSTAB

/-- Conjugation by (the image of) `a ∈ A` fixes `c y * y⁻¹` on the image of the normal
subgroup `U` in `M ⧸ V`, for `⁅⁅K, A⁆, A⁆ = ⊥` and `U ≤ K`. -/
theorem ConjNormalQuadratic {M : Type*} [Group M] {U V : Subgroup M}
    [U.Normal] [V.Normal] {K A : Subgroup M} (hUK : U ≤ K)
    (hKAA : ⁅⁅K, A⁆, A⁆ = (⊥ : Subgroup M)) {a : M} (ha : a ∈ A)
    (y : ↥(U.map (QuotientGroup.mk' V))) :
    MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)) (QuotientGroup.mk' V a)
        (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)) (QuotientGroup.mk' V a) y * y⁻¹) =
      MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)) (QuotientGroup.mk' V a) y * y⁻¹ := by
  -- Lift `y` to an element `u ∈ U` of the ambient group.
  obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp y.property
  -- `⁅a, u⁆` still lies in `U`, because `U` is normal.
  have hxU : ⁅a, u⁆ ∈ U := by
    rw [commutatorElement_def]
    exact U.mul_mem ((inferInstance : U.Normal).conj_mem u hu a) (U.inv_mem hu)
  -- The element of `H` whose image is `⁅a, u⁆`.
  let X : ↥(U.map (QuotientGroup.mk' V)) :=
    ⟨QuotientGroup.mk' V ⁅a, u⁆, Subgroup.mem_map_of_mem _ hxU⟩
  -- `⁅a, u⁆ ∈ ⁅K, A⁆`, since `u ∈ U ≤ K` and `a ∈ A`.
  have hxmem : ⁅a, u⁆ ∈ ⁅K, A⁆ := by
    have h := Subgroup.commutator_mem_commutator (hUK hu) ha
    rw [← commutatorElement_inv u a]
    exact Subgroup.inv_mem _ h
  -- The hypothesis `⁅⁅K, A⁆, A⁆ = ⊥` says exactly that `⁅K, A⁆` centralizes `A`.
  have hcent : ⁅K, A⁆ ≤ Subgroup.centralizer (A : Set M) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKAA
  have hcomm : a * ⁅a, u⁆ = ⁅a, u⁆ * a :=
    (Subgroup.mem_centralizer_iff.mp (hcent hxmem)) a ha
  -- Hence `a` fixes `⁅a, u⁆` by conjugation.
  have hax : a * ⁅a, u⁆ * a⁻¹ = ⁅a, u⁆ := by
    rw [hcomm, mul_inv_cancel_right]
  -- And `a u a⁻¹ = ⁅a, u⁆ * u`.
  have hau : a * u * a⁻¹ = ⁅a, u⁆ * u := by
    rw [commutatorElement_def]; group
  -- `X` is fixed by conjugation by `ā = mk' V a`.
  have hphiX : MulAut.conjNormal (H := U.map (QuotientGroup.mk' V))
      (QuotientGroup.mk' V a) X = X := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    change QuotientGroup.mk' V a * QuotientGroup.mk' V ⁅a, u⁆ * (QuotientGroup.mk' V a)⁻¹
      = QuotientGroup.mk' V ⁅a, u⁆
    have hh := congrArg (QuotientGroup.mk' V) hax
    simpa only [map_mul, map_inv] using hh
  -- Conjugation of `y` is multiplication by `X`.
  have hphiy : MulAut.conjNormal (H := U.map (QuotientGroup.mk' V))
      (QuotientGroup.mk' V a) y = X * y := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, Subgroup.coe_mul]
    change QuotientGroup.mk' V a * ↑y * (QuotientGroup.mk' V a)⁻¹
      = QuotientGroup.mk' V ⁅a, u⁆ * ↑y
    rw [← huy]
    have hh := congrArg (QuotientGroup.mk' V) hau
    simpa only [map_mul, map_inv] using hh
  -- Therefore `c y * y⁻¹ = X`, which is fixed.
  have hz : MulAut.conjNormal (H := U.map (QuotientGroup.mk' V))
      (QuotientGroup.mk' V a) y * y⁻¹ = X := by
    rw [hphiy, mul_inv_cancel_right]
  rw [hz, hphiX]

end Work.PSTAB
