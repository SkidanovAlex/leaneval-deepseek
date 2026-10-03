/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semisimplicity of `D H` from the division-ring property of `D G'`

`Work.ORLinnell.Cosets.isSemisimpleRing_D` proves that `D H` is semisimple for every `H ≤ G` when
`G' ⊴ G` is normal of finite index and *torsion free* (`IsMulTorsionFree G'`, i.e. every power map
of `G'` injective).  The hypothesis that is actually consumed by the proof is only the
division-ring property of `D G'`: `∀ x : ↥(D G'), x ≠ 0 → IsUnit x`.  This is the form in which
node N6 delivers the Hughes-free division rings (for a locally indicable `G'`), and it does *not*
imply `IsMulTorsionFree G'` (the Klein bottle group is torsion free and locally indicable but
`(a t)² = t²` with `a t ≠ t`), so the two statements are genuinely different.

Here we prove the transfer of the division-ring property to *any* subgroup of `G'`
(`isUnit_of_mem_D_of_le`) and then the target statement
`isSemisimpleRing_D_of_divisionOn`: for `G' ⊴ G` of finite index with `D G'` a division ring,
`D H` is semisimple for every `H ≤ G`.

The finite index Maschke argument with the division hypothesis on `D H₀` (instead of
`IsMulTorsionFree H₀`) is proved separately, in
`Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_finiteIndex_of_divOn`.
-/
import Mathlib
import Submission.Work.ORLinnell.Main
import Submission.Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_finiteIndex_of_divOn

namespace Work.ORFinal.WeakSemisimple

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Nontrivial U]
  [Algebra K U]

/-- **The division-ring property of `D G'` descends to `D G''` for `G'' ≤ G'`.**

If every nonzero element of `L.D G'` is a unit, then the same holds for every subgroup
`G'' ≤ G'`: given `x ∈ D G'' ⊆ D G'` nonzero, the inverse `u⁻¹` of `x` inside `D G'` satisfies
`x * u⁻¹ = 1` in `U`, so `u⁻¹ ∈ D G''` by division closedness of `D G''`. -/
theorem isUnit_of_mem_D_of_le (L : Work.ORLinnell.LinnellDatum K G U) {G'' G' : Subgroup G}
    (h : G'' ≤ G') (hdiv : ∀ x : ↥(L.D G'), x ≠ 0 → IsUnit x) :
    ∀ x : ↥(L.D G''), x ≠ 0 → IsUnit x := by
  intro x hx
  have hxU : (x : U) ∈ L.D G' := L.D_mono h x.2
  have hxne : (⟨(x : U), hxU⟩ : ↥(L.D G')) ≠ 0 := by
    intro h'
    exact hx (Subtype.ext (by simpa using congrArg (fun y : ↥(L.D G') => (y : U)) h'))
  let u : (↥(L.D G'))ˣ := (hdiv ⟨(x : U), hxU⟩ hxne).unit
  have hu : ((u : ↥(L.D G')) : U) = (x : U) :=
    congrArg (fun y : ↥(L.D G') => (y : U)) (IsUnit.unit_spec _)
  have h1 : (((u : ↥(L.D G')) : U)) * ((((u⁻¹ : (↥(L.D G'))ˣ) : ↥(L.D G')) : U)) = 1 :=
    congrArg (fun y : ↥(L.D G') => (y : U)) (Units.mul_inv u)
  have h2 : ((((u⁻¹ : (↥(L.D G'))ˣ) : ↥(L.D G')) : U)) * (((u : ↥(L.D G')) : U)) = 1 :=
    congrArg (fun y : ↥(L.D G') => (y : U)) (Units.inv_mul u)
  have hxm : (x : U) * ((((u⁻¹ : (↥(L.D G'))ˣ) : ↥(L.D G')) : U)) = 1 := by
    rw [← hu]; exact h1
  have hmx : ((((u⁻¹ : (↥(L.D G'))ˣ) : ↥(L.D G')) : U)) * (x : U) = 1 := by
    rw [← hu]; exact h2
  have hbD : ((((u⁻¹ : (↥(L.D G'))ˣ) : ↥(L.D G')) : U)) ∈ L.D G'' :=
    L.isDivisionClosed G'' (x : U) x.2 _ hxm
  exact ⟨⟨x, ⟨_, hbD⟩, Subtype.ext hxm, Subtype.ext hmx⟩, rfl⟩

/-- **`D H` is semisimple when `D G'` is a division ring**, for `G' ⊴ G` normal of finite index
and *every* subgroup `H ≤ G` (characteristic zero).

This is `Work.ORLinnell.Cosets.isSemisimpleRing_D` with the hypothesis `IsMulTorsionFree G'`
replaced by the division-ring property of `D G'` — the form supplied by the Hughes-free input for
a locally indicable `G'`.  The proof runs the finite index Maschke argument on
`H₀ := H ⊓ G' ≤ H` (normal of finite index in `H`), whose division closure is a division ring by
`isUnit_of_mem_D_of_le`. -/
theorem isSemisimpleRing_D_of_divisionOn (K : Type*) [Field K] [CharZero K] (G : Type*) [Group G]
    (U : Type*) [Ring U] [Nontrivial U] [Algebra K U]
    (L : Work.ORLinnell.LinnellDatum K G U) (G' : Subgroup G) (hG'n : G'.Normal)
    (hfin : G'.FiniteIndex) (hdiv : ∀ x : ↥(L.D G'), x ≠ 0 → IsUnit x) (H : Subgroup G) :
    IsSemisimpleRing ↥(L.D H) := by
  have hle : H ⊓ G' ≤ H := inf_le_left
  have hN : ((H ⊓ G').subgroupOf H).Normal := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    exact hG'n.subgroupOf H
  have hfin' : ((H ⊓ G').subgroupOf H).FiniteIndex := by
    rw [Subgroup.inf_subgroupOf_left G' H]
    infer_instance
  refine Work.ORFinal.WeakSemisimple.isSemisimpleRing_D_of_finiteIndex_of_divOn K G U L
    (H₀ := H ⊓ G') (H := H) hle hN hfin' ?_
  exact isUnit_of_mem_D_of_le L inf_le_right hdiv

end Work.ORFinal.WeakSemisimple
