import Mathlib
import Submission.Work.Transgression.Kunneth
import Submission.Work.Transgression.Algebra
import Submission.Work.Transgression.Statement

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The `S³ × S³` overlaps of the transgression: the vanishing of the cross pullbacks

`Work.Transgression.KunnethInj` (the Künneth-basis input of the Mayer–Vietoris transgression) says
that a class in `H³(S³ × S³;ℤ)` killed by both factor inclusions `sect₁, sect₂` is zero.  Its two
easy halves are

* `sectᵢ^* ∘ prjᵢ^* = id` — already proved in `Submission/Work/Transgression/Kunneth.lean`
  (`sect₁_comp_prj₁`, `sect₂_comp_prj₂`), and
* `sectᵢ^* ∘ prj_j^* = 0` for `i ≠ j`, proved here: `prj_j ∘ sectᵢ` is the *constant* map at the
  north pole and a constant map induces `0` on positive-degree cohomology
  (`Work.Agree.HMap_const_eq_zero`).

The constraint on the formalisation (learned the hard way): the utility
`Work.Cohomology.singularCohomologyMap_const_eq_zero` lives in
`Submission/Work/Projective/SS_lattice_and_pairings.lean`, which **cannot** be imported together
with `Transgression.Kunneth` (both `Cohomology/prodSphereAux.lean` and
`Cohomology/CompatTrans/prodSphereAux.lean` define `Work.Cohomology.homologyBiprodIso`), so the
vanishing is re-proved here from `Work.Cohomology.punit`.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- **A constant map induces `0` on `H^{m+1}`.**  It factors as `B₁ → PUnit → B₂`, and the middle
term `H^{m+1}(PUnit;ℤ)` is a zero object (`Work.Cohomology.punit`), so the first factor is zero. -/
theorem HMap_const_eq_zero {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    (y : B₂) (m : ℕ) (x : H (m + 1) B₂) :
    (HMap (ContinuousMap.const B₁ y) (m + 1)).hom x = 0 := by
  have hfac : ContinuousMap.const B₁ y
      = (ContinuousMap.const PUnit y).comp (ContinuousMap.const B₁ PUnit.unit) := by
    ext b
    rfl
  haveI hZ : CategoryTheory.Limits.IsZero (H (m + 1) PUnit) := Work.Cohomology.punit ℤ m
  have hz : HMap (ContinuousMap.const PUnit y) (m + 1) = 0 := hZ.eq_of_tgt _ 0
  rw [hfac, HMap_comp, hz, ModuleCat.hom_comp]
  simp

/-- **The first cross composite is constant**: `prj₂ ∘ sect₁ = const N`. -/
theorem prj₂_comp_sect₁ :
    Work.Transgression.prj₂.comp Work.Transgression.sect₁
      = ContinuousMap.const _ (Work.Cohomology.sphN 3) := by
  ext y
  rfl

/-- **The second cross composite is constant**: `prj₁ ∘ sect₂ = const N`. -/
theorem prj₁_comp_sect₂ :
    Work.Transgression.prj₁.comp Work.Transgression.sect₂
      = ContinuousMap.const _ (Work.Cohomology.sphN 3) := by
  ext y
  rfl

/-- **The first cross pullback vanishes** in degree `3`: `sect₁^* ∘ prj₂^* = 0`. -/
theorem sect₁_prj₂_zero :
    ((HMap Work.Transgression.sect₁ 3).hom).comp
      ((HMap Work.Transgression.prj₂ 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp Work.Transgression.sect₁ Work.Transgression.prj₂ 3
  rw [prj₂_comp_sect₁] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact HMap_const_eq_zero (Work.Cohomology.sphN 3) 2 x

/-- **The second cross pullback vanishes** in degree `3`: `sect₂^* ∘ prj₁^* = 0`. -/
theorem sect₂_prj₁_zero :
    ((HMap Work.Transgression.sect₂ 3).hom).comp
      ((HMap Work.Transgression.prj₁ 3).hom) = 0 := by
  apply LinearMap.ext
  intro x
  have hcomp := HMap_comp Work.Transgression.sect₂ Work.Transgression.prj₁ 3
  rw [prj₁_comp_sect₂] at hcomp
  rw [← ModuleCat.hom_comp, ← hcomp]
  exact HMap_const_eq_zero (Work.Cohomology.sphN 3) 2 x

/-! ## The rank-two bookkeeping: what remains, and the instance trap

The remaining step of `Work.Transgression.KunnethInj` is the *span* statement: with `gen` the
generator of `H³(S³;ℤ)` (i.e. `ModuleCat.Hom.hom s3Iso.inv 1` for
`s3Iso : H³(S³;ℤ) ≅ ℤ`, whose `φ := ModuleCat.Hom.hom s3Iso.hom` satisfies `φ gen = 1`), form

* `T : (Fin 2 → ℤ) →ₗ[ℤ] H³(S³ × S³;ℤ)`, `T c = c 0 • prj₁^* gen + c 1 • prj₂^* gen`,
* `S : H³(S³ × S³;ℤ) →ₗ[ℤ] (Fin 2 → ℤ)`, `S x = ![φ (sect₁^* x), φ (sect₂^* x)]`,

and prove `S.comp T = LinearMap.id` from the four pairing entries (`sectᵢ_comp_prjᵢ`, and
`Work.Agree.sect₁_prj₂_zero`/`sect₂_prj₁_zero` above).  Then
`Work.Transgression.bijective_of_comp_eq_id_of_iso_two T S h e` (`e` from
`Work.Cohomology.cohomology_prod_sphere 3 3 3`, bridged to `Coh ℤ 3 ↥(S33)` by
`Homeomorph.setCongr (sphereSet_eq' 4)`) gives `T` bijective, and since `S.comp T = id`,
`Function.Injective S` follows (`y = S (T y)`), hence `KunnethInj`.

**The instance trap (hit twice; do not repeat).**  The carrier `↥(H n X) = ↥(Coh ℤ n X)` of a
`ModuleCat` carries *two* compatible `ℤ`-scalar structures — `ZSMul.toSMul` and
`DistribMulAction.toDistribSMul.toSMul` — so by-hand `LinearMap` constructions on it fail:
`smulRight` needs `IsScalarTower ℤ ℤ ↥(H n X)` (not synthesizable), and goals such as
`k • (c 0 • A) = ((RingHom.id ℤ) k) • (c 0 • A)` are *propositionally* but not *definitionally*
true, so `rfl`/`simp` will not close them (use `add_zsmul`/`neg_zsmul`/`smul_add`/`mul_zsmul`
explicitly, as `Work.Agree.bottHopf_of_bricks` does for its final scalar bookkeeping, or build the
maps through `ModuleCat` homs rather than raw `LinearMap`s).
-/

end

end Work.Agree
