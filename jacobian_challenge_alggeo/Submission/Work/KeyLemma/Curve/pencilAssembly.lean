/-
# Assembly of the pencil case of the key lemma

This file contains the two bookkeeping steps that turn the specialisation statement
`Work.KeyLemma.Curve.exists_branch_sum` into the pencil case of the key lemma
`Work.KeyLemma.Curve.sumOfPoints_eq_of_pencil`:

* `Work.KeyLemma.Curve.exists_const_eq_genericSum` (step **(asm)**): from
  `e : K(ℙ¹) ≅ k(h)` and the Galois descent (`exists_genericSum_descend`) of the generic-fibre sum
  one obtains a `k`-point `c` of `A` whose base change to `N` is `genericSum`.  The extension
  `Spec K(ℙ¹) ⟶ A` of the descent along the generic point exists by
  `Work.KeyLemma.Curve.extends_of_stalk_genericPoint_p1` and is constant by `p1Const`.

* `Work.KeyLemma.Curve.sumOfPoints_eq_of_branch` (step **(br-final)**): an `R'`-point `ρ` of `A`
  whose generic value is the base change of `c` is the constant morphism with value `c`
  (`Work.SpecLin.RPt.eq_of_generic_eq`, i.e. separatedness of `A`), so its special value
  `Σ f(s)` equals `c`.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.genericSum_galois
import Submission.Work.KeyLemma.Curve.exists_genericSum_descend
import Submission.Work.KeyLemma.Curve.genericSum_inv
import Submission.Work.KeyLemma.Curve.p1FunctionField
import Submission.Work.KeyLemma.Curve.extends_of_stalk_genericPoint_p1
import Submission.Work.KeyLemma.Pencil
import Submission.Work.KeyLemma.Sum
import Submission.Work.SpecLin.Setup.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.CurveBasics

variable {k : Type u} [Field k]

/-- The generic point of `ℙ¹` is a morphism over `Spec k` for the canonical `k`-algebra structure
on `K(ℙ¹)` (the analogue of `Work.CurveBasics.Curve.fromSpecStalk_genericPoint_comp_hom`). -/
theorem fromSpecStalk_genericPoint_comp_hom_p1 (k : Type u) [Field k] :
    (Work.AbVar.P1 k).left.fromSpecStalk (genericPoint (Work.AbVar.P1 k).left) ≫
        (Work.AbVar.P1 k).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField))) := by
  have : Nonempty (⊤ : (Work.AbVar.P1 k).left.Opens) :=
    ⟨⟨genericPoint (Work.AbVar.P1 k).left, trivial⟩⟩
  rw [← cancel_mono (Spec (CommRingCat.of k)).toSpecΓ]
  rw [Category.assoc, Scheme.toSpecΓ_naturality, ← Category.assoc,
      Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rw [show (Spec (CommRingCat.of k)).toSpecΓ =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).hom) from by
    rw [← Scheme.isoSpec_hom]; simp [Scheme.isoSpec_Spec]]
  rw [← Spec.map_comp]
  refine (Spec.map_injective.eq_iff).mpr ?_
  rw [show CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Work.AbVar.P1 k).hom.appTop ≫
        (Work.AbVar.P1 k).left.germToFunctionField ⊤ from rfl]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section Asm

variable (C : Curve k) {h : C.functionField} (hht : Transcendental k h)
variable {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] (f : C.toOver ⟶ A)
variable {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]
  [FiniteDimensional ↥(baseField C h) ↥C.functionField]
  [Algebra.IsSeparable ↥(baseField C h) ↥C.functionField]
  [IsGalois ↥(baseField C h) N]

/-- **(asm)**: there is a `k`-point `c` of `A` whose base change to `N` is the generic-fibre sum
of the pencil of `h`.

Given an isomorphism `e : K(ℙ¹) ≅ k(h)`, the Galois descent `a` of `genericSum`
(`exists_genericSum_descend`) transports along `e` to a morphism `Spec K(ℙ¹) ⟶ A`, which extends
to `ℙ¹ ⟶ A` (`extends_of_stalk_genericPoint_p1`) and is constant with value `c` (`p1Const`). -/
theorem exists_const_eq_genericSum
    (e : ↥((Work.AbVar.P1 k).left.functionField) ≃ₐ[k] ↥(baseField C h)) :
    ∃ c : Pt k A, Spec.map (CommRingCat.ofHom (algebraMap k N)) ≫ c.left
      = genericSum (C := C) (h := h) (N := N) f := by
  classical
  -- the Galois descent of the generic-fibre sum
  obtain ⟨a, haK, ha⟩ := exists_genericSum_descend (k := k) C h f N
    (fun τ => genericSum_galois (k := k) C h f N τ)
  -- the morphism `Spec K(ℙ¹) ⟶ A` obtained by transporting `a` along `e`
  set g : Spec (CommRingCat.of ↥((Work.AbVar.P1 k).left.functionField)) ⟶ A.left :=
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ a with hg_def
  -- it is compatible with the structure morphisms of `ℙ¹`
  have hg : g ≫ A.hom = (Work.AbVar.P1 k).left.fromSpecStalk
      (genericPoint (Work.AbVar.P1 k).left) ≫ (Work.AbVar.P1 k).hom := by
    have hcomp : CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField))
        = CommRingCat.ofHom (algebraMap k ↥(baseField C h))
          ≫ CommRingCat.ofHom e.symm.toRingHom := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      exact RingHom.ext fun x => (e.symm.commutes x).symm
    rw [hg_def, Category.assoc, haK, ← Spec.map_comp]
    rw [← hcomp]
    exact (fromSpecStalk_genericPoint_comp_hom_p1 k).symm
  -- extension to `ℙ¹`
  obtain ⟨σ, hσA, hσg⟩ := extends_of_stalk_genericPoint_p1 (k := k) g hg
  -- the corresponding `Over`-morphism and its constancy
  let φ : Work.AbVar.P1 k ⟶ A := Over.homMk σ hσA
  obtain ⟨c, hc⟩ := Work.KeyLemma.Curve.p1Const k φ
  refine ⟨c, ?_⟩
  -- the generic value of the constant morphism
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField)))
      ≫ c.left = g := by
    have hcomp2 : Spec.map (CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField)))
        = (Work.AbVar.P1 k).left.fromSpecStalk (genericPoint (Work.AbVar.P1 k).left)
          ≫ (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k)).left := by
      rw [show (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k)).left
        = (Work.AbVar.P1 k).hom from rfl]
      exact (fromSpecStalk_genericPoint_comp_hom_p1 k).symm
    have h2 : (SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k)).left ≫ c.left = σ := by
      have h3 := congrArg Over.Hom.left hc
      rw [Over.comp_left] at h3
      rw [← h3]
      rfl
    rw [hcomp2, Category.assoc, h2]
    exact hσg
  -- the generic value of `c` is the descent `a`
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap k ↥(baseField C h))) ≫ c.left = a := by
    have hh := congrArg (fun m => Spec.map (CommRingCat.ofHom e.toRingHom) ≫ m) h1
    rw [← Category.assoc] at hh
    rw [← Spec.map_comp] at hh
    rw [show CommRingCat.ofHom (algebraMap k ↥((Work.AbVar.P1 k).left.functionField))
          ≫ CommRingCat.ofHom e.toRingHom
        = CommRingCat.ofHom (algebraMap k ↥(baseField C h)) from by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      exact RingHom.ext fun x => e.commutes x] at hh
    rw [hg_def] at hh
    rw [← Category.assoc] at hh
    rw [← Spec.map_comp] at hh
    rw [show CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom
        = 𝟙 (CommRingCat.of ↥(baseField C h)) from by
      rw [show (𝟙 (CommRingCat.of ↥(baseField C h)))
          = CommRingCat.ofHom (RingHom.id ↥(baseField C h)) from rfl]
      rw [← CommRingCat.ofHom_comp]
      congr 1
      exact RingHom.ext fun x => e.apply_symm_apply x] at hh
    simpa using hh
  -- base change to `N`
  have h4 := congrArg (fun m => Spec.map
    (CommRingCat.ofHom (algebraMap ↥(baseField C h) N)) ≫ m) h3
  rw [← Category.assoc] at h4
  rw [← Spec.map_comp] at h4
  rw [show CommRingCat.ofHom (algebraMap k ↥(baseField C h))
        ≫ CommRingCat.ofHom (algebraMap ↥(baseField C h) N)
      = CommRingCat.ofHom (algebraMap k N) from by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    exact (IsScalarTower.algebraMap_eq k ↥(baseField C h) N).symm] at h4
  rw [ha] at h4
  exact h4

end Asm

section BrFinal

variable (C : Curve k) {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] (f : C.toOver ⟶ A)

/-- **(br-final)**: an `R'`-point `ρ` of `A` whose generic value over `N = Frac R'` is the base
change of the `k`-point `c` is determined by `c`, and so the value of `ρ` at the closed point
(described by `hρ2`) is `c`.

`ρ` and the base change of `c` to `R'` are two `R'`-points of `A` with the same generic fibre
over `N = Frac R'`, so they agree by separatedness of `A`
(`Work.SpecLin.Setup.RPt.eq_of_generic_eq`).  The value of the constant morphism at the closed
point is then computed by composing with the structure morphism of `A`: the resulting endomorphism
of `Spec k` is the identity, so `Σ f(s) = c`. -/
theorem sumOfPoints_eq_of_branch {s : SumDiv C}
    {N : Type u} [Field N] [Algebra k N]
    {R' : Type u} [CommRing R'] [IsDomain R'] [ValuationRing R'] [Algebra k R']
    [Algebra R' N] [IsFractionRing R' N] [IsScalarTower k R' N]
    (ρ : Work.SpecLin.RPt A R') (c : Pt k A) (c₀ : Work.SpecLin.RPt A k)
    (hc₀ : c₀.left = c.leftHom)
    (e : IsLocalRing.ResidueField R' ≃+* k)
    (hρ1 : Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k R' N) ρ
      = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k k N) c₀)
    (hρ2 : Spec.map (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue R'))) ≫ ρ.left
      = (SumDiv.sumOfPoints C f s).leftHom) :
    SumDiv.sumOfPoints C f s = c := by
  classical
  -- `ρ` is the base change of `c`
  have hconst : ρ = Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k k R') c₀ := by
    refine Work.SpecLin.RPt.eq_of_generic_eq (K := k) (X := A)
      (inferInstanceAs (IsSeparated A.hom)) R' N ?_
    rw [hρ1, ← Work.SpecLin.RPt.map_comp]
    congr 1
    ext
  -- the value of the base change of `c` at the closed point
  have hmap : (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom k k R') c₀).left
      = Spec.map (CommRingCat.ofHom (algebraMap k R')) ≫ c.leftHom := by
    simp only [Work.SpecLin.RPt.map, Work.SpecLin.specOfMap, Work.SpecLin.specOfMapHom,
      Over.homMk_left, Over.comp_left, hc₀]
    rfl
  have hval : Spec.map (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue R')))
      ≫ (Spec.map (CommRingCat.ofHom (algebraMap k R')) ≫ c.leftHom)
      = (SumDiv.sumOfPoints C f s).leftHom := by
    rw [← hmap, ← hρ2, hconst]
  -- compose with the structure morphism of `A`
  have h3 := congrArg (fun m => m ≫ A.hom) hval
  simp only [Category.assoc, Pt.leftHom_comp, Category.comp_id] at h3
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h3
  have h4 : (e.toRingHom.comp (IsLocalRing.residue R')).comp (algebraMap k R')
      = RingHom.id k := by
    rw [show (𝟙 (Spec (CommRingCat.of k))) = Spec.map (𝟙 (CommRingCat.of k)) from
      (Spec.map_id (CommRingCat.of k)).symm] at h3
    have hspec := Spec.map_injective h3
    have hh := congrArg CommRingCat.Hom.hom hspec
    simpa using hh
  -- conclude
  have h5 : (SumDiv.sumOfPoints C f s).leftHom = c.leftHom := by
    have h6 : Spec.map (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue R')))
        ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))
        = 𝟙 (Spec (CommRingCat.of k)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h4, CommRingCat.ofHom_id, Spec.map_id]
    rw [← hval, ← Category.assoc, h6, Category.id_comp]
  exact Over.OverMorphism.ext h5

end BrFinal

end Work.KeyLemma.Curve
