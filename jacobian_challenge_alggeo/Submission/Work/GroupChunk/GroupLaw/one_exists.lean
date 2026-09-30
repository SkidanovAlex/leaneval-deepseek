import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Defs
import Submission.Work.GroupChunk.AbelJacobi
import Submission.Work.GroupChunk.Gluing.Transitions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped MonoidalCategory

universe u

namespace Work.GroupChunk.GroupLaw

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
  {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
  [Work.SpecLin.DivBase C]

/-! ## Helper lemmas for `one_exists`

The origin of the group chunk is a `K`-point of `G D`, i.e. a morphism `Spec K ⟶ G D`
over `K`, whereas the statement of `one_exists` asks for a morphism `𝟙_ (Sch K) ⟶ G D`
out of the terminal object.  The two are the same thing, since `specOf K K = Spec K`
*is* the terminal object of `Sch K` — but only up to a propositional (not definitional)
equality, so an explicit inverse of the structure morphism
`toUnit (specOf K K) : specOf K K ⟶ 𝟙_ (Sch K)` has to be produced.  The lemmas below
supply that inverse (through `eqToHom`), its defining equation, the compatibility of
`toUnit` with base change of the field, and the vanishing of the chart class `picOf`
under base change of the field. -/

/-- The structure morphism `Spec K ⟶ Spec K` defining `specOf K K` is the identity. -/
theorem specOf_self_hom_eq :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  rw [show algebraMap K K = RingHom.id K from rfl]
  exact Spec.map_id _

/-- `specOf K K = Spec K` is the terminal object `𝟙_ (Sch K)`. -/
theorem specOf_self_eq_unit :
    (Work.GCBasics.specOf K K : Work.GCBasics.Sch K) = 𝟙_ (Work.GCBasics.Sch K) := by
  show Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) = 𝟙_ (Work.GCBasics.Sch K)
  rw [specOf_self_hom_eq]
  rfl
/-- The inverse of `toUnit (specOf K K)`, as a morphism given by `eqToHom`. -/
theorem toUnit_specOf_comp_eqToHom :
    Work.GroupChunk.toUnit (Work.GCBasics.specOf K K)
      ≫ eqToHom (specOf_self_eq_unit (K := K)).symm = 𝟙 (Work.GCBasics.specOf K K) := by
  rw [show Work.GroupChunk.toUnit (Work.GCBasics.specOf K K)
      = eqToHom (specOf_self_eq_unit (K := K)) from Work.GroupChunk.toUnit_unique _ _]
  rw [eqToHom_trans, eqToHom_refl]

/-- A `K`-point of a `K`-scheme is the composite of the corresponding `𝟙_`-point with the
structure map `specOf K K ⟶ 𝟙_`. -/
theorem toUnit_comp_pt {X : Work.GCBasics.Sch K} (p : Work.GCBasics.FPt X K) :
    Work.GroupChunk.toUnit (Work.GCBasics.specOf K K)
      ≫ (eqToHom (specOf_self_eq_unit (K := K)).symm ≫ p) = p := by
  rw [← Category.assoc, toUnit_specOf_comp_eqToHom, Category.id_comp]

/-- Base change of the point of `X` defined by the `𝟙_`-point `P`. -/
theorem RPt_map_toUnit {X : Work.GCBasics.Sch K} {F : Type u} [Field F] [Algebra K F]
    (e : K →ₐ[K] F) (P : 𝟙_ (Work.GCBasics.Sch K) ⟶ X) :
    Work.GCBasics.RPt.map e (Work.GroupChunk.toUnit (Work.GCBasics.specOf K K) ≫ P)
      = Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ P := by
  show Work.GCBasics.specOfMap (K := K) e
      ≫ (Work.GroupChunk.toUnit (Work.GCBasics.specOf K K) ≫ P) = _
  rw [← Category.assoc]
  rw [Work.GroupChunk.toUnit_unique
    (Work.GCBasics.specOfMap (K := K) e ≫ Work.GroupChunk.toUnit (Work.GCBasics.specOf K K))
    (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F))]

/-- The chart class `picOf` of a point of `Sym^g C` over `K`, base changed to a field `F`,
vanishes as soon as it vanishes over `K`. -/
theorem picOf_bc (D : Work.GroupChunk.Input C P0) (i : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (y : Work.GCBasics.FPt (D.Sym D.g) K) (hy : D.picOf i y = 0) :
    D.picOf i (Work.GCBasics.RPt.map (Algebra.ofId K F) y) = 0 := by
  rw [Work.GroupChunk.Input.picOf_def] at hy ⊢
  rw [show (0 : Work.GCBasics.Pic0 C K)
      = Work.GCBasics.Pic0.mk (0 : Work.GCBasics.Dv C K) (by simp)
      from (Work.GCBasics.Pic0.mk_zero).symm] at hy
  have hL0 : Work.GCBasics.LinEquiv C (D.divOf D.g y - D.divOf D.g (D.EF i)) 0 :=
    (Work.GCBasics.Pic0.mk_eq_iff _ _).mp hy
  have hA : D.divOf D.g (D.EF i) = D.EDiv i := by
    rw [Work.GroupChunk.Input.EF_divOf]
    show Work.SpecLin.DivBase.bc (Algebra.ofId K K) (D.EDiv i) = D.EDiv i
    rw [show (Algebra.ofId K K : K →ₐ[K] K) = AlgHom.id K K from rfl,
      Work.SpecLin.DivBase.bc_id]
  rw [hA] at hL0
  have hbc : Work.GCBasics.LinEquiv C
      (Work.SpecLin.DivBase.bc (Algebra.ofId K F) (D.divOf D.g y)
        - Work.SpecLin.DivBase.bc (Algebra.ofId K F) (D.EDiv i)) 0 := by
    have h := Work.SpecLin.DivBase.linEquiv_bc (Algebra.ofId K F) hL0
    rw [Work.SpecLin.DivBase.bc_zero] at h
    have h1 : Work.SpecLin.DivBase.bc (Algebra.ofId K F) (D.divOf D.g y - D.EDiv i)
        = Work.SpecLin.DivBase.bc (Algebra.ofId K F) (D.divOf D.g y)
          - Work.SpecLin.DivBase.bc (Algebra.ofId K F) (D.EDiv i) := by
      rw [sub_eq_add_neg, Work.SpecLin.DivBase.bc_add, Work.SpecLin.DivBase.bc_neg,
        sub_eq_add_neg]
    rw [h1] at h
    exact h
  rw [show (0 : Work.GCBasics.Pic0 C F)
      = Work.GCBasics.Pic0.mk (0 : Work.GCBasics.Dv C F) (by simp)
      from (Work.GCBasics.Pic0.mk_zero).symm]
  refine (Work.GCBasics.Pic0.mk_eq_iff
    (D := D.divOf D.g (Work.GCBasics.RPt.map (Algebra.ofId K F) y) - D.divOf D.g (D.EF i))
    (D' := (0 : Work.GCBasics.Dv C F)) _ _).mpr ?_
  rw [Work.GroupChunk.Input.EF_divOf,
    Work.GroupChunk.Input.divOf_map D D.g (Algebra.ofId K F) y]
  exact hbc

open CategoryTheory in
theorem one_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    ∃ one : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶
        Work.GroupChunk.GSch D,
      ∀ {F : Type u} [Field F] [Algebra K F],
        Work.GroupChunk.Input.cls D
          (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ one) = 0 := by
  classical
  -- A `K`-point of the group chunk with trivial class, factoring through a chart.
  obtain ⟨i, y, hyV, hy0⟩ := Work.GroupChunk.Input.cov' D (0 : Work.GCBasics.Pic0 C K)
  obtain ⟨y', hy', -⟩ := Work.GCBasics.FPt.factor_of_landsIn (K := K) D.V y hyV
  -- An (opaque) inverse for the structure morphism `specOf K K ⟶ 𝟙_`, and hence a
  -- `𝟙_`-point of `G D` whose underlying `K`-point is `y' ≫ chart i`.
  have hne : Nonempty {q : 𝟙_ (Work.GCBasics.Sch K) ⟶ Work.GCBasics.specOf K K //
      Work.GroupChunk.toUnit (Work.GCBasics.specOf K K) ≫ q = 𝟙 (Work.GCBasics.specOf K K)} :=
    ⟨⟨eqToHom (specOf_self_eq_unit (K := K)).symm, toUnit_specOf_comp_eqToHom⟩⟩
  let q : 𝟙_ (Work.GCBasics.Sch K) ⟶ Work.GCBasics.specOf K K := (Classical.choice hne).1
  have hq : Work.GroupChunk.toUnit (Work.GCBasics.specOf K K) ≫ q
      = 𝟙 (Work.GCBasics.specOf K K) := (Classical.choice hne).2
  let one : 𝟙_ (Work.GCBasics.Sch K) ⟶ Work.GroupChunk.GSch D := q ≫ (y' ≫ D.chart i)
  have hone : Work.GroupChunk.toUnit (Work.GCBasics.specOf K K) ≫ one = y' ≫ D.chart i := by
    show Work.GroupChunk.toUnit (Work.GCBasics.specOf K K)
      ≫ (q ≫ (y' ≫ D.chart i)) = y' ≫ D.chart i
    rw [← Category.assoc, hq, Category.id_comp]
  refine ⟨one, ?_⟩
  intro F _ _
  -- The base change of the `𝟙_`-point is the base change of the `K`-point `y'`.
  have hbase : Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ one
      = Work.GCBasics.RPt.map (Algebra.ofId K F) (y' ≫ D.chart i) := by
    rw [← RPt_map_toUnit (Algebra.ofId K F) one, hone]
  have hfac : Work.GroupChunk.toUnit (Work.GCBasics.specOf K F) ≫ one
      = Work.GCBasics.RPt.map (Algebra.ofId K F) y' ≫ D.chart i := by
    rw [hbase]
    rw [show Work.GCBasics.RPt.map (Algebra.ofId K F) y'
        = Work.GCBasics.specOfMap (K := K) (Algebra.ofId K F) ≫ y' from rfl]
    rw [show Work.GCBasics.RPt.map (Algebra.ofId K F) (y' ≫ D.chart i)
        = Work.GCBasics.specOfMap (K := K) (Algebra.ofId K F) ≫ (y' ≫ D.chart i) from rfl]
    rw [Category.assoc]
  have h3 : Work.GCBasics.RPt.map (Algebra.ofId K F) y' ≫ Work.GCBasics.Opens.ιOver D.V
      = Work.GCBasics.RPt.map (Algebra.ofId K F) y := by
    rw [show Work.GCBasics.RPt.map (Algebra.ofId K F) y'
        = Work.GCBasics.specOfMap (K := K) (Algebra.ofId K F) ≫ y' from rfl]
    rw [show Work.GCBasics.RPt.map (Algebra.ofId K F) y
        = Work.GCBasics.specOfMap (K := K) (Algebra.ofId K F) ≫ y from rfl]
    rw [Category.assoc, hy']
  exact (congrArg (Work.GroupChunk.Input.cls D) hfac).trans
    ((Work.GroupChunk.Input.cls_chart D i (Work.GCBasics.RPt.map (Algebra.ofId K F) y')).trans
      ((congrArg (D.picOf i) h3).trans (picOf_bc D i y hy0)))
end Work.GroupChunk.GroupLaw
