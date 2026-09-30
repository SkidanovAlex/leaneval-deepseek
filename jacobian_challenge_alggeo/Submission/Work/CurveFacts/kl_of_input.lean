import Mathlib
import Submission.Work.Universal.Basic
import Submission.Work.Universal.sumMap_powMap
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.KeyLemma.Final
import Submission.Work.KeyLemma.Unconditional
import Submission.Work.GenusZero.Basic
import Submission.Work.GenusZero.PointDiv
import Submission.Work.CurveFacts.ptBaseChange_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



namespace Work.CurveFacts

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped CategoryTheory.Obj
open scoped Work.GCBasics

/-! ## Auxiliary facts

These three facts are the plumbing that lets one compare `Work.Universal.sumDiv` (a sum over an
effective divisor, defined through the symmetric power `Symⁿ C`) with the sums
`Work.KeyLemma.Curve.SumDiv.sumOfPoints` over a *split* multiset of points (which is the form in
which the key lemma of area KL is stated).
-/

/-- The place of `C_F` attached to an `F`-point `x` of `C` is the place classified by the base
change of `x` to a point of `Sym¹ C`: both are the image of `Spec F` under the section
`pullback.lift x.left 𝟙`. -/
theorem placeOfPoint_ptBaseChange {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] (x : Work.GCBasics.FPt C.toOver F) :
    Work.KeyLemma.Curve.placeOfPoint (C.baseChange F)
        (Work.GenusZero.ptBaseChange (k := K) F C.toOver x) = Work.SpecLin.ptPlace x := by
  apply Subtype.ext
  rfl

/-- The dictionary between the two descriptions of the divisor of an `F`-point:
`Work.KeyLemma.Curve.SumDiv.toDiv` of the singleton multiset at the base-changed point is the
point divisor `Work.SpecLin.ptDiv`. -/
theorem toDiv_single_ptBaseChange {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] (x : Work.GCBasics.FPt C.toOver F) :
    Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange F)
        (Finsupp.single (Work.GenusZero.ptBaseChange (k := K) F C.toOver x) 1) =
      Work.SpecLin.ptDiv x := by
  rw [Work.GenusZero.toDiv_single_one, placeOfPoint_ptBaseChange]
  rfl

/-- The sum over a multiset of points which is a sum of singletons is the product of the images
of those points. -/
theorem sumOfPoints_sum_single {k : Type u} [Field k] {C : Work.CurveBasics.Curve k}
    {A : Work.GenusZero.Sch k} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) {I : Type} [Fintype I] (p : I → Work.KeyLemma.Curve.Point C) :
    Work.KeyLemma.Curve.SumDiv.sumOfPoints C f (∑ i, Finsupp.single (p i) 1) =
      ∏ i, (p i ≫ f) := by
  have key : ∀ s : Finset I,
      Work.KeyLemma.Curve.SumDiv.sumOfPoints C f (∑ i ∈ s, Finsupp.single (p i) 1) =
        ∏ i ∈ s, (p i ≫ f) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Work.KeyLemma.Curve.SumDiv.sumOfPoints_zero]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, Work.KeyLemma.Curve.SumDiv.sumOfPoints_add,
          ih, Work.KeyLemma.Curve.SumDiv.sumOfPoints_single_one]
  simpa using key Finset.univ

/-- **The key lemma with a field of definition for the divisors.**  For any algebraically closed
field `L` over `F`, the equality `Σ f(E) = Σ f(E')` of two linearly equivalent effective divisors
of degree `n` on `C_F` can be checked after base change to `L`.

This is the heart of item A6: over `L` both divisors split into points
(`Work.SpecLin.SymGeom.split`), the sum `Σ f` becomes the product of the images of the points
(`Work.Universal.sumMap_powMap`), and the model form of the key lemma of area KL
(`Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond`) applies.  The comparison of the
products is then transported back through `Work.GenusZero.ptBaseChange` (which is a monoid
homomorphism, `Work.CurveFacts.ptBaseChange_prodV`). -/
theorem kl_of_input_aux {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (f : C.toOver ⟶ A) {F L : Type u} [Field F] [Algebra K F] [Field L] [Algebra K L]
    [Algebra F L] [IsScalarTower K F L] [IsAlgClosed L]
    (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective) (n : ℕ)
    (hn : Work.GCBasics.Ddeg C F E = (n : ℤ)) (hn' : Work.GCBasics.Ddeg C F E' = (n : ℤ))
    (hlin : Work.GCBasics.LinEquiv C E E') :
    Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F L) (Work.Universal.sumDiv D f E hE n hn) =
      Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F L)
        (Work.Universal.sumDiv D f E' hE' n hn') := by
  obtain ⟨x, hx⟩ := (D.symGeom n).split (F' := L) E hE hn
  obtain ⟨x', hx'⟩ := (D.symGeom n).split (F' := L) E' hE' hn'
  -- `Σ f(G)` computed over `L` is the product of the images of the points of a splitting of `G`.
  have hgen : ∀ (G : Work.GCBasics.Dv C F) (hG : G.IsEffective)
      (hGn : Work.GCBasics.Ddeg C F G = (n : ℤ)) (y : Fin n → Work.SpecLin.CurveFPt C L),
      Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) G = ∑ m, Work.SpecLin.ptDiv (y m) →
      Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F L) (Work.Universal.sumDiv D f G hG n hGn)
        = ∏ m, (y m ≫ f) := by
    intro G hG hGn y hy
    obtain ⟨p, hp⟩ : ∃ p, (D.symGeom n).divOf p = G := (D.symGeom n).divOf_complete G hG hGn
    rw [Work.Universal.sumDiv_eq_of_divOf D f hG hGn hp]
    rw [Work.GCBasics.RPt.map, ← Category.assoc, ← Work.GCBasics.RPt.map]
    have ha : Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K F L) p = (D.symGeom n).powMap y := by
      refine (D.symGeom n).divOf_injective _ _ ?_
      change (D.symGeom n).divOf (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K F L) p) =
        (D.symGeom n).divOf ((D.symGeom n).powMap y)
      rw [(D.symGeom n).divOf_map, hp, (D.symGeom n).divOf_powMap, hy]
    rw [ha, Work.Universal.sumMap_powMap]
    rfl
  have hL := hgen E hE hn x hx
  have hL' := hgen E' hE' hn' x' hx'
  rw [hL, hL']
  -- Now compare the two products, over `L`.
  have hprop : IsProper ((Work.GenusZero.bcFun L).obj A).hom := by
    change IsProper (pullback.snd A.hom (Work.CurveBasics.Curve.specMap K L))
    infer_instance
  let fbar : (C.baseChange L).toOver ⟶ (Work.GenusZero.bcFun L).obj A :=
    (Work.GenusZero.bcFun L).map f
  obtain ⟨h, hh, hdiv⟩ := Work.SpecLin.DivBase.linEquiv_bc (IsScalarTower.toAlgHom K F L) hlin
  let pb : Fin n → Work.KeyLemma.Curve.Point (C.baseChange L) :=
    fun m => Work.GenusZero.ptBaseChange (k := K) L C.toOver (x m)
  let pb' : Fin n → Work.KeyLemma.Curve.Point (C.baseChange L) :=
    fun m => Work.GenusZero.ptBaseChange (k := K) L C.toOver (x' m)
  let s : Work.KeyLemma.Curve.SumDiv (C.baseChange L) := ∑ m, Finsupp.single (pb m) 1
  let s' : Work.KeyLemma.Curve.SumDiv (C.baseChange L) := ∑ m, Finsupp.single (pb' m) 1
  have htoDiv : Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange L) s =
      Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) E := by
    show Work.KeyLemma.Curve.SumDiv.toDivAddHom (C.baseChange L)
      (∑ m, Finsupp.single (pb m) 1) = _
    rw [map_sum (Work.KeyLemma.Curve.SumDiv.toDivAddHom (C.baseChange L))]
    trans ∑ m : Fin n, Work.SpecLin.ptDiv (x m)
    · apply Finset.sum_congr rfl
      intro m _
      exact toDiv_single_ptBaseChange (x m)
    · exact hx.symm
  have htoDiv' : Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange L) s' =
      Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K F L) E' := by
    show Work.KeyLemma.Curve.SumDiv.toDivAddHom (C.baseChange L)
      (∑ m, Finsupp.single (pb' m) 1) = _
    rw [map_sum (Work.KeyLemma.Curve.SumDiv.toDivAddHom (C.baseChange L))]
    trans ∑ m : Fin n, Work.SpecLin.ptDiv (x' m)
    · apply Finset.sum_congr rfl
      intro m _
      exact toDiv_single_ptBaseChange (x' m)
    · exact hx'.symm
  have hdiv' : (C.baseChange L).div h =
      Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange L) s -
        Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange L) s' := by
    rw [hdiv, htoDiv, htoDiv']
  have key : Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s' :=
    Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond (C.baseChange L) fbar hh hdiv'
  have hsumx1 : Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s =
      ∏ m : Fin n, (pb m ≫ fbar) := by
    show Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar
      (∑ m, Finsupp.single (pb m) 1) = _
    exact sumOfPoints_sum_single (C := C.baseChange L) fbar pb
  have hsumx : Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s =
      ∏ m : Fin n, Work.GenusZero.ptBaseChange (k := K) L A (x m ≫ f) := by
    rw [hsumx1]
    apply Finset.prod_congr rfl
    intro m _
    exact (Work.GenusZero.ptBaseChange_comp (k := K) L (x m) f).symm
  have hsumx'1 : Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s' =
      ∏ m : Fin n, (pb' m ≫ fbar) := by
    show Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar
      (∑ m, Finsupp.single (pb' m) 1) = _
    exact sumOfPoints_sum_single (C := C.baseChange L) fbar pb'
  have hsumx' : Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L) fbar s' =
      ∏ m : Fin n, Work.GenusZero.ptBaseChange (k := K) L A (x' m ≫ f) := by
    rw [hsumx'1]
    apply Finset.prod_congr rfl
    intro m _
    exact (Work.GenusZero.ptBaseChange_comp (k := K) L (x' m) f).symm
  have hkey : ∏ m : Fin n, Work.GenusZero.ptBaseChange (k := K) L A (x m ≫ f) =
      ∏ m : Fin n, Work.GenusZero.ptBaseChange (k := K) L A (x' m ≫ f) :=
    hsumx.symm.trans (key.trans hsumx')
  have hfinal : (Work.CurveFacts.ptBaseChangeMonoidHom (k := K) (F := L) A)
        (∏ m : Fin n, (x m ≫ f)) =
      (Work.CurveFacts.ptBaseChangeMonoidHom (k := K) (F := L) A)
        (∏ m : Fin n, (x' m ≫ f)) := by
    rw [map_prod (Work.CurveFacts.ptBaseChangeMonoidHom (k := K) (F := L) A)
        (fun m : Fin n => (x m ≫ f)) Finset.univ,
      map_prod (Work.CurveFacts.ptBaseChangeMonoidHom (k := K) (F := L) A)
        (fun m : Fin n => (x' m ≫ f)) Finset.univ]
    exact hkey
  exact Work.GenusZero.ptBaseChange_injective L A hfinal

/-- **Item A6 of the closure design, first half: the key result in the form of `sumDiv`.**

`Work.Universal.sumDiv D f E hE n hn` is the sum `Σ f(E)` of `f` over the effective divisor `E`
of degree `n`, defined as the value of the sum morphism `Work.Universal.sumMap D f n` at the point
of `Symⁿ C` classified by `E` (`Submission/Work/Universal/Basic.lean`).  The statement below says
that `Σ f` is constant on linear equivalence classes -- this is the field `kl` of
`Work.Universal.Input`.

**Deviation from the requested type, and why.**  `Work.Universal.Input.kl` binds the target `A` as
`{A : Sch K} [GrpObj A] [IsCommMonObj A]` with no properness; that type is false in general (a
nonconstant map from a curve to `𝔾ₘ` would give a counterexample to constancy on linear
equivalence classes, and every form of the key result in area KL must assume `IsProper A.hom`
because its proof runs through the constancy of a map `ℙ¹ ⟶ A`: `Curve.P1Const`, the geometric
input of the pencil argument).  We therefore add `[IsProper A.hom]`; for abelian varieties it is
an instance (`Work.AbVar.IsAbelianVariety.isProper`), so every intended consumer (the universal
property, whose target carries `[Smooth A.hom] [IsProper A.hom] [GrpObj A]`) is unaffected.  The
field `Work.Universal.Input.kl` of `Submission/Work/Universal/Basic.lean` -- and the copy
`JacClose/Inputs.lean` `KLLemma.kl` -- should be restated with `[IsProper A.hom]` added to their
binders.

Proof route.  Pass to `F̄ := AlgebraicClosure F`, where both `E` and `E'` split into points
(`SpecLin.SymGeom.split`), rewrite `sumDiv` with `Work.Universal.sumDiv_eq_of_divOf` and
`Work.Universal.sumMap_fpt`, and apply the key result in model form on the curve
`C.baseChange F̄` (`Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_uncond`); the dictionary is
`toDiv (single x 1) = ptDiv x` (`Work.GenusZero.toDiv_single_one`).  Transport along `F → F̄` with
the `ptBaseChange` API of `Work.GenusZero` (`Submission/Work/GenusZero/Basic.lean`) and descend by
`Work.GenusZero.ptBaseChange_injective`.  Base-change compatibility of `divOf` is
`SymGeom.divOf_map`, and of `sumDiv` it follows from the interface fields of
`Work.SpecLin.DivBase` together with `SymGeom`-naturality. -/
theorem kl_of_input {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : 𝟙_ (Work.GCBasics.Sch K) ⟶ C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D] :
    ∀ {A : Work.GCBasics.Sch K} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
      (f : C.toOver ⟶ A) {F : Type u} [Field F] [Algebra K F]
      (E E' : Work.GCBasics.Dv C F) (hE : E.IsEffective) (hE' : E'.IsEffective) (n : ℕ)
      (hn : Work.GCBasics.Ddeg C F E = (n : ℤ)) (hn' : Work.GCBasics.Ddeg C F E' = (n : ℤ)),
      Work.GCBasics.LinEquiv C E E' →
      Work.Universal.sumDiv D f E hE n hn = Work.Universal.sumDiv D f E' hE' n hn' := by
  intro A _ _ _ f F _ _ E E' hE hE' n hn hn' hlin
  refine Work.GroupChunk.smap_injective (X := A)
    (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) _ _ ?_
  exact kl_of_input_aux D f E E' hE hE' n hn hn' hlin

end Work.CurveFacts
