import Mathlib
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Cohomology.Pullback
import Submission.Work.Serre.serreK2Int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre.Assembly

/-!
# `H₀(-; R)` for a general coefficient ring `R`

The whole content of `Submission/Work/Serre/hZeroOfPiZero.lean` is insensitive to the coefficient
ring: Mathlib's `TopCat.singularHomology₀Iso` identifies `H₀(Z;R)` with the coproduct of copies of
the coefficient object `R` indexed by the path components of `Z`, for an *arbitrary* coefficient
object `R` of an abelian category with coproducts.  This file repeats that argument with the
coefficient object `R : ModuleCat R` kept general, and specialises to `R = ℤ` to obtain the
integral form of the degree-`0` range Whitehead statement.

* `genCoeff`, `genHom`, `genIso`, `genCycle`, `genPoint`: the coefficients, `H₀`, Mathlib's
  coproduct comparison, the `0`-cycle of a point and its class in `H₀`;
* `genCycle_iso`, `genSigma_ι_map_zeroth`, `genPoint_iso`, `genSigma_ι_inv_iso`: the comparison
  with the coproduct model, at the level of a point;
* `genPoint_natural`: the naturality of that class, which is the compatibility Mathlib does not
  record (`Work.Serre.h0Point_natural` in the rational case);
* `genAux`: the main computation, `Φ_X.inv ≫ H₀(f) ≫ Φ_Y.hom = ∐(h0Pi0Map f)`;
* `hZeroOfPiZeroInt`: the requested integral statement.

The generic statements about `π₀`/`ZerothHomotopy` (`Work.Serre.h0Pi0Map`, `h0Pi0Map_mk`,
`h0Pi0EquivZerothHomotopy_mk`, `h0Pi0Map_square`, `h0Pi0Map_bijective`,
`h0_toSSetObj₀Equiv_natural`) do not mention the coefficient ring at all, so they are reused
verbatim from `Submission/Work/Serre/hZeroOfPiZero.lean`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval Simplicial
open Simplicial

noncomputable section

/-- The coefficient object `R` of `ModuleCat R`. -/
abbrev genCoeff (R : Type) [CommRing R] : ModuleCat R := ModuleCat.of R R

/-- `H₀(Z;R)`, in the shape of the singular chain complex of `TopCat.toSSet.obj Z`. -/
abbrev genHom (R : Type) [CommRing R] (Z : TopCat) : ModuleCat R :=
  (TopCat.toSSet.obj Z).chainComplex (genCoeff R) |>.homology 0

/-- Mathlib's `TopCat.singularHomology₀Iso`, with its source type spelled in the shape `genHom`. -/
def genIso (R : Type) [CommRing R] (Z : TopCat) :
    genHom R Z ≅ ∐ (fun _ : ZerothHomotopy Z ↦ genCoeff R) :=
  TopCat.singularHomology₀Iso Z (genCoeff R)

/-- The `0`-cycle of the singular chain complex of `Z` carried by a `0`-simplex `z`. -/
def genCycle (R : Type) [CommRing R] (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    genCoeff R ⟶ (TopCat.toSSet.obj Z).chainComplex (genCoeff R) |>.cycles 0 :=
  ((TopCat.toSSet.obj Z).chainComplex (genCoeff R)).liftCycles
    ((TopCat.toSSet.obj Z).ιChainComplex z) 0 (by simp) (by simp)

/-- The class in `H₀(Z;R)` of a `0`-simplex `z` (i.e. of a point of `Z`). -/
def genPoint (R : Type) [CommRing R] (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    genCoeff R ⟶ genHom R Z :=
  genCycle R Z z ≫ ((TopCat.toSSet.obj Z).chainComplex (genCoeff R)).homologyπ 0

/-- **Mathlib's computation of `H₀` at the level of the singular simplicial set.**  The class of
the `0`-simplex `z` corresponds to the basis element of the coproduct indexed by the connected
component `π₀.mk z`. -/
theorem genCycle_iso (R : Type) [CommRing R] (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    genCycle R Z z ≫ ((TopCat.toSSet.obj Z).chainComplex (genCoeff R)).homologyπ 0 ≫
        ((TopCat.toSSet.obj Z).homology₀Iso (genCoeff R)).hom =
      Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) ↦ genCoeff R) (SSet.π₀.mk z) := by
  unfold genCycle
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom (TopCat.toSSet.obj Z)
    (genCoeff R) z

/-- The identification `ZerothHomotopy Z ≃ π₀ (TopCat.toSSet.obj Z)` sends coproduct injections
along the map `ZerothHomotopy.mk ∘ TopCat.toSSetObj₀Equiv`. -/
theorem genSigma_ι_map_zeroth (R : Type) [CommRing R] (Z : TopCat)
    (z : TopCat.toSSet.obj Z _⦋0⦌) :
    Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) ↦ genCoeff R) (SSet.π₀.mk z) ≫
        ((sigmaConst.obj (genCoeff R)).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom =
      Sigma.ι (fun _ : ZerothHomotopy Z ↦ genCoeff R)
        (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
  rw [Functor.mapIso_hom, sigmaConst_obj_map, Sigma.ι_comp_map']
  simp

/-- **The class of a point, in the coproduct model of `H₀`.** -/
theorem genPoint_iso (R : Type) [CommRing R] (Z : TopCat)
    (z : TopCat.toSSet.obj Z _⦋0⦌) :
    genPoint R Z z ≫ (genIso R Z).hom =
      Sigma.ι (fun _ : ZerothHomotopy Z ↦ genCoeff R)
        (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
  unfold genIso
  have h1 := genCycle_iso R Z z
  have h2 := genSigma_ι_map_zeroth R Z z
  rw [show TopCat.singularHomology₀Iso Z (genCoeff R) =
      SSet.homology₀Iso (TopCat.toSSet.obj Z) (genCoeff R) ≪≫
      (sigmaConst.obj (genCoeff R)).mapIso TopCat.zerothHomotopyEquiv.toIso.symm from rfl]
  rw [Iso.trans_hom]
  unfold genPoint
  calc (genCycle R Z z ≫ ((TopCat.toSSet.obj Z).chainComplex (genCoeff R)).homologyπ 0) ≫
        (((TopCat.toSSet.obj Z).homology₀Iso (genCoeff R)).hom ≫
          ((sigmaConst.obj (genCoeff R)).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom)
      = (genCycle R Z z ≫ ((TopCat.toSSet.obj Z).chainComplex (genCoeff R)).homologyπ 0 ≫
          ((TopCat.toSSet.obj Z).homology₀Iso (genCoeff R)).hom) ≫
          ((sigmaConst.obj (genCoeff R)).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom := by
        simp only [Category.assoc]
      _ = Sigma.ι (fun _ : ZerothHomotopy Z ↦ genCoeff R)
            (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
        rw [h1, h2]

/-- The inverse form of `genPoint_iso`. -/
theorem genSigma_ι_inv_iso (R : Type) [CommRing R] (Z : TopCat) (x : Z) :
    Sigma.ι (fun _ : ZerothHomotopy Z ↦ genCoeff R) (ZerothHomotopy.mk x) ≫
        (genIso R Z).inv =
      genPoint R Z (TopCat.toSSetObj₀Equiv.symm x) := by
  have h := genPoint_iso R Z (TopCat.toSSetObj₀Equiv.symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Naturality of the class of a point**, with general coefficients. -/
theorem genPoint_natural (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (z : TopCat.toSSet.obj (TopCat.of X) _⦋0⦌) :
    genPoint R (TopCat.of X) z ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 =
      genPoint R (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ z) := by
  unfold genPoint
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, show genCycle R (TopCat.of X) z ≫
    HomologicalComplex.cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
      (genCoeff R)) 0
    = genCycle R (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ z) from ?_]
  unfold genCycle
  apply (cancel_mono (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex (genCoeff R)).iCycles 0)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, SSet.ι_chainComplexMap_f]

/-- **The main computation, with general coefficients.**  `genAux` conjugates `H₀(f)` by the two
coproduct isomorphisms `genIso`; the conjugate is the coproduct of copies of `R` along the
bijection `h0Pi0Map f` of the index sets, by the naturality of `genPoint`. -/
theorem genAux (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] (f : C(X, Y)) (h : ∀ x : X, Function.Bijective (piMapN f 0 x)) :
    IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hbij : Function.Bijective (h0Pi0Map f) := h0Pi0Map_bijective f (h x₀)
  have hg : (genIso R (TopCat.of X)).inv ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 ≫
        (genIso R (TopCat.of Y)).hom =
      (sigmaConst.obj (genCoeff R)).map (TypeCat.ofHom (h0Pi0Map f)) := by
    apply Sigma.hom_ext
    intro i
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective i
    have hidx : ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv
        ((TopCat.toSSet.map (TopCat.ofHom f)).app _
        (TopCat.toSSetObj₀Equiv.symm x))) = h0Pi0Map f (ZerothHomotopy.mk x) := by
      rw [h0_toSSetObj₀Equiv_natural, Equiv.apply_symm_apply, h0Pi0Map_mk]
    calc Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ genCoeff R)
            (ZerothHomotopy.mk x) ≫
          ((genIso R (TopCat.of X)).inv ≫ HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 ≫
            (genIso R (TopCat.of Y)).hom)
        = (Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ genCoeff R)
              (ZerothHomotopy.mk x) ≫
            (genIso R (TopCat.of X)).inv) ≫ (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 ≫
            (genIso R (TopCat.of Y)).hom) := by simp only [Category.assoc]
      _ = genPoint R (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
            (HomologicalComplex.homologyMap
              (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 ≫
              (genIso R (TopCat.of Y)).hom) := by rw [genSigma_ι_inv_iso]
      _ = (genPoint R (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
            HomologicalComplex.homologyMap
              (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0) ≫
            (genIso R (TopCat.of Y)).hom := by simp only [Category.assoc]
      _ = genPoint R (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _
            (TopCat.toSSetObj₀Equiv.symm x)) ≫ (genIso R (TopCat.of Y)).hom := by
            rw [genPoint_natural]
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ genCoeff R) (ZerothHomotopy.mk
            (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _
              (TopCat.toSSetObj₀Equiv.symm x)))) :=
            genPoint_iso R (TopCat.of Y) _
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ genCoeff R)
            (h0Pi0Map f (ZerothHomotopy.mk x)) := by rw [hidx]
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ genCoeff R)
            (ZerothHomotopy.mk x) ≫
            (sigmaConst.obj (genCoeff R)).map (TypeCat.ofHom (h0Pi0Map f)) := by
          rw [sigmaConst_obj_map, Sigma.ι_comp_map']
          simp
  have hcomp : HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (genCoeff R)) 0 =
      (genIso R (TopCat.of X)).hom ≫
        ((sigmaConst.obj (genCoeff R)).map (TypeCat.ofHom (h0Pi0Map f))) ≫
        (genIso R (TopCat.of Y)).inv := by
    rw [← hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hcomp]
  let e : ZerothHomotopy (TopCat.of X) ≅ ZerothHomotopy (TopCat.of Y) :=
    Equiv.toIso (Equiv.ofBijective (h0Pi0Map f) hbij)
  have hmap : (sigmaConst.obj (genCoeff R)).map (TypeCat.ofHom (h0Pi0Map f)) =
      (sigmaConst.obj (genCoeff R)).map e.hom := rfl
  rw [hmap]
  exact Iso.isIso_hom ((genIso R (TopCat.of X)) ≪≫ (sigmaConst.obj (genCoeff R)).mapIso e ≪≫
    (genIso R (TopCat.of Y)).symm)

-- **Degree `0` of the range Whitehead statement, over `ℤ`.**  A `π₀`-bijection induces an
-- isomorphism on `H₀(-;ℤ)`.
--
-- This is the integral form of `Work.Serre.hZeroOfPiZero`
-- (`Submission/Work/Serre/hZeroOfPiZero.lean`), which is stated over `ℚ`.  The proof there
-- identifies `H₀(Z;R)` with the coproduct of copies of the coefficient object `R` indexed by the
-- path components of `Z` (`TopCat.singularHomology₀Iso`, which is available for an arbitrary
-- coefficient object `R`), shows that the class in `H₀` of a point of `Z` is natural
-- (`h0Point_natural`), and conjugates the induced map `H₀(f)` by the two coproduct isomorphisms;
-- the conjugate is the coproduct of copies of `R` along the bijection `h0Pi0Map f` of the index
-- types, hence an isomorphism.  Copying that proof with the coefficient object `ℤ`
-- (`h0Coeff := ModuleCat.of ℤ ℤ`) — or proving it for a general coefficient object `R` and
-- specialising — gives the statement.  The hypothesis `[Nonempty X]` is necessary: for `X` empty
-- the `π₀`-hypothesis is vacuous while `H₀(∅;ℤ) = 0` need not be isomorphic to `H₀(Y;ℤ)`. -/
theorem hZeroOfPiZeroInt {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (h : ∀ x : X, Function.Bijective (Work.Serre.piMapN f 0 x)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) 0) :=
  genAux ℤ f h

end

end Work.Serre.Assembly
