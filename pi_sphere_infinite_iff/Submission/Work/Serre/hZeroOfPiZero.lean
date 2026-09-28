import Mathlib
import Submission.Work.Serre.Engine

/-!
# `H₀(X;ℚ)` is the free `ℚ`-module on `π₀(X)`, and it is functorial

If `X` is nonempty and `f : X → Y` induces a bijection on path components, then
`H₀(f;ℚ) : H₀(X;ℚ) → H₀(Y;ℚ)` is an isomorphism.  This is the degree-`0` case of
`Work.Serre.serreK2` (`N = 1`), consumed by `Submission/Work/Serre/serreK2.lean`.

Mathlib identifies `H₀(X;ℚ)` with the coproduct of copies of `ℚ` indexed by the path
components, `TopCat.singularHomology₀Iso`, but it does **not** record the compatibility of this
isomorphism with the maps induced by a continuous map.  The whole content of this file is that
compatibility (`h0Point_natural` below), together with the bookkeeping around it:

* `h0Cycle Z z` — the `0`-cycle carried by a `0`-simplex `z` of the singular complex of `Z`, and
  `h0Point Z z` its class in `H₀(Z;ℚ)`;
* `h0Cycle_iso` / `h0Point_iso` — Mathlib's `SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom`
  transported to `TopCat.singularHomology₀Iso` and to `ZerothHomotopy`
  (`Σ.ι i ≫ Φ.inv` is the class of a point representing `i`);
* `h0Point_natural` — `h0Point` is natural: `h0Point X z ≫ H₀(f) = h0Point Y (f ∘ z)`.
  This is the naturality of the Hurewicz-type map `X → H₀(X;ℚ)` in degree `0`;
* `h0Pi0Map f` — the induced map on `ZerothHomotopy`, `h0Pi0Map_mk`, `h0Pi0Map_square` (its compatibility
  with `HomotopyGroup.pi0EquivZerothHomotopy`), and `h0Pi0Map_bijective`;
* `hZeroOfPiZero_aux` — the main computation: `Φ_X.inv ≫ H₀(f) ≫ Φ_Y.hom = ∐(h0Pi0Map f)`, so that
  conjugating `H₀(f)` by the two coproduct isomorphisms exhibits it as the coproduct of copies of
  `ℚ` along a bijection of index sets, hence an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval Simplicial
open Simplicial

namespace Work.Serre

noncomputable section

/-- The coefficient ring `ℚ`, as an object of `ModuleCat ℚ`. -/
abbrev h0Coeff : ModuleCat ℚ := ModuleCat.of ℚ ℚ

/-- `H₀(Z;ℚ)`, in the shape of the singular chain complex of `TopCat.toSSet.obj Z`.  (This is
definitionally `ratH Z 0`; the explicit shape is what the functoriality lemmas below match.) -/
abbrev h0Hom (Z : TopCat) : ModuleCat ℚ := (TopCat.toSSet.obj Z).chainComplex h0Coeff |>.homology 0

/-- Mathlib's `TopCat.singularHomology₀Iso`, with its source type spelled in the shape `h0Hom`. -/
def h0Iso (Z : TopCat) : h0Hom Z ≅ ∐ (fun _ : ZerothHomotopy Z ↦ h0Coeff) :=
  TopCat.singularHomology₀Iso Z h0Coeff

/-- The `0`-cycle of the singular chain complex of `Z` carried by a `0`-simplex `z`. -/
def h0Cycle (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    h0Coeff ⟶ (TopCat.toSSet.obj Z).chainComplex h0Coeff |>.cycles 0 :=
  ((TopCat.toSSet.obj Z).chainComplex h0Coeff).liftCycles
    ((TopCat.toSSet.obj Z).ιChainComplex z) 0 (by simp) (by simp)

/-- The class in `H₀(Z;ℚ)` of a `0`-simplex `z` (i.e. of a point of `Z`). -/
def h0Point (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) : h0Coeff ⟶ h0Hom Z :=
  h0Cycle Z z ≫ ((TopCat.toSSet.obj Z).chainComplex h0Coeff).homologyπ 0

/-- **Mathlib's computation of `H₀` at the level of the singular simplicial set.**  The class of
the `0`-simplex `z` corresponds to the basis element of the coproduct indexed by the connected
component `π₀.mk z`. -/
theorem h0Cycle_iso (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    h0Cycle Z z ≫ ((TopCat.toSSet.obj Z).chainComplex h0Coeff).homologyπ 0 ≫
        ((TopCat.toSSet.obj Z).homology₀Iso h0Coeff).hom =
      Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) ↦ h0Coeff) (SSet.π₀.mk z) := by
  unfold h0Cycle
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom (TopCat.toSSet.obj Z) h0Coeff z

/-- The identification `ZerothHomotopy Z ≃ π₀ (TopCat.toSSet.obj Z)` sends coproduct injections
along the map `ZerothHomotopy.mk ∘ TopCat.toSSetObj₀Equiv`. -/
theorem h0Sigma_ι_map_zeroth (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj Z) ↦ h0Coeff) (SSet.π₀.mk z) ≫
        ((sigmaConst.obj h0Coeff).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom =
      Sigma.ι (fun _ : ZerothHomotopy Z ↦ h0Coeff)
        (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
  rw [Functor.mapIso_hom, sigmaConst_obj_map, Sigma.ι_comp_map']
  simp

/-- **The class of a point, in the coproduct model of `H₀`.**  `h0Point Z z` is carried by the
isomorphism `TopCat.singularHomology₀Iso` to the basis element indexed by the path component of
the point corresponding to `z`. -/
theorem h0Point_iso (Z : TopCat) (z : TopCat.toSSet.obj Z _⦋0⦌) :
    h0Point Z z ≫ (h0Iso Z).hom =
      Sigma.ι (fun _ : ZerothHomotopy Z ↦ h0Coeff)
        (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
  unfold h0Iso
  have h1 := h0Cycle_iso Z z
  have h2 := h0Sigma_ι_map_zeroth Z z
  rw [show TopCat.singularHomology₀Iso Z h0Coeff = SSet.homology₀Iso (TopCat.toSSet.obj Z) h0Coeff ≪≫
      (sigmaConst.obj h0Coeff).mapIso TopCat.zerothHomotopyEquiv.toIso.symm from rfl]
  rw [Iso.trans_hom]
  unfold h0Point
  calc (h0Cycle Z z ≫ ((TopCat.toSSet.obj Z).chainComplex h0Coeff).homologyπ 0) ≫
        (((TopCat.toSSet.obj Z).homology₀Iso h0Coeff).hom ≫
          ((sigmaConst.obj h0Coeff).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom)
      = (h0Cycle Z z ≫ ((TopCat.toSSet.obj Z).chainComplex h0Coeff).homologyπ 0 ≫
          ((TopCat.toSSet.obj Z).homology₀Iso h0Coeff).hom) ≫
          ((sigmaConst.obj h0Coeff).mapIso TopCat.zerothHomotopyEquiv.toIso.symm).hom := by
        simp only [Category.assoc]
      _ = Sigma.ι (fun _ : ZerothHomotopy Z ↦ h0Coeff)
            (ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv z)) := by
        rw [h1, h2]

/-- The inverse form of `h0Point_iso`: the basis element of the coproduct indexed by the path
component of a point `x` is carried by `Φ⁻¹` to the class in `H₀` of that point. -/
theorem h0Sigma_ι_inv_iso (Z : TopCat) (x : Z) :
    Sigma.ι (fun _ : ZerothHomotopy Z ↦ h0Coeff) (ZerothHomotopy.mk x) ≫ (h0Iso Z).inv =
      h0Point Z (TopCat.toSSetObj₀Equiv.symm x) := by
  have h := h0Point_iso Z (TopCat.toSSetObj₀Equiv.symm x)
  rw [Equiv.apply_symm_apply] at h
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Naturality of the class of a point**: the chain-level functoriality of `H₀` at the level of
the generators `h0Point`.  This is the compatibility that Mathlib does not record. -/
theorem h0Point_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (z : TopCat.toSSet.obj (TopCat.of X) _⦋0⦌) :
    h0Point (TopCat.of X) z ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 =
      h0Point (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ z) := by
  unfold h0Point
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, show h0Cycle (TopCat.of X) z ≫
    HomologicalComplex.cyclesMap (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0
    = h0Cycle (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _ z) from ?_]
  unfold h0Cycle
  apply (cancel_mono (((TopCat.toSSet.obj (TopCat.of Y)).chainComplex h0Coeff).iCycles 0)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
    HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i, SSet.ι_chainComplexMap_f]

/-- `TopCat.toSSetObj₀Equiv` is natural in the space. -/
theorem h0_toSSetObj₀Equiv_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (z : TopCat.toSSet.obj (TopCat.of X) _⦋0⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _ z) =
      f (TopCat.toSSetObj₀Equiv z) := rfl

/-! ## The induced map on `π₀` -/

/-- The map on path components induced by a continuous map (Mathlib has no such map: it only knows
`ZerothHomotopy` as a quotient of the points). -/
def h0Pi0Map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  Quotient.map f (fun x y (h : Joined x y) => h.map f.continuous)

theorem h0Pi0Map_mk {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    h0Pi0Map f (ZerothHomotopy.mk x) = ZerothHomotopy.mk (f x) := Quotient.map_mk _ _ x

/-- `HomotopyGroup.pi0EquivZerothHomotopy` sends the class of a `0`-cube to the path component of
its value. -/
theorem h0Pi0EquivZerothHomotopy_mk {Z : Type} [TopologicalSpace Z] {z : Z} (γ : Ω^ (Fin 0) Z z) :
    HomotopyGroup.pi0EquivZerothHomotopy (Quotient.mk _ γ) = ZerothHomotopy.mk (γ 0) := by
  rw [HomotopyGroup.pi0EquivZerothHomotopy]
  unfold homotopyGroupEquivZerothHomotopyOfIsEmpty
  rfl

/-- `piMapN f 0` and `h0Pi0Map f` agree under the identification `π₀ ≃ ZerothHomotopy` of
`HomotopyGroup.pi0EquivZerothHomotopy`. -/
theorem h0Pi0Map_square {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} (f : C(X, Y)) (a : π_ 0 X x₀) :
    h0Pi0Map f (HomotopyGroup.pi0EquivZerothHomotopy a)
      = HomotopyGroup.pi0EquivZerothHomotopy (piMapN f 0 x₀ a) := by
  induction a using Quotient.inductionOn with
  | h γ =>
    rw [h0Pi0EquivZerothHomotopy_mk, piMapN_apply_mk, h0Pi0EquivZerothHomotopy_mk, h0Pi0Map_mk,
      Work.StemsB.genLoopMap_apply]

/-- A map which is a bijection on `π₀` at one base point is a bijection on `ZerothHomotopy`. -/
theorem h0Pi0Map_bijective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X}
    (f : C(X, Y)) (h : Function.Bijective (piMapN f 0 x₀)) :
    Function.Bijective (h0Pi0Map f) := by
  have hcomp : h0Pi0Map f = ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := f x₀)) ∘
      ((piMapN f 0 x₀) ∘ ⇑(HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).symm) := by
    funext i
    rw [Function.comp_apply, Function.comp_apply]
    have h' := h0Pi0Map_square (x₀ := x₀) f
      ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).symm i)
    rw [Equiv.apply_symm_apply] at h'
    exact h'
  rw [hcomp]
  exact Function.Bijective.comp (HomotopyGroup.pi0EquivZerothHomotopy (x := f x₀)).bijective
    (h.comp (HomotopyGroup.pi0EquivZerothHomotopy (x := x₀)).symm.bijective)

/-- **Degree `0` of K2.**  If `f : X → Y` is a bijection on `π₀` (at every base point), then
`H₀(f;ℚ)` is an isomorphism.

The proof conjugates the induced map on homology by the two coproduct isomorphisms `h0Iso`; the
conjugate is the coproduct of copies of `ℚ` along the bijection `h0Pi0Map f` of the index sets, by
the naturality of `h0Point`, and a functor carries the resulting isomorphism of index types to an
isomorphism.  (Here `H₀` is written in the shape of the singular chain complex of
`TopCat.toSSet.obj -`, which is definitionally the shape in which `ratHomologyMap` is stated.) -/
theorem hZeroOfPiZero_aux {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (h : ∀ x : X, Function.Bijective (piMapN f 0 x)) :
    IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hbij : Function.Bijective (h0Pi0Map f) := h0Pi0Map_bijective f (h x₀)
  have hcf : IsIso (TypeCat.ofHom (h0Pi0Map f)) := by
    rw [show TypeCat.ofHom (h0Pi0Map f) =
      (Equiv.toIso (Equiv.ofBijective (h0Pi0Map f) hbij)).hom from rfl]
    exact Iso.isIso_hom _
  have hmk : IsIso ((sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f))) :=
    Functor.map_isIso (sigmaConst.obj h0Coeff) (TypeCat.ofHom (h0Pi0Map f))
  -- the conjugate of `H₀(f)` is the coproduct map along `h0Pi0Map f`
  have hg : (h0Iso (TopCat.of X)).inv ≫
        HomologicalComplex.homologyMap
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
        (h0Iso (TopCat.of Y)).hom = (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) := by
    apply Sigma.hom_ext
    intro i
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective i
    have hidx : ZerothHomotopy.mk (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _
        (TopCat.toSSetObj₀Equiv.symm x))) = h0Pi0Map f (ZerothHomotopy.mk x) := by
      rw [h0_toSSetObj₀Equiv_natural, Equiv.apply_symm_apply, h0Pi0Map_mk]
    calc Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
          ((h0Iso (TopCat.of X)).inv ≫ HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
            (h0Iso (TopCat.of Y)).hom)
        = (Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
            (h0Iso (TopCat.of X)).inv) ≫ (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
            (h0Iso (TopCat.of Y)).hom) := by simp only [Category.assoc]
      _ = h0Point (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
            (HomologicalComplex.homologyMap
              (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 ≫
              (h0Iso (TopCat.of Y)).hom) := by rw [h0Sigma_ι_inv_iso]
      _ = (h0Point (TopCat.of X) (TopCat.toSSetObj₀Equiv.symm x) ≫
            HomologicalComplex.homologyMap
              (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0) ≫
            (h0Iso (TopCat.of Y)).hom := by simp only [Category.assoc]
      _ = h0Point (TopCat.of Y) ((TopCat.toSSet.map (TopCat.ofHom f)).app _
            (TopCat.toSSetObj₀Equiv.symm x)) ≫ (h0Iso (TopCat.of Y)).hom := by
            rw [h0Point_natural]
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ h0Coeff) (ZerothHomotopy.mk
            (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map (TopCat.ofHom f)).app _
              (TopCat.toSSetObj₀Equiv.symm x)))) :=
            h0Point_iso (TopCat.of Y) _
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of Y) ↦ h0Coeff)
            (h0Pi0Map f (ZerothHomotopy.mk x)) := by rw [hidx]
      _ = Sigma.ι (fun _ : ZerothHomotopy (TopCat.of X) ↦ h0Coeff) (ZerothHomotopy.mk x) ≫
            (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) := by
          rw [sigmaConst_obj_map, Sigma.ι_comp_map']
          simp
  have hcomp : HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) h0Coeff) 0 =
      (h0Iso (TopCat.of X)).hom ≫ ((sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f))) ≫
        (h0Iso (TopCat.of Y)).inv := by
    rw [← hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hcomp]
  let e : ZerothHomotopy (TopCat.of X) ≅ ZerothHomotopy (TopCat.of Y) :=
    Equiv.toIso (Equiv.ofBijective (h0Pi0Map f) hbij)
  have hmap : (sigmaConst.obj h0Coeff).map (TypeCat.ofHom (h0Pi0Map f)) =
      (sigmaConst.obj h0Coeff).map e.hom := rfl
  rw [hmap]
  exact Iso.isIso_hom ((h0Iso (TopCat.of X)) ≪≫ (sigmaConst.obj h0Coeff).mapIso e ≪≫
    (h0Iso (TopCat.of Y)).symm)

/-- **`H₀` is the free `ℚ`-module on `π₀`, so a `π₀`-bijection induces an isomorphism in degree `0`.**

If `X` is nonempty and `f : X → Y` induces a bijection on path components (equivalently, using
Mathlib's `HomotopyGroup (Fin 0) X x ≃ ZerothHomotopy X`, on `π₀`), then
`H₀(f; ℚ) : H₀(X; ℚ) → H₀(Y; ℚ)` is an isomorphism.  It is the degree-`0` case of
`Work.Serre.serreK2` for `N = 1`, consumed by `Submission/Work/Serre/serreK2.lean`.

Route: Mathlib's `TopCat.singularHomology₀Iso` identifies `H₀(-;ℚ)` with the coproduct of copies of
`ℚ` indexed by `ZerothHomotopy`, and `HomotopyGroup.pi0EquivZerothHomotopy` identifies the induced
maps; the induced map of coproducts along a bijection is an isomorphism.  (The hypothesis
`[Nonempty X]` is needed: for `X` empty the hypothesis is vacuous while `H₀(∅;ℚ) = 0 ≇ H₀(pt;ℚ)`.) -/
theorem hZeroOfPiZero {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (h : ∀ x : X, Function.Bijective (Work.Serre.piMapN f 0 x)) :
    _root_.CategoryTheory.IsIso (Work.Serre.ratHomologyMap f 0) :=
  hZeroOfPiZero_aux f h

end

end Work.Serre
