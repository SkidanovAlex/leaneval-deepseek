import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The generator of a relative perfect closure

Let `k` be a field, `L / k` a field extension and `x ∈ L` transcendental over `k` with `L / k(x)`
finite dimensional.  Write `K = k(x) ⊆ L` and let `P = perfectClosure K L` be the relative perfect
closure of `K` in `L`, so that `P / K` is finite and purely inseparable.  If `y : P` is the image
of `x` (i.e. `(y : L) = x`), then

* `y` is still transcendental over `k`;
* `P` is finite dimensional and purely inseparable over `k(y)`.

In fact `k(y) = k(x) = K` as subfields of `P`: since `K` is generated over `k` by `x = y`, the
subfields `K` and `k(y)` of `P` are equal, and the assertions follow from the corresponding
statements for `K`.
-/

open scoped Classical IntermediateField.algebraAdjoinAdjoin

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CurveBasics.Order

theorem perfectClosure_adjoin_gen {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    (y : ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L))
    (hy : (y : L) = x) :
    Transcendental k y ∧
    FiniteDimensional (IntermediateField.adjoin k ({y} : Set ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)))
      ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L) ∧
    IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)))
      ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L) := by
  -- Abbreviations for the two fields playing a role.
  let K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  let P : IntermediateField ↥K L := perfectClosure ↥K L
  -- The base-change structure making `P` an `L`-algebra over `k`.
  haveI : IsScalarTower k ↥P L := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IntermediateField.algebraMap_apply]
    exact Subalgebra.coe_algebraMap P.toSubalgebra c)
  -- `Q = k(y)` inside `P`, and the inclusion `P → L`.
  let Q : IntermediateField k ↥P := IntermediateField.adjoin k ({y} : Set ↥P)
  let f : ↥P →ₐ[k] L := IsScalarTower.toAlgHom k ↥P L
  have hf : f y = x := hy
  -- The image of `Q` in `L` is `k(x) = K`.
  have hmap : Q.map f = K := by
    rw [show Q = IntermediateField.adjoin k ({y} : Set ↥P) from rfl,
      IntermediateField.adjoin_map k ({y} : Set ↥P) f]
    rw [show f '' ({y} : Set ↥P) = ({x} : Set L) by
      rw [Set.image_singleton]
      exact congrArg Set.singleton hf]
  -- The resulting identification `k(y) ≃ₐ[k] K`, compatible with the inclusions into `L`.
  let ψ : ↥Q ≃ₐ[k] ↥K := (IntermediateField.equivMap Q f).trans (IntermediateField.equivOfEq hmap)
  have hval : ∀ z : ↥Q, (ψ z : L) = (z : L) := by
    intro z
    have h2 : ∀ w : ↥(Q.map f), ((IntermediateField.equivOfEq hmap) w : L) = (w : L) :=
      fun w => rfl
    have h1 : ∀ z : ↥Q, ((IntermediateField.equivMap Q f) z : L) = f z :=
      fun z => IntermediateField.coe_equivMap_apply Q f z
    rw [show ψ = (IntermediateField.equivMap Q f).trans (IntermediateField.equivOfEq hmap) from rfl,
      AlgEquiv.trans_apply, h2, h1]
    rfl
  -- `y` is transcendental, being the image of the transcendental element `x`.
  have hy_t : Transcendental k y := fun hyalg => hx (by
    have hfy : (IsScalarTower.toAlgHom k ↥P L) y = x := hy
    rw [← hfy]
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom k ↥P L)
      (fun _ _ h => (algebraMap ↥P L).injective h)).2 hyalg)
  -- Transport the `K`-structure on `P` to a `k(y)`-structure along `ψ`.
  letI : Algebra ↥K ↥Q := (ψ.symm : ↥K →ₐ[k] ↥Q).toRingHom.toAlgebra
  haveI hST : IsScalarTower ↥K ↥Q ↥P := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    rw [IntermediateField.coe_algebraMap_apply, IntermediateField.algebraMap_apply]
    show (a : L) = ((ψ.symm a) : L)
    have hh := hval (ψ.symm a)
    rw [AlgEquiv.apply_symm_apply] at hh
    exact hh)
  exact ⟨hy_t, Module.Finite.of_restrictScalars_finite ↥K ↥Q ↥P,
    IsPurelyInseparable.tower_top ↥K ↥Q ↥P⟩

end Work.CurveBasics.Order
