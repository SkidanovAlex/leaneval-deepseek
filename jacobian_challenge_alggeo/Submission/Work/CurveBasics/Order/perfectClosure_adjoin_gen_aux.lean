import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Order

set_option linter.style.haveILetI false

/-- For `x` transcendental over `k`, put `K = k(x) ⊆ L` and let `P` be the relative perfect
closure of `K` in `L` (so `P / K` is finite and purely inseparable).  If `y : P` is the image of
`x`, then `y` is transcendental over `k` and the extension `P / k(y)` is finite and purely
inseparable (indeed `k(y) = K` as subfields of `P`). -/
theorem perfectClosure_adjoin_gen_aux {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    (y : ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L))
    (hy : (y : L) = x) :
    Transcendental k y ∧
    FiniteDimensional (IntermediateField.adjoin k ({y} : Set ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)))
      ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L) ∧
    IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)))
      ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L) := by
  let K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  let P : IntermediateField ↥K L := perfectClosure ↥K L
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self k x
  -- `K` is contained in `P` (viewed as an intermediate field of `L / k`).
  have hle : K ≤ P.restrictScalars k := by
    intro a ha
    exact P.set_range_subset ⟨⟨a, ha⟩, rfl⟩
  -- The element `x`, viewed in `K`, generates `K` over `k`.
  have hgen : IntermediateField.adjoin k ({(⟨x, hxK⟩ : ↥K)} : Set ↥K) = ⊤ := by
    apply IntermediateField.lift_injective K
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
  have hcast : ∀ r : k, ((algebraMap k ↥P) r : L) = algebraMap k L r :=
    fun r => Subalgebra.coe_algebraMap (R := ↥K) (A := L) (S := P.toSubalgebra) r
  -- The inclusion `K ↪ P` as a `k`-algebra map.
  let φ : ↥K →ₐ[k] ↥P :=
    { toFun := fun a => ⟨algebraMap ↥K L a, P.algebraMap_mem a⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp
      commutes' := fun r => by
        apply Subtype.ext
        show algebraMap ↥K L (algebraMap k ↥K r) = ((algebraMap k ↥P) r : L)
        rw [← IsScalarTower.algebraMap_apply k ↥K L r]
        exact (hcast r).symm }
  have hφx : φ ⟨x, hxK⟩ = y := by
    apply Subtype.ext
    change (algebraMap ↥K L ⟨x, hxK⟩ : L) = (y : L)
    rw [hy]
    rfl
  -- The image of `K` in `P` is `k(y)`.
  have hfr : φ.fieldRange = (IntermediateField.adjoin k ({y} : Set ↥P)) := by
    rw [AlgHom.fieldRange_eq_map, ← hgen, IntermediateField.adjoin_map, Set.image_singleton, hφx]
  -- `y` is transcendental over `k`.
  have htrans_x' : Transcendental k (⟨x, hxK⟩ : ↥K) := by
    rw [Subalgebra.transcendental_iff_transcendental_val]
    simpa using hx
  have htrans_y : Transcendental k y := by
    have h : Transcendental k (φ ⟨x, hxK⟩) :=
      (isAlgebraic_algHom_iff φ φ.injective).not.mpr htrans_x'
    rwa [hφx] at h
  let K' : IntermediateField k ↥P := IntermediateField.adjoin k ({y} : Set ↥P)
  -- The ring hom `K → K'` induced by `φ`, whose image is everything.
  have hmem : ∀ a : ↥K, φ a ∈ K' := fun a => by
    show φ a ∈ IntermediateField.adjoin k ({y} : Set ↥P)
    rw [← hfr]
    exact ⟨a, rfl⟩
  let ψ : ↥K →+* K' :=
    { toFun := fun a => ⟨φ a, hmem a⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a b) }
  letI : Algebra ↥K K' := ψ.toAlgebra
  haveI hST : IsScalarTower ↥K K' ↥P :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change algebraMap K' ↥P (ψ c) = algebraMap ↥K ↥P c
      rw [show algebraMap K' ↥P (ψ c) = ((ψ c : ↥P)) from rfl,
        show ((ψ c : ↥P)) = φ c from rfl]
      rfl)
  -- `P` is finite and purely inseparable over `K'`, because it is so over `K = K'`.
  haveI : Module.Finite ↥K ↥P := inferInstance
  have hfin : FiniteDimensional K' ↥P := Module.Finite.of_restrictScalars_finite ↥K K' ↥P
  have hpure : IsPurelyInseparable K' ↥P := IsPurelyInseparable.tower_top ↥K K' ↥P
  exact ⟨htrans_y, hfin, hpure⟩

end Work.CurveBasics.Order
