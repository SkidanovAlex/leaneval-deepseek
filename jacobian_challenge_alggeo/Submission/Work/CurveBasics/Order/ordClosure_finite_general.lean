import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.perfectClosure_adjoin_gen
import Submission.Work.CurveBasics.Order.perfectClosure_separable_of_normal
import Submission.Work.CurveBasics.Order.kx_pure_insep
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_general_assembly
import Submission.Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of the integral closure of `k[h]` in the function field of a curve

The main result of this file is `Work.CurveBasics.Order.ordClosure_finite_general`: for a curve
`C` over a field `k` and `h ∈ K(C)` transcendental over `k` with `[K(C) : k(h)]` finite, the
integral closure of `k[h]` in `K(C)` is a finite `k[h]`-module.

Since `k[h] = Algebra.adjoin k {h}` and the integral closure is `integralClosure (k[h]) K(C)`,
this is the specialisation of the classical theorem that `k[x] ≅ k[X]` is *Japanese* (Nagata's
N-2 property): the normalisation of `k[x]` in a finite extension of `k(x)` is a finite module.

The proof of the general theorem is assembled here from lemmas that already exist in the
workspace (all of them free of placeholders and resting only on the usual axioms):

* `normalClosure_reduction` (from `integralClosure_adjoin_finite_general_assembly`) reduces the
  general case to the *normal* case by passing to a normal closure;
* the normal case splits along the relative perfect closure `P = perfectClosure k(x) L`: the
  integral closure of `k[x]` in `P` is finite because `P/k(x)` is finite purely inseparable
  (`kx_pure_insep`), and the remaining step `P → L` is a finite *separable* extension, handled by
  Mathlib's `IsIntegralClosure.finite`; the two are glued with `glue_general` below.
-/

open scoped IntermediateField.algebraAdjoinAdjoin

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CurveBasics.Order

open Work.CurveBasics

/-! ## Gluing and transfer lemmas -/

/-- **Gluing.** If `A ⊆ B ⊆ N ⊆ L`, `B` is a finite `A`-algebra, `N` is the fraction field of
`B` (with `L / N` finite separable), and `A`, `B` are Noetherian integrally closed domains, then
the integral closure of `A` in `L` is a finite `A`-module.

(The statement and proof are those of `Work.CurveBasics.Order.glue_general`; they are reproduced
here so that this file is self-contained.) -/
theorem ordClosure_finite_general_glue
    {A B N L : Type*} [CommRing A] [CommRing B] [Field N] [Field L]
    [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N] [IsFractionRing B N]
    [Algebra A L] [Algebra N L] [Algebra B L] [IsScalarTower A N L] [IsScalarTower B N L]
    [IsScalarTower A B L]
    [FiniteDimensional N L] [Algebra.IsSeparable N L]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (h1 : Module.Finite A B) :
    Module.Finite A ↥(integralClosure A L) := by
  haveI : Module.Finite A B := h1
  haveI h3 : Module.Finite B ↥(integralClosure B L) :=
    IsIntegralClosure.finite B N L ↥(integralClosure B L)
  have h4 : Module.Finite A ↥(integralClosure B L) :=
    Module.Finite.trans B ↥(integralClosure B L)
  have hEq : Subalgebra.restrictScalars A (integralClosure B L) = integralClosure A L := by
    ext y
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun hy => isIntegral_trans (A := B) y hy, fun hy => IsIntegral.tower_top hy⟩
  rw [← hEq]
  exact h4

/-! ## The normal case -/

/-- **The normal case.** If `L / k(x)` is finite and normal, then the integral closure of `k[x]`
in `L` is a finite `k[x]`-module.  The purely inseparable part is `kx_pure_insep`, and the
separable part is glued with `ordClosure_finite_general_glue`, using that `L` is separable over
its relative perfect closure (`perfectClosure_separable_of_normal`).

The outline of the assembly (perfect closure, the transfer along `k[y] ≅ k[x]`, and the gluing)
is the one developed in the workspace in `Work.CurveBasics.Order.reduce_general_to_pure` and
`Work.CurveBasics.Order.kx_normal_aux`; the version below is self-contained and uses only the
placeholders-free lemmas named above. -/
theorem ordClosure_finite_general_normal_case {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    [Normal (IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  let A : Subalgebra k L := Algebra.adjoin k ({x} : Set L)
  let K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self k x
  haveI hfdK : FiniteDimensional K L :=
    ‹FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L›
  haveI hNK : Normal K L := ‹Normal (IntermediateField.adjoin k ({x} : Set L)) L›
  haveI hSTAKL : IsScalarTower ↥A ↥K L := by
    show IsScalarTower ↥(Algebra.adjoin k ({x} : Set L))
      ↥(IntermediateField.adjoin k ({x} : Set L)) L
    infer_instance
  haveI hFrAK : IsFractionRing ↥A ↥K := by
    show IsFractionRing ↥(Algebra.adjoin k ({x} : Set L))
      ↥(IntermediateField.adjoin k ({x} : Set L))
    infer_instance
  let P : IntermediateField ↥K L := perfectClosure ↥K L
  haveI hfdKP : FiniteDimensional ↥K ↥P := inferInstance
  haveI hpiKP : IsPurelyInseparable ↥K ↥P := inferInstance
  haveI hfdPL : FiniteDimensional ↥P L := inferInstance
  haveI hsepPL : Algebra.IsSeparable ↥P L := perfectClosure_separable_of_normal
  haveI tAKP : IsScalarTower ↥A ↥K ↥P := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tAPL : IsScalarTower ↥A ↥P L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the element `y = x` viewed in `P`
  have hxP : x ∈ (P : Set L) := by
    have h1 : ((⟨x, hxK⟩ : ↥K) : L) = x := rfl
    rw [← h1]
    exact Subalgebra.algebraMap_mem _ (⟨x, hxK⟩ : ↥K)
  let y : ↥P := ⟨x, hxP⟩
  have hyval : (y : L) = x := rfl
  obtain ⟨hyT, hyfd, hypi⟩ := perfectClosure_adjoin_gen x hx y hyval
  haveI hfdA' : FiniteDimensional (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hyfd
  haveI hpiA' : IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hypi
  have hpure : Module.Finite ↥(Algebra.adjoin k ({y} : Set ↥P))
      ↥(integralClosure ↥(Algebra.adjoin k ({y} : Set ↥P)) ↥P) :=
    kx_pure_insep (k := k) (L := ↥P) y hyT
  -- transfer to `A = k[x]`
  haveI hSTkPL : IsScalarTower k ↥P L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinclP : Function.Injective (IsScalarTower.toAlgHom k ↥P L) := by
    intro a b h; exact Subtype.ext h
  have hmap : (Algebra.adjoin k ({y} : Set ↥P)).map (IsScalarTower.toAlgHom k ↥P L) = A := by
    show (Algebra.adjoin k ({y} : Set ↥P)).map (IsScalarTower.toAlgHom k ↥P L)
      = Algebra.adjoin k ({x} : Set L)
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  -- The identity on `L` identifies the `k`-subalgebras `k[y] ⊆ P` and `A = k[x] ⊆ L`.
  let f' : ↥(Algebra.adjoin k ({y} : Set ↥P)) →+* ↥A :=
    { toFun := fun b => ⟨(b : L), by
        rw [← hmap]
        exact Subalgebra.mem_map.mpr ⟨b, b.2, rfl⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hf'inj : Function.Injective f' := by
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥A => (z : L)) h))
  have hf'surj : Function.Surjective f' := by
    intro a
    have ha : (a : L) ∈ (Algebra.adjoin k ({y} : Set ↥P)).map
        (IsScalarTower.toAlgHom k ↥P L) := by
      rw [hmap]; exact a.2
    obtain ⟨b, hb, hb'⟩ := Subalgebra.mem_map.mp ha
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    dsimp only [f']
    exact hb'
  let Φ : ↥(Algebra.adjoin k ({y} : Set ↥P)) ≃+* ↥A :=
    RingEquiv.ofBijective f' ⟨hf'inj, hf'surj⟩
  have hΦcoe : ∀ b : ↥(Algebra.adjoin k ({y} : Set ↥P)), ((Φ b : ↥A) : L) = (b : L) :=
    fun b => rfl
  have hΦsymmcoe : ∀ a : ↥A, ((Φ.symm a : ↥(Algebra.adjoin k ({y} : Set ↥P))) : L) = (a : L) := by
    intro a
    have h1 : (Φ (Φ.symm a) : ↥A) = a := RingEquiv.apply_symm_apply Φ a
    have h2 : ((Φ (Φ.symm a) : ↥A) : L) = (a : L) := by rw [h1]
    rwa [hΦcoe] at h2
  have hcompat : (algebraMap ↥(Algebra.adjoin k ({y} : Set ↥P)) ↥P).comp Φ.symm.toRingHom
      = algebraMap ↥A ↥P := by
    refine RingHom.ext fun a => ?_
    apply Subtype.ext
    show ((Φ.symm a : ↥(Algebra.adjoin k ({y} : Set ↥P))) : L) = (a : L)
    exact hΦsymmcoe a
  have h1 : Module.Finite ↥A ↥(integralClosure ↥A ↥P) :=
    module_finite_integralClosure_of_ringEquiv (A := ↥A)
      (A' := ↥(Algebra.adjoin k ({y} : Set ↥P))) (N := ↥P) Φ.symm hcompat hpure
  -- glue
  haveI hNoethA : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial k)
      (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hICA : IsIntegrallyClosed ↥A :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hFrB : IsFractionRing ↥(integralClosure ↥A ↥P) ↥P :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥A ↥K ↥P ↥(integralClosure ↥A ↥P)
  haveI hICB : IsIntegrallyClosed ↥(integralClosure ↥A ↥P) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ↥K
  haveI hNoethB : IsNoetherianRing ↥(integralClosure ↥A ↥P) :=
    IsNoetherianRing.of_finite ↥A _
  exact ordClosure_finite_general_glue (A := ↥A) (B := ↥(integralClosure ↥A ↥P)) (N := ↥P)
    (L := L) h1

/-! ## The general case -/

/-- **`k[x]` is Japanese.**  For `x` transcendental over a field `k` and `L / k(x)` finite, the
integral closure of `k[x]` in `L` is a finite `k[x]`-module.  The general case is reduced to the
normal case by passing to a normal closure (`normalClosure_reduction`). -/
theorem ordClosure_finite_general_adjoin {k : Type*} [Field k] {L : Type*} [Field L]
    [Algebra k L] (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) :=
  normalClosure_reduction
    (fun {k L} _ _ _ x _ _ hx => ordClosure_finite_general_normal_case (k := k) (L := L) x hx)
    x hx

open Work.CurveBasics in
theorem ordClosure_finite_general {k : Type*} [Field k] (C : Curve k) (h : C.functionField)
    (hh : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField] :
    Module.Finite (C.ordBase h) (C.ordClosure h) := by
  exact ordClosure_finite_general_adjoin h hh

end Work.CurveBasics.Order
