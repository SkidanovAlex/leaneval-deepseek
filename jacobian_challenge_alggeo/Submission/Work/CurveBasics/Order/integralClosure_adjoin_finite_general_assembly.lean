import Mathlib
import Submission.Work.CurveBasics.Order.kx_pure_insep
import Submission.Work.CurveBasics.Order.perfectClosure_separable_of_normal
import Submission.Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv
import Submission.Work.CurveBasics.Order.isPurelyInseparable_of_ringEquiv_smul
import Submission.Work.CurveBasics.Order.finite_integralClosure_of_ringHom
import Submission.Work.CurveBasics.Order.kx_finite_of_embedding
import Submission.Work.CurveBasics.Order.ringEquivTransportAssembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

namespace Work.CurveBasics.Order

/-- **Reduction of the finiteness of the integral closure of `k[x]` to the normal case.**

If the statement of the theorem holds for every finite *normal* extension of `k(x)`, then it holds
for an arbitrary finite extension, by passing to the normal closure. -/
theorem normalClosure_reduction.{u, v}
    (hnorm : ∀ {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] (x : L)
      [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L]
      [Normal ↥(IntermediateField.adjoin k ({x} : Set L)) L],
      Transcendental k x →
      Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
        ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L))
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L] (x : L) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  let K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  haveI hfdK : FiniteDimensional ↥K L := by
    show FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L
    infer_instance
  let Ω := AlgebraicClosure L
  let M : IntermediateField ↥K Ω := IntermediateField.normalClosure ↥K L Ω
  haveI hfdM : FiniteDimensional ↥K ↥M := normalClosure.is_finiteDimensional ↥K L Ω
  haveI hNrmM : Normal ↥K ↥M := by
    have hsp : ∀ y : L, ((minpoly ↥K y).map (algebraMap ↥K Ω)).Splits :=
      fun y => IsAlgClosed.splits _
    exact (Algebra.IsAlgebraic.isNormalClosure_normalClosure (splits := hsp)).normal
  letI : Algebra k ↥M := ((algebraMap ↥K ↥M).comp (algebraMap k ↥K)).toAlgebra
  haveI hSTkKM : IsScalarTower k ↥K ↥M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : L →ₐ[k] ↥M := ((IsScalarTower.toAlgHom ↥K L Ω).codRestrict M.toSubalgebra
    (fun z => AlgHom.fieldRange_le_normalClosure _ ⟨z, rfl⟩)).restrictScalars k
  have hcoe : ∀ a : L, ((ψ a : ↥M) : Ω) = (algebraMap L Ω) a := fun a => rfl
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h1 : (algebraMap L Ω) a = (algebraMap L Ω) b := by
      rw [← hcoe a, ← hcoe b, hab]
    exact (algebraMap L Ω).injective h1
  have hadj : K.map ψ = IntermediateField.adjoin k ({ψ x} : Set ↥M) := by
    rw [IntermediateField.adjoin_map k ({x} : Set L) ψ, Set.image_singleton]
  let e : ↥K ≃+* ↥(K.map ψ) := (Subalgebra.equivMapOfInjective K.toSubalgebra ψ hψ).toRingEquiv
  have hcoe_e : ∀ a : ↥K, ((e a : ↥(K.map ψ)) : ↥M) = ψ (a : L) := fun a =>
    Subalgebra.coe_equivMapOfInjective_apply K.toSubalgebra ψ hψ a
  have ecomp : (algebraMap ↥(K.map ψ) ↥M).comp e.toRingHom = algebraMap ↥K ↥M := by
    refine RingHom.ext fun a => Subtype.ext ?_
    show ((algebraMap ↥(K.map ψ) ↥M) (e a) : Ω) = ((algebraMap ↥K ↥M) a : Ω)
    rw [show ((algebraMap ↥(K.map ψ) ↥M) (e a) : ↥M) = ψ (a : L) from hcoe_e a]
    exact hcoe (a : L)
  haveI hfdi : FiniteDimensional ↥(IntermediateField.adjoin k ({ψ x} : Set ↥M)) ↥M := by
    rw [← hadj]
    refine module_finite_of_ringEquiv_smul e.symm (fun r m => ?_) hfdM
    have h2 : algebraMap ↥K ↥M (e.symm r) = algebraMap ↥(K.map ψ) ↥M r := by
      have h3 := congrArg (fun f : ↥K →+* ↥M => f (e.symm r)) ecomp
      rw [RingHom.comp_apply] at h3
      rw [show e.toRingHom (e.symm r) = r from RingEquiv.apply_symm_apply e r] at h3
      exact h3.symm
    show (e.symm r) • m = r • m
    rw [Algebra.smul_def, Algebra.smul_def, h2]
  haveI hnrmi : Normal ↥(IntermediateField.adjoin k ({ψ x} : Set ↥M)) ↥M := by
    rw [← hadj]
    exact normal_of_ringEquiv_smul e ecomp hNrmM
  have htr : Transcendental k (ψ x) := by
    change ¬ IsAlgebraic k (ψ x)
    intro halg
    exact hx ((isAlgebraic_algHom_iff ψ hψ).mp halg)
  exact kx_finite_of_embedding x hx ψ hψ (hnorm (x := ψ x) htr)

end Work.CurveBasics.Order
