import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.cohomology_bridge
import Submission.Work.SSGRoute.hassePrinciple_h1_cocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]

/-- The restriction map `G_k → Gal(K/k)` is surjective (every `k`-embedding of the normal
extension `K` extends to the algebraic closure `Ω`). -/
theorem res_surjective (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [Normal k K] :
    Function.Surjective (SSGRoute.res k K) :=
  AlgEquiv.restrictNormalHom_surjective Ω

/-- **Descent of a locally trivial cocycle** (the Hasse principle, `hassePrinciple_h1_cocycles`):
a locally constant `1`-cocycle which is a coboundary at every finite place and at every involution
descends to a `1`-cocycle on `Gal(K/k)`. -/
theorem exists_descent (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) :
    ∃ ψ : (K ≃ₐ[k] K) → M,
      SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ ∧
        z.1 = ψ ∘ SSGRoute.res k K :=
  hassePrinciple_h1_cocycles k Ω K p M z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2

/-- The descended cocycle `Gal(K/k) → M` of an element of `Z¹_loc`, chosen once and for all. -/
noncomputable def descentZ1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) : Work.GroupCohomology.Z1 (K ≃ₐ[k] K) M :=
  ⟨Classical.choose (exists_descent p k Ω K M z),
    (isCocycleOn_iff_mem_Z1 (MonoidHom.id (K ≃ₐ[k] K)) _).mp
      (Classical.choose_spec (exists_descent p k Ω K M z)).1⟩

/-- The defining property of `descentZ1`: it is a genuine descent of the cocycle. -/
theorem descentZ1_comp_res (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) :
    z.1 = (descentZ1 p k Ω K M z).1 ∘ SSGRoute.res k K :=
  (Classical.choose_spec (exists_descent p k Ω K M z)).2

/-- **Uniqueness of the descent** (on the level of functions): `res` is surjective, so a descent of
`z` is unique. -/
theorem descentZ1_val_eq_of (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) {ψ : (K ≃ₐ[k] K) → M}
    (h : z.1 = ψ ∘ SSGRoute.res k K) :
    (descentZ1 p k Ω K M z).1 = ψ := by
  refine funext fun τ => ?_
  obtain ⟨σ, rfl⟩ := res_surjective k Ω K τ
  have h1 : ((descentZ1 p k Ω K M z).1 ∘ SSGRoute.res k K) σ
      = (ψ ∘ SSGRoute.res k K) σ :=
    congrFun ((descentZ1_comp_res p k Ω K M z).symm.trans h) σ
  simpa only [Function.comp_apply] using h1

/-- **Uniqueness of the descent**, in `Z¹`. -/
theorem descentZ1_eq_of (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) (ψ : Work.GroupCohomology.Z1 (K ≃ₐ[k] K) M)
    (h : z.1 = ψ.1 ∘ SSGRoute.res k K) :
    descentZ1 p k Ω K M z = ψ :=
  Subtype.ext (descentZ1_val_eq_of p k Ω K M z h)

/-- **The descent map** on the group of locally trivial cocycles, with values in `H¹(Gal(K/k),M)`.
It is additive because a descent is unique. -/
noncomputable def descentHom (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ↥(Z1loc p k Ω K M) →+ Work.GroupCohomology.H1 (K ≃ₐ[k] K) M where
  toFun z := Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M z)
  map_zero' := by
    show Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M 0) = 0
    have hz : descentZ1 p k Ω K M 0 = 0 := by
      refine descentZ1_eq_of p k Ω K M 0 0 ?_
      funext σ
      simp
    rw [hz, map_zero]
  map_add' z z' := by
    show Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M (z + z'))
      = Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M z)
        + Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M z')
    have hz : descentZ1 p k Ω K M (z + z')
        = descentZ1 p k Ω K M z + descentZ1 p k Ω K M z' := by
      refine descentZ1_eq_of p k Ω K M (z + z') _ ?_
      funext σ
      change z.1 σ + z'.1 σ
        = (descentZ1 p k Ω K M z).1 (SSGRoute.res k K σ)
          + (descentZ1 p k Ω K M z').1 (SSGRoute.res k K σ)
      have h1 : z.1 σ = (descentZ1 p k Ω K M z).1 (SSGRoute.res k K σ) :=
        congrFun (descentZ1_comp_res p k Ω K M z) σ
      have h2 : z'.1 σ = (descentZ1 p k Ω K M z').1 (SSGRoute.res k K σ) :=
        congrFun (descentZ1_comp_res p k Ω K M z') σ
      rw [h1, h2]
    rw [hz, map_add]

/-- The computation of `descentHom` on a cocycle. -/
theorem descentHom_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) :
    descentHom p k Ω K M z
      = Work.GroupCohomology.H1π (K ≃ₐ[k] K) M (descentZ1 p k Ω K M z) := rfl

/-- The computation of `descentHom` on a cocycle with a known descent `ψ`. -/
theorem descentHom_eq_H1π (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (z : ↥(Z1loc p k Ω K M)) {ψ : (K ≃ₐ[k] K) → M}
    (hψ : SSGRoute.IsCocycleOn (MonoidHom.id (K ≃ₐ[k] K)) ⊤ ψ)
    (h : z.1 = ψ ∘ SSGRoute.res k K) :
    descentHom p k Ω K M z
      = Work.GroupCohomology.H1π (K ≃ₐ[k] K) M
          ⟨ψ, (isCocycleOn_iff_mem_Z1 (MonoidHom.id (K ≃ₐ[k] K)) ψ).mp hψ⟩ := by
  rw [descentHom_apply]
  exact congrArg (Work.GroupCohomology.H1π (K ≃ₐ[k] K) M)
    (Subtype.ext (descentZ1_val_eq_of p k Ω K M z h))

end Work.SSGRoute
