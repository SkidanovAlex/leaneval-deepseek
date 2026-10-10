import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The canonical action of a decomposition group, and the model bridge for it

`LTDDefs/Basic.lean` defines the local cohomology `H0loc`, `H1loc`, `H2loc` of a subgroup
`H ≤ G_k` with coefficients in a `Gal(K/k)`-module `M`, and `LTDDefs/H1loc_iso_H1cont.lean`
identifies `H1loc` with the workspace's continuous-cochain model `Work.AbsoluteKummer.H1 ↥H M`
*relative to an action of* `↥H` *on* `M` satisfying a compatibility hypothesis.

For the arithmetic case `H = D_A = decomp k A` there is a canonical such action, namely the
action of `D_A` through the restriction `res k K : G_k →* Gal(K/k)`
(`decompDistribMulAction`, `decompSmulCommClass`).  With it the bridge becomes unconditional:

`H1loc p k Ω K M (decomp k A) ≃+ Work.AbsoluteKummer.H1 ↥(decomp k A) M`

(`H1locEquivH1_decomp`), so that the continuous-cohomology toolkit of the workspace
(inflation, restriction, Shapiro, the class-field-theory lemmas of `Commons`/`NK`, …) is
available for the local `H¹` of a decomposition group in the exact form used by the arithmetic
inputs of `Work.SSGRoute.local_tate_duality`.

The action depends on `K` (through `res k K`), which is not determined by the type
`↥(decomp k A)`; it is therefore a definition and not a type-class instance, and consumers
introduce it with `letI := decompDistribMulAction K M A`.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

section Action

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]

/-- **The canonical action of a decomposition group.**  `D_A = decomp k A` acts on a
`Gal(K/k)`-module `M` through the restriction `res k K : G_k →* Gal(K/k)`. -/
@[instance_reducible] def decompDistribMulAction (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (A : ValuationSubring Ω) : DistribMulAction ↥(SSGRoute.decomp k A) M where
  smul h m := SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
  one_smul m := by
    show SSGRoute.res k K (((1 : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)) • m = m
    rw [show ((1 : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) = 1 from rfl, map_one, one_smul]
  mul_smul h1 h2 m := by
    show SSGRoute.res k K (((h1 * h2 : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)) • m
      = SSGRoute.res k K ((h1 : Ω ≃ₐ[k] Ω)) • (SSGRoute.res k K ((h2 : Ω ≃ₐ[k] Ω)) • m)
    rw [show ((h1 * h2 : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)
        = (h1 : Ω ≃ₐ[k] Ω) * (h2 : Ω ≃ₐ[k] Ω) from rfl, map_mul, mul_smul]
  smul_zero h := smul_zero _
  smul_add h m n := smul_add _ _ _

variable (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]

/-- The compatibility hypothesis of the model bridge holds definitionally for the canonical
action of a decomposition group. -/
theorem decomp_smul_eq_res (A : ValuationSubring Ω) (h : ↥(SSGRoute.decomp k A)) (m : M) :
    @SMul.smul ↥(SSGRoute.decomp k A) M (decompDistribMulAction K M A).toSMul h m
      = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := rfl

end Action

section Bridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **The model bridge at a decomposition group**, with the canonical action: the local `H¹` of
`LTDDefs/Basic` is the workspace's continuous cohomology of `D_A`. -/
def H1locEquivH1_decomp (A : ValuationSubring Ω) :
    letI : SMul ↥(SSGRoute.decomp k A) M := (decompDistribMulAction K M A).toSMul
    letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
    H1loc p k Ω K M (SSGRoute.decomp k A) ≃+
      Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) M :=
  letI : SMul ↥(SSGRoute.decomp k A) M := (decompDistribMulAction K M A).toSMul
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
  H1locEquivH1 p k Ω K M (SSGRoute.decomp k A)
    (fun h m => decomp_smul_eq_res K M A h m)

end Bridge

end

end Work.SSGRoute
