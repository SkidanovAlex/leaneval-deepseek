import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.RingTheory.RootsOfUnity.Basic
import Submission.Work.SSGRoute.PTembedding.KummerMuDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ω`-free instances for the `ZMod p`-module structure on the `p`-th roots of unity

The interface `Work.SSGRoute.H2loc` (and `Work.AbsoluteKummer.H2`) asks a coefficient module for
`[Module (ZMod p) M]`, `[DistribMulAction G M]` and `[SMulCommClass G (ZMod p) M]`.  For the
coefficient module `μ_p = Additive (rootsOfUnity p E)` the workspace provides these in
`Submission.Work.SSGRoute.PTembedding.KummerMuDefs` (`instModuleMuAdd`,
`instSMulCommClassMuAdd`) and in `Submission.Work.SSGRoute.PTembedding.mup_kummer_defs`
(`instDistribMulActionAddRootsOfUnityOfField`) — but the first two take `K : IntermediateField k Ω`
as an argument, which a goal of the form
`SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Additive (rootsOfUnity p K))`
(no `Ω` in sight) does not mention, so typeclass search cannot instantiate them; that is why
`Submission.Work.SSGRoute.PTembedding.h1loc_mup_kummer_card` passes
`MupCard.instSMulCommClassMuAdd` explicitly.

The two instances below are the `Ω`-free (and, for the module structure, `F`-free) versions, in the
shape in which typeclass search finds them from such goals.  They are stated for prime `n` so that
no `ZMod 0`-instance is created.
-/

namespace Work.SSGRoute.PTCore

/-- **The `ZMod n`-module structure on the `n`-th roots of unity of a field.**

`Additive (rootsOfUnity n E)` has exponent `n`, so it is a `ZMod n`-module by
`AddCommGroup.zmodModule`.  This is the `Ω`-free, `F`-free version of
`Work.SSGRoute.PTembedding.MupCard.instModuleMuAdd`. -/
noncomputable instance instModuleAddRootsOfUnityOfField (n : ℕ) [Fact n.Prime] {E : Type*}
    [Field E] : Module (ZMod n) (Additive (rootsOfUnity n E)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    rw [Work.SSGRoute.PTembedding.MupCard.toMul_nsmul]
    show (Additive.toMul x : rootsOfUnity n E) ^ n = 1
    apply Subtype.ext
    show ((Additive.toMul x : rootsOfUnity n E) : Eˣ) ^ n = 1
    exact (mem_rootsOfUnity n ((Additive.toMul x : rootsOfUnity n E) : Eˣ)).mp
      (Additive.toMul x).2)

/-- **The Galois action on the `n`-th roots of unity commutes with the `ZMod n`-scalar action.**

Together with `Work.SSGRoute.PTembedding.MupKummer.instDistribMulActionAddRootsOfUnityOfField`
(the action itself) and `instModuleAddRootsOfUnityOfField` (the scalars) this is the instance that
`Work.SSGRoute.H2loc` asks for at `μ_p = Additive (rootsOfUnity n E)`; it is the `Ω`-free version of
`Work.SSGRoute.PTembedding.MupCard.instSMulCommClassMuAdd`. -/
noncomputable instance instSMulCommClassAddRootsOfUnityOfField (n : ℕ) [Fact n.Prime]
    {F E : Type*} [Field F] [Field E] [Algebra F E] :
    SMulCommClass (E ≃ₐ[F] E) (ZMod n) (Additive (rootsOfUnity n E)) where
  smul_comm g c x := by
    rw [Work.SSGRoute.PTembedding.MupCard.zmod_smul_eq_nsmul_val (p := n) c x,
      Work.SSGRoute.PTembedding.MupCard.zmod_smul_eq_nsmul_val (p := n) c (g • x),
      Work.SSGRoute.PTembedding.MupCard.smul_nsmul_comm]

end Work.SSGRoute.PTCore
