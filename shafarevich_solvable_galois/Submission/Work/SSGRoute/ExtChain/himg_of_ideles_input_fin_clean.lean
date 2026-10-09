import Submission.Work.SSGRoute.ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial
import Submission.Work.SSGRoute.ExtChain.himgIdelesInput_fin
import Submission.Work.SSGRoute.hasseExt1_C2_lattice_leaf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `himg` leaf, modulo the finite-place clause *alone*, above the import cycle

The target file `ExtChain/extToIdeles_eq_zero_imp_chainC_locallyTrivial.lean` carries the `himg`
half of the node `ext_sha2_bridge` and cannot import its own children:
`ExtChain.himgIdelesInput_inf` (and hence `ExtChain.himgFromIdelesInput`) has the node
`Submission.Work.SSGRoute.ext_sha2_bridge` in its import cone (via
`ExtChain.freeCoverSES_lattice`), while the node imports the leaf file — a cycle.

This module sits *above* the cycle and below the node.  Its cone contains neither the node nor
`himgFromIdelesInput`: it imports the leaf file (for the assembly `himg_of_ideles_input`), the
finite-place clause `ExtChain.himgIdelesInput_fin`, and the *clean, axiom-clean* involution clause
`Work.SSGRoute.ExtChain.himgIdelesInput_inf_clean`
(`Submission/Work/SSGRoute/hasseExt1_C2_lattice_leaf.lean`, whose `#print axioms` is
`[propext, Classical.choice, Quot.sound]`).

Therefore the node can cite the theorem below instead of the leaf's own `sorry`, and its entire
frontier becomes the single finite-place clause `ExtChain.himgIdelesInput_fin`.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

-- The `Module.Finite ℤ (ker (freeCover N)).V` instance of the canonical syzygy, needed by
-- `himg_of_ideles_input`, `himgIdelesInput_fin` and `himgIdelesInput_inf_clean`.
attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-- **The `himg` leaf's conclusion, from the finite-place clause alone.**  Statement identical to
`Work.SSGRoute.ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial` (the `sorry` of
`ExtChain/extToIdeles_eq_zero_imp_chainC_locallyTrivial.lean`); the finite-place authority is
`ExtChain.himgIdelesInput_fin`, the involution authority is the clean, axiom-clean
`ExtChain.himgIdelesInput_inf_clean`. -/
theorem extToIdeles_eq_zero_imp_chainC_locallyTrivial_of_fin (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      SSGRoute.PTExt.extToIdeles (k := k) y = 0 →
        ∃ c : ↥(SSGRoute.Z2loc p k Ω K E),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            (Work.SSGRoute.PT.Z2ofZ2loc p k Ω K E c) =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact himg_of_ideles_input (k := k) (Ω := Ω) (K := K) p ζ hζ hζK T hT E
    (fun z hz A hA hns =>
      Work.SSGRoute.ExtChain.himgIdelesInput_fin p k Ω K ζ hζ hζK T hT E z hz A hA hns)
    (fun z hz σ hσ hnt =>
      Work.SSGRoute.ExtChain.himgIdelesInput_inf_clean p k Ω K ζ hζ hζK T hT E z hz σ hσ hnt)

end

end Work.SSGRoute.ExtChain
