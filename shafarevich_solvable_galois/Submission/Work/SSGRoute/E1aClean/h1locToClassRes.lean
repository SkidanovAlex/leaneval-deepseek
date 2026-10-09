import Mathlib
import Submission.Work.SSGRoute.E1aClean.h1locCoeffNatural
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The left end of the finite-place comparison square: `toClass`, `bridgeFwd`, `resH1`, `H1π`

The finite-place **square** clause of `LeadNatWit.FinPlaceDict` (the obligation filed at
`E1aClean/LeadPhiUnr/phiCan_square.lean`) compares

  `extLoc_q (extToIdeles (globalDictionaryCanon E b))`   and   `phiCan E (toClass b)`

for a *global* locally constant cocycle `b`.  The first factor of `phiCan`'s chain is

  `h1locSubgroupEqEquiv` (a cast between the equal subgroups `decomp k A` and `(decompField k Ω A).fixingSubgroup`)

followed by the model bridge `H1locEquivH1 … ↥H'`, which lands in `H¹(↥H', E)`.  The left side,
after `globalDictionaryCanon`'s construction `(h1AddEquiv Φd) ≫ (e1cEquiv₁)⁻¹` and the brick
`E1aClean.resH1_h1AddEquiv`, needs the *same* element, namely `resH1 H' (h1AddEquiv Φd (H1π b))`.
So the two identifications below are exactly what makes the left end of the square close:

* `h1locSubgroupEqEquiv_toClass` — the cast on `H1loc` does nothing to a `toClass`;
* `h1locEquivH1_toClass_eq_resH1` — for a **global** cocycle `b`, the model bridge of its `H1loc`
  class is the restriction to `↥H` of its class in `H¹(G_k, M)`:
  `H1locEquivH1 … H (toClass … b) = resH1 H M (H1π Γ M b)`.

Both are stated *generically* (any subgroup `H` of `Ω ≃ₐ[k] Ω`, any coefficient module `M`), and
both are proof-independent of the number-field hypotheses that do not occur in their statements.
They are `sorry`-free and axiom-clean; the callers supply the `lcCocycles`/`Z1` memberships, so no
`DistribMulAction.compHom` instance has to be forced definitionally in the statement.

Nothing else in the square is touched here.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-- **The subgroup-equality cast of `H1loc` does nothing to a `toClass`.**  `h1locSubgroupEqEquiv`
is `rw [h]`, i.e. the identity transported along the equality of the two `H1loc`-groups; on the
class of a function it is the class of the same function. -/
theorem h1locSubgroupEqEquiv_toClass
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') (b : (Ω ≃ₐ[k] Ω) → M) :
    h1locSubgroupEqEquiv p M h (SSGRoute.toClass p k Ω K M H b)
      = SSGRoute.toClass p k Ω K M H' b := by
  cases h
  rfl

/-- **The model bridge of a global cocycle's class is the restriction of its class.**  For a
function `b` which is a locally constant cocycle on `H` and a continuous global cocycle, the
`H1loc`-class of `b` maps under `H1locEquivH1` to `resH1 H M` of the class of `b` in
`H¹(G_k, M)`.  Both sides are `H1π` of "restrict `b` to `↥H`"; the two memberships differ only by
proofs. -/
theorem h1locEquivH1_toClass_eq_resH1
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction (Ω ≃ₐ[k] Ω) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hbH : b ∈ SSGRoute.lcCocycles p k Ω K M H)
    (hbZ : b ∈ Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) M) :
    SSGRoute.H1locEquivH1 p k Ω K M H hcompat
        (SSGRoute.toClass p k Ω K M H b)
      = Work.SSGRoute.PT.H2Fin.resH1 H M
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) M ⟨b, hbZ⟩) := by
  dsimp only [SSGRoute.toClass]
  rw [dif_pos hbH]
  show SSGRoute.bridgeFwd p k Ω K M H hcompat
      (Submodule.Quotient.mk ⟨b, hbH⟩)
      = Work.SSGRoute.PT.H2Fin.resH1 H M
          (Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) M ⟨b, hbZ⟩)
  rw [bridgeFwd_mk]
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π]
  exact congrArg (Work.AbsoluteKummer.H1π ↥H M)
    (Subtype.ext (funext fun n => rfl))

end

end Work.SSGRoute.E1aClean
