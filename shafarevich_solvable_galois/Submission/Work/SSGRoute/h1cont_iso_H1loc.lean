import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7a, §15 option (b): the last transport of the continuous chain

`H1_cont(Gal(κ̄/k_v), E) ≃+ H1loc p k Ω K E (decomp k A)`, stated in `PT.h1Transfer`'s pattern with
`IsHomeomorph Φ` and the coefficient compatibility `hact` as hypotheses — i.e. never asking the
opaque `localGaloisEquivAt` for continuity (see `E7a_HANDOFF.md` §15).  The proof is the two-step
assembly: `AddEquiv.refl E` is `Φ`-equivariant by `hact`, so `h1Transfer` applies; compose its
inverse with `(H1locEquivH1_decomp …).symm`.
-/

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

theorem h1cont_iso_H1loc (p : ℕ) [Fact p.Prime] (k : Type) (Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [inst : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E]
    (Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA))
    (hΦ : IsHomeomorph Φ)
    (hact : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E),
      @SMul.smul _ _ inst.toSMul (Φ σ) e = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) :
    Nonempty (Work.AbsoluteKummer.H1
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA) E ≃+
      Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A)) := by
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E := decompDistribMulAction K E A
  have hΨ : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E),
      (AddEquiv.refl E) (σ • e) = Φ σ • ((AddEquiv.refl E) e) := by
    intro σ e
    show @SMul.smul _ _ (decompDistribMulAction K E A).toSMul σ e = Φ σ • e
    rw [decomp_smul_eq_res K E A σ e]
    exact (hact σ e).symm
  exact ⟨(Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl E) hΨ).symm.trans
    (H1locEquivH1_decomp p k Ω K E A).symm⟩

end

end Work.SSGRoute
