import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.CohomologicalShrinking.All
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.sha2_dual_control
import Submission.Work.SSGRoute.tatePoitouEmbedding
import Submission.Work.SSGRoute.sha2_image_of_Hm2_of_dualControl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# sha2_image_of_Hm2_fin  (node H7, replaces the target shape of `sha2_image_of_Hm2`)

**What changed.** Identical to `Work.SSGRoute.sha2_image_of_Hm2` except `[Finite E₂]` on the test module.
The only consumer (`stage_global_lifting`, Step 2) instantiates `E₂ = E p G n i j`, which is finite.
Arbitrary `E₂` forced the old intermediate `tatePoitou_sha2_image` to define `Ψ E` on *infinite* modules.
That is true but pointless work.

**Proof.** `sha2_image_of_Hm2_of_dualControl` applied to the dual control produced by
`sha2_dual_control_of_tatePoitouEmbedding` from the Tate--Poitou embedding
(`tatePoitouEmbedding`).  `hc` is `⟨hc, hcc, hloc, hinf⟩ : c ∈ Z2loc …`; `T` is finite because
`hT.1` gives `finrank = 1`.
-/

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct

theorem sha2_image_of_Hm2_fin (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    ∃ x : Work.Tate.Hm2 (K ≃ₐ[k] K) (E ⊗[ZMod p] T),
      ∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e),
        Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
            (fun g z => Work.CohomologicalShrinking.rTensor_equiv p f hf g z) x = 0 →
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (c σ τ)) := by
  -- `T` is a line, hence finite: this is the only extra instance the assembly asks for.
  haveI : Finite T := finite_of_finrank_eq_one (p := p) T hT.1
  -- the Tate--Poitou embedding (the injectivity half of Poitou--Tate duality), as Φ
  obtain ⟨Φ, hΦinj, hΦnat⟩ := tatePoitouEmbedding p k Ω K ζ hζ hζK T hT
  -- `Φ_E([c])` is the dual-control functional on `Ш¹(k, E^∨(1))`
  exact sha2_image_of_Hm2_of_dualControl p k Ω K E T c
    (sha2_dual_control_of_tatePoitouEmbedding p k Ω K ζ hζ hζK E T hT c
      ⟨hc, hcc, hloc, hinf⟩ Φ hΦinj hΦnat)

end Work.SSGRoute
