import Mathlib
import Submission.Work.SSGRoute.exists_sha2ToH2
import Submission.Work.SSGRoute.ShaCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Naturality of the cocycle-level bridge `Ш²(k,M) → H²(G_k,M)` in the coefficient module**
(piece 5 of the design of the node `Work.SSGRoute.ext_sha2_bridge`, E1a): for a `Gal(K/k)`-equivariant
`𝔽_p`-linear `f : M → M₂` and any two bridges `φ`, `φ₂` realising the computation rule of
`Work.SSGRoute.exists_sha2ToH2` on representatives, the square

`Ш²(k,M) --Sha2Map f--> Ш²(k,M₂)`
`   | φ                              | φ₂`
`H²(G_k,M) --mapH2 f--> H²(G_k,M₂)`

commutes, where the `G_k = Ω ≃ₐ[k] Ω`-actions on `M`, `M₂` are those pulled back along
`res k K : G_k →* Gal(K/k)` (`DistribMulAction.compHom · (SSGRoute.res k K)`).

Proof route: reduce `b` to a representative `Submodule.Quotient.mk ⟨c, hc⟩` (the quotient being
`↥(Z2loc) ⧸ (B2top).comap (Z2loc).subtype`), rewrite `Sha2Map` on representatives by
`Work.SSGRoute.Sha2Map_mk` (the push-forward is `pushC2`), apply both computation rules `hφ`, `hφ₂`,
and conclude by the cochain-level identity `mapCochain2 G f (fun q => c q.1 q.2) =
(fun q => f (c q.1 q.2))` together with `mapH2_H2π`.  The `f`-equivariance for the pulled-back
`G_k`-action is `fun σ m => hf (SSGRoute.res k K σ) m`.  In the `@mapH2` spelling there are three
`_` for `[Group G]`, `[AddCommGroup M]`, `[AddCommGroup M₂]`, then the two explicit
`DistribMulAction.compHom … (res k K)` instances. -/
theorem sha2ToH2_natural (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (φ : Work.SSGRoute.Sha2 p k Ω K M →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M _ _
          (DistribMulAction.compHom M (SSGRoute.res k K)))
    (hφ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K M),
        φ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M _ _
              (DistribMulAction.compHom M (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩)
    (φ₂ : Work.SSGRoute.Sha2 p k Ω K M₂ →+
        @Work.GroupCohomology.H2 (Ω ≃ₐ[k] Ω) M₂ _ _
          (DistribMulAction.compHom M₂ (SSGRoute.res k K)))
    (hφ₂ : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M₂) (hc : c ∈ Work.SSGRoute.Z2loc p k Ω K M₂),
        φ₂ (Submodule.Quotient.mk ⟨c, hc⟩)
          = @Work.GroupCohomology.H2π (Ω ≃ₐ[k] Ω) M₂ _ _
              (DistribMulAction.compHom M₂ (SSGRoute.res k K))
              ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2,
                (Work.SSGRoute.bridge_isCocycle2_mem_Z2 (SSGRoute.res k K)
                  (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2)).mp hc.1⟩)
    (b : Work.SSGRoute.Sha2 p k Ω K M) :
    φ₂ (Work.SSGRoute.Sha2Map p k Ω K M M₂ f hf b)
      = @Work.GroupCohomology.mapH2 (Ω ≃ₐ[k] Ω) M M₂ _ _ _
          (DistribMulAction.compHom M (SSGRoute.res k K))
          (DistribMulAction.compHom M₂ (SSGRoute.res k K))
          f.toAddMonoidHom (fun σ m => hf (SSGRoute.res k K σ) m) (φ b) := by
  -- The pulled-back action of `G_k` on the coefficients, spelled out because it is not
  -- synthesizable (the subgroup `K` is not inferable from the coefficient type).
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M := DistribMulAction.compHom M (SSGRoute.res k K)
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) M₂ := DistribMulAction.compHom M₂ (SSGRoute.res k K)
  -- Reduce to a representative `x : ↥(Z2loc)` of `b` in `Z²_loc`.
  refine Submodule.Quotient.induction_on
    ((B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype) b fun x => ?_
  -- Compute `Sha2Map` on the representative (`Sha2Map_mk`), then apply the two computation
  -- rules of the bridges `φ`, `φ₂` to the representatives `x.1` and `pushC2 … f x.1`; the two
  -- resulting classes agree because `mapCochain2` on the pushed-forward cocycle is exactly the
  -- push-forward of the cochain: this is `Work.GroupCohomology.mapH2_H2π`, which here holds by
  -- definitional unfolding of `mapH2` (`QuotientAddGroup.lift` on a class).
  rw [Sha2Map_mk p k Ω K M M₂ f hf x,
    hφ₂ (pushC2 p k Ω K M M₂ f x.1) (Z2loc_pushC2_mem p k Ω K M M₂ f hf x.1 x.2),
    hφ x.1 x.2]
  -- What is left is the cochain-level identity: `mapH2 f … (H2π c)` is *definitionally*
  -- `H2π (mapZ2 f … c)`, and `mapZ2` on the class of `x.1` is the class of `pushC2 … f x.1`
  -- (`mapCochain2` and `pushC2` agree on values), so both sides are `H2π` of the same
  -- `2`-cocycle.
  rfl

end Work.SSGRoute
