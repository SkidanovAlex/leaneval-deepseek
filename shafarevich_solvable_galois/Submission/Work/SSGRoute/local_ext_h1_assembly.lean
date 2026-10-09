import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E7a: the assembly step — a group isomorphism gives the map `β`

`local_ext_h1_bridge` asks for a map `β` from all functions `G_k → E` to `Ext¹_{D_w}(E', K_wˣ)`,
additive on locally constant `1`-cocycles on the decomposition group `D_A`, with kernel the
coboundaries and surjective onto the `Ext¹` group.  These three conditions say exactly that `β`
induces an isomorphism `H1loc(D_A, E) ≅ Ext¹`; conversely, this file shows that any additive
isomorphism `φ : H1loc(D_A, E) ≃+ Y` produces such a `β` for `Y` the target group: send a locally
constant cocycle `b` to `φ (toClass b)` and everything else to `0`.

* additivity comes from `toClass_add`;
* the kernel description from `toClass_eq_zero_iff` plus injectivity of `φ`;
* surjectivity from `toClass_surjective` plus surjectivity of `φ`.

So the whole content of E7a is the existence of the additive isomorphism
`H1loc(D_A, E) ≃+ Ext¹_{D_w}(E', K_wˣ)` (i.e. lane (a) plus local Tate duality in degree one,
`H1loc(D_A, E) ≅ H1loc(D_A, E^∨(1))` and `H1loc(D_A, E^∨(1)) ≅ Ext¹`).
-/

namespace Work.SSGRoute

/-- **E7a, assembly.**  An additive isomorphism between the locally constant `H¹` of the
decomposition group `D_A` and any target group `Y` yields a map `β` on all functions `G_k → E`
which is additive on locally constant cocycles, whose kernel on those is exactly the coboundaries,
and which is onto `Y`. -/
theorem exists_beta_of_addEquiv (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (A : ValuationSubring Ω) (Y : Type) [AddCommGroup Y]
    (φ : Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+ Y) :
    ∃ β : ((Ω ≃ₐ[k] Ω) → E) → Y,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
          β (b + b') = β b + β b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
      ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ β b = y := by
  refine ⟨fun b => φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b), ?_, ?_, ?_⟩
  · intro b b' hb1 hb2 hb1' hb2'
    change φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) (b + b')) =
      φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) +
        φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b')
    rw [Work.SSGRoute.toClass_add p k Ω K E (SSGRoute.decomp k A) (f := b) (f' := b')
      ⟨hb1, hb2⟩ ⟨hb1', hb2'⟩]
    exact map_add φ _ _
  · intro b hb1 hb2
    change φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b) = 0 ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
    rw [map_eq_zero_iff φ φ.injective]
    exact Work.SSGRoute.toClass_eq_zero_iff p k Ω K E (SSGRoute.decomp k A) (f := b)
      ⟨hb1, hb2⟩
  · intro y
    obtain ⟨g, hg, hgy⟩ := Work.SSGRoute.toClass_surjective p k Ω K E
      (SSGRoute.decomp k A) (φ.symm y)
    refine ⟨g, hg.1, hg.2, ?_⟩
    change φ (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) g) = y
    rw [hgy, AddEquiv.apply_symm_apply]

end Work.SSGRoute
