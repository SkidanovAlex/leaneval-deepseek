/-
# The gluing of `G1` with the *cocycle-hypothesised* naturality clause

`Work.SSGRoute.E7Arch.glue_of_finiteHalf` (`Submission/Work/SSGRoute/E7Arch/g1Assembly.lean`)
assembles input `G1` (`Work.SSGRoute.canonical_localPairing_with_reciprocity`) from a *finite-place
half* `fin` satisfying `hclauses`, `hnat`, `horth`, `hrecJoint` together with the proved archimedean
half.  Its hypothesis `hnat` is

```
∀ M M₂ f hf f' hff' H a b, fin M₂ H (fun σ => f (a σ)) b = fin M H a (fun σ => f' (b σ)),
```

with **no** cocycle/local-constancy hypotheses on `a` and `b`.  That is strictly stronger than clause
(5) of `G1`, which asserts the identity only for locally constant **cocycles**; and the only known
finite-place half — the explicit cup construction `Work.SSGRoute.pairOfInvH` of
`Submission/Work/SSGRoute/cupInvariantPerPlace.lean` — is a *guarded* pairing
(`if IsCocycleOn … then inv (evCupFun …) else 0`), for which the unconditional identity can fail
(if `f ∘ a` and `b` are cocycles but `a` is not, the left side is `inv (evCupFun _ _)` while the
right side is `0`).  So the cup lane's proved clause (5), `Work.SSGRoute.cupH_natural`, cannot be fed
into `glue_of_finiteHalf`: the composition is blocked by the *shape of the hypothesis*, not only by
type-class instances.

This file supplies the corrected gluing: the same `pairGlue` construction, but with `hnat` carrying
the hypotheses that `G1`'s clause (5) carries.  All the other pieces of `g1Assembly.lean`
(`pairGlue`, `pairGlue_arch`, `pairGlue_fin`, `pairGlue_decomp`, `pairClauses_of_pair_eq`,
`pairGlue_pairClauses`, `pairGlue_orth`, `pairGlue_reciprocity`) do not involve `hnat` and are
imported verbatim.

The final theorem `canonical_localPairing_of_cup` then reduces `G1` to exactly the cup datum: an
invariant `inv` per local group with its three properties, the diagonal-tensor rule `hdiag`, the
perfectness input `h4` (local Tate duality in cup form) and the joint reciprocity `hrecJoint`.
-/
import Submission.Work.SSGRoute.cupG1Assembly
import Submission.Work.SSGRoute.E7Arch.exists_level_localDegree_ge_three
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.E7Arch

attribute [local instance] Classical.propDecidable

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (fin : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
    Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p)

/-- **Clause (5) of the glued family at every local group, with the cocycle hypotheses of `G1`.**

This is `Work.SSGRoute.E7Arch.pairGlue_naturality` with the hypothesis `hnat` weakened to the shape
in which the cup construction supplies it (locally constant cocycles only).  The archimedean branch is
`Work.SSGRoute.E7Arch.pairArchFamily_naturality`, which is unconditional. -/
theorem pairGlue_naturality_cocycle
    (hnat : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
        [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
        (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
        (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (H : Subgroup (Ω ≃ₐ[k] Ω))
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        fin M₂ H (fun σ => f (a σ)) b = fin M H a (fun σ => f' (b σ)))
    (hempty : LocalGroupDisjoint k Ω) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
      [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
      (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
      (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] SSGRoute.DualMod p (M ⊗[ZMod p] T))
      (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
        f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
      (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H1Pair.IsLocalGroup k Ω H)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T))
      (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b),
      pairGlue p k Ω K ζ hζ hζK T hT fin M₂ H (fun σ => f (a σ)) b =
        pairGlue p k Ω K ζ hζ hζK T hT fin M H a (fun σ => f' (b σ)) := by
  intro M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' H hH a b ha hb
  rcases hH with ⟨A, hA, rfl⟩ | ⟨c, hc, rfl⟩
  · rw [pairGlue_decomp p k Ω K ζ hζ hζK T hT fin hempty M₂ A hA (fun σ => f (a σ)) b,
      pairGlue_decomp p k Ω K ζ hζ hζK T hT fin hempty M A hA a (fun σ => f' (b σ))]
    exact hnat M M₂ f hf f' hff' (SSGRoute.decomp k A) a b ha hb
  · rw [pairGlue_arch p k Ω K ζ hζ hζK T hT fin M₂ hc rfl (fun σ => f (a σ)) b,
      pairGlue_arch p k Ω K ζ hζ hζK T hT fin M hc rfl a (fun σ => f' (b σ))]
    exact pairArchFamily_naturality p k Ω K ζ hζ hζK T hT M M₂ f hf f' hff' a b c hc

/-- **The assembly of the clause list of the glued family with the corrected naturality
hypothesis.**  This is `Work.SSGRoute.E7Arch.glue_of_finiteHalf` with `hnat` weakened to the shape
in which the cup construction supplies it.  The conclusion has the same four-part shape. -/
theorem glue_of_finiteHalf_cocycle
    (hclauses : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      H1Pair.PairClauses p K T M (fun a b => fin M (SSGRoute.decomp k A) a b)
        (SSGRoute.decomp k A))
    (hnat : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
        [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
        (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
        (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
          SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
          f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (H : Subgroup (Ω ≃ₐ[k] Ω))
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        fin M₂ H (fun σ => f (a σ)) b = fin M H a (fun σ => f' (b σ)))
    (horth : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
        (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0),
        fin M (SSGRoute.decomp k A) a b = 0)
    (hrecJoint : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', fin M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0)
    (hempty : LocalGroupDisjoint k Ω) :
    ∃ pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p,
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (H : Subgroup (Ω ≃ₐ[k] Ω)), H1Pair.IsLocalGroup k Ω H →
          H1Pair.PairClauses p K T M (fun a b => pair M H a b) H) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
          [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
          (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
          (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
            SSGRoute.DualMod p (M ⊗[ZMod p] T))
          (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
            f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
          (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H1Pair.IsLocalGroup k Ω H)
          (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T))
          (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b),
          pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ))) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
          (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
          (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
          (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
          (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0),
          pair M (SSGRoute.decomp k A) a b = 0) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
          H1Pair.PairReciprocity p K T M (fun H a b => pair M H a b)) :=
  ⟨fun M _ _ _ _ _ => pairGlue p k Ω K ζ hζ hζK T hT fin M,
    fun M _ _ _ _ _ H hH =>
      pairGlue_pairClauses p k Ω K ζ hζ hζK T hT fin hclauses hempty M H hH,
    fun M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' H hH a b ha hb =>
      pairGlue_naturality_cocycle p k Ω K ζ hζ hζK T hT fin hnat hempty M M₂ f hf f' hff' H hH
        a b ha hb,
    fun M _ _ _ _ _ A hA hpA hramA a b ha hb hiner =>
      pairGlue_orth p k Ω K ζ hζ hζK T hT fin horth hempty M A hA hpA hramA a b ha hb hiner,
    fun M _ _ _ _ _ => pairGlue_reciprocity p k Ω K ζ hζ hζK T hT fin hrecJoint hempty M⟩

/-- **`G1` from the cup datum.**  The conclusion of
`Work.SSGRoute.canonical_localPairing_with_reciprocity` follows from the cup construction with a
place-dependent invariant `inv` (additive, killing `2`-coboundaries, killing the cochains vanishing
on the inertia at good places), the diagonal-tensor rule `hdiag`, the perfectness input `h4` at the
decomposition groups of the finite places, and the joint reciprocity `hrecJoint`.

The family returned is the glued family `pairGlue` of `fin := pairOfInvH … inv`; the archimedean half
and the disjointness of the two shapes of local group are the proved
`Work.SSGRoute.E7Arch.pairArchFamily_*` and `Work.SSGRoute.E7Arch.localGroupDisjoint`. -/
theorem canonical_localPairing_of_cup
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (hdiag : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
      (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t))
    (h4 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
          (∀ b : (Ω ≃ₐ[k] Ω) →
              SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hrecJoint : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0) :
    ∃ pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p,
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (∀ H : Subgroup (Ω ≃ₐ[k] Ω),
          ((∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) ∨
            (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
          (∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M H (a + a') b = pair M H a b + pair M H a' b) ∧
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
            pair M H a (b + b') = pair M H a b + pair M H a b') ∧
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
              SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
            pair M H a b = 0) ∧
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T),
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
          (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (∀ a : (Ω ≃ₐ[k] Ω) → M,
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) ∧
          (∀ (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
              [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
              (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
              (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
                SSGRoute.DualMod p (M ⊗[ZMod p] T))
              (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
                f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
              (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ))) ∧
          (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
            pair M (SSGRoute.decomp k A) a b = 0))) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', pair M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pair M (Subgroup.zpowers c) a b = 0) := by
  obtain ⟨pair, hcl, hnat, horth, hrec⟩ :=
    glue_of_finiteHalf_cocycle p k Ω K ζ hζ hζK T hT
      (fin := fun M _ _ _ _ _ => Work.SSGRoute.pairOfInvH p k Ω K T inv M)
      (fun M _ _ _ _ _ A hA =>
        Work.SSGRoute.cupH_pairClauses p k Ω K T inv hinv_add hinv_cob hinv_unram
          hdiag h4 M A hA)
      (fun M _ _ _ _ _ M₂ _ _ _ _ _ f hf f' hff' H a b ha hb =>
        Work.SSGRoute.cupH_natural p k Ω K T inv hinv_add hinv_cob hinv_unram
          hdiag M M₂ f hf f' hff' H a b ha hb)
      (fun M _ _ _ _ _ A hA hpA hramA a b ha hb hiner =>
        Work.SSGRoute.cupH_unramified p k Ω K T inv hinv_add hinv_cob hinv_unram
          hdiag h4 M A hA hpA hramA a b ha hb hiner)
      hrecJoint
      (Work.SSGRoute.E7Arch.localGroupDisjoint k Ω)
  refine ⟨pair, fun M _ _ _ _ _ => ?_, fun M _ _ _ _ _ => ?_⟩
  · intro H hH
    obtain ⟨h1, h2, h3, h4', h5⟩ := hcl M H hH
    exact ⟨h1, h2, h3, h4', h5,
      fun M₂ _ _ _ _ _ f hf f' hff' a b ha hb => hnat M M₂ f hf f' hff' H hH a b ha hb,
      fun A a b hA hpA hramA ha hb hiner => horth M A hA hpA hramA a b ha hb hiner⟩
  · intro a b ha1 ha2 hb1 hb2
    exact hrec M a b ha1 ha2 hb1 hb2


/-- **The diagonal-tensor rule is provable at the global diagonal action on `M ⊗ T`.**  This
discharges the hypothesis `hdiag` of `canonical_localPairing_of_cup` once and for all: the instance
used by `pairOfInvH` in the conclusion of that theorem is the global
`Work.Shrinking.instDistribMulActionTensorProduct` (this is exactly the content of
`Work.SSGRoute.tensorAction_eq_of_diag`'s bridge), and the rule holds for it. -/
theorem hdiag_cup :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
      (g : K ≃ₐ[k] K) (x : M) (t : T),
      g • (TensorProduct.tmul (ZMod p) x t) =
        TensorProduct.tmul (ZMod p) (g • x) (g • t) :=
  fun M _ _ _ _ g x t =>
    Work.Shrinking.diagTensor_smul_tmul (p := p) (G := K ≃ₐ[k] K) g x t

/-- **`G1` from the cup datum, with the diagonal-tensor rule discharged.**  Same statement as
`canonical_localPairing_of_cup`, but `hdiag` is replaced by the proved `hdiag_cup`: the remaining
inputs are exactly the invariant functional `inv` with its three properties, the perfectness input
`h4` and the joint reciprocity `hrecJoint`. -/
theorem canonical_localPairing_of_cup' 
    (inv : Subgroup (Ω ≃ₐ[k] Ω) →
      ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T) → ZMod p)
    (hinv_add : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c c' : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T),
      inv H (c + c') = inv H c + inv H c')
    (hinv_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T),
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c → inv H c = 0)
    (hinv_unram : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p T,
      (∀ g h : Ω ≃ₐ[k] Ω, (SSGRoute.IsInertia k A g ∨ SSGRoute.IsInertia k A h) → c g h = 0) →
      inv (SSGRoute.decomp k A) c = 0)
    (h4 : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
          (∀ b : (Ω ≃ₐ[k] Ω) →
              SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b = 0) →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hrecJoint : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
        (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', Work.SSGRoute.pairOfInvH p k Ω K T inv M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0) :
    ∃ pair : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
          ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p,
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (∀ H : Subgroup (Ω ≃ₐ[k] Ω),
          ((∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) ∨
            (∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c)) →
          (∀ (a a' : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M H (a + a') b = pair M H a b + pair M H a' b) ∧
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
            pair M H a (b + b') = pair M H a b + pair M H a b') ∧
          (∀ (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
              SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
            pair M H a b = 0) ∧
          (∀ a : (Ω ≃ₐ[k] Ω) → M,
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T),
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a) ∧
          (∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            (∀ a : (Ω ≃ₐ[k] Ω) → M,
              (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
              pair M H a b = 0) →
            SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) ∧
          (∀ (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂]
              [DistribMulAction (K ≃ₐ[k] K) M₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
              (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
              (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p]
                SSGRoute.DualMod p (M ⊗[ZMod p] T))
              (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
                f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
              (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)),
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
            pair M₂ H (fun σ => f (a σ)) b = pair M H a (fun σ => f' (b σ))) ∧
          (∀ (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → M)
              (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
            SSGRoute.IsFinPlace k A → ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) →
            (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
              SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
            (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → a σ = 0 ∧ b σ = 0) →
            pair M (SSGRoute.decomp k A) a b = 0))) ∧
      (∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
          [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
          (a : (Ω ≃ₐ[k] Ω) → M)
          (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
          ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
            ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∀ (C' : Finset (Ω ≃ₐ[k] Ω)), (∀ c ∈ C', c ^ 2 = 1) →
        (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) →
        (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') →
        ∑ A ∈ S', pair M (SSGRoute.decomp k A) a b +
          ∑ c ∈ C', pair M (Subgroup.zpowers c) a b = 0) :=
  canonical_localPairing_of_cup p k Ω K ζ hζ hζK T hT inv hinv_add hinv_cob hinv_unram
    (fun M => hdiag_cup p k Ω K T M) h4 hrecJoint

end Work.SSGRoute.E7Arch
