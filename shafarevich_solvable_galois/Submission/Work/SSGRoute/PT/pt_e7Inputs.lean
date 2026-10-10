import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.pt_canonicalFin_clauses_of_euler02
import Submission.Work.SSGRoute.local_tate_duality_02
import Submission.Work.SSGRoute.local_tate_duality_euler
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two arithmetic inputs of `E7`, named

Input (1) of `pt_canonical_relaxed` (`hpair`) is, after the reductions proved in
`pt_finiteHalf_glue.lean` and `pt_canonicalFin_clauses_of_euler02.lean`, exactly:

* the **local Euler characteristic** — the axiom node `Work.SSGRoute.local_tate_duality_euler`
  (Milne, *ADT*, I.2.8; NSW 7.3.1), and
* **Tate duality in degrees 0 and 2** — the axiom node `Work.SSGRoute.local_tate_duality_02`
  (Milne, *ADT*, I.2.3 at `r = 0`),

together with the *mixed* reciprocity law (`E8`, Hasse reciprocity in the form
`∑_{finite} + ∑_{archimedean} = 0`) for the family glued from them.

This file gives those two inputs **names**, so that they can be cited as single propositions (their
bodies are elaborated here, in the context of the node files, where the instance search for
`H1loc … (DualMod p (M ⊗ T))` resolves), and derives each name from its node.  The names are the
ones consumed by `Work.SSGRoute.PT.pt_canonical_relaxed` (gap (1) in its reduced form).
**WARNING (added after the two-reviewer check of `pt_nodeMixedReciprocity`).**  `canonicalFin` and
`MixedReciprocity`/`NodeMixedReciprocity` below must **not** be used as a *reduced form* of the
target's gap (1).  The reason, recorded by the reviewers: `canonicalFin` is a `Classical.choose` of
the *existential* of `pt_canonicalFin_clauses_of_euler02`, whose specification (the clause bundle
`H1Pair.PairClauses` plus agreement with the archimedean family) does **not** determine the local
pairings — a place-dependent rescaling in `𝔽_p^×` preserves every clause and destroys the
reciprocity sum.  Hence the mixed reciprocity law is *not* a consequence of that specification and
cannot be asserted of the chosen family.  The sound formulation of gap (1) is the whole existential
`FiniteHalfExistsMixed` (clauses **and** mixed reciprocity, as in `pt_finiteHalf_glue.lean`); the
sound route to it needs the *explicitly constructed* canonical pairing (cup product with the local
invariant), which is node `E8`'s content.  The objects below remain useful as *names* for the
intended statements, not as a decomposition.
-/

open scoped TensorProduct

namespace Work.SSGRoute.PT

noncomputable section

/-- **The local Euler characteristic** (`E7a`), named: for every finite place `A` of `Ω` over `k`
there is a uniform `ε` such that every finite `𝔽_p[Gal(K/k)]`-module `M` has
`h¹(M) = h⁰(M) + h²(M) + ε·dim M`, with `H¹(D_A, M)` finite.  This is the statement of the axiom
node `Work.SSGRoute.local_tate_duality_euler`. -/
def EulerCharInput (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] : Prop :=
  ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
    ∃ ε, ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ∧
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) +
              Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) +
            ε * Module.finrank (ZMod p) M

/-- **Tate duality in degrees 0 and 2** (`E7b`), named: for every finite place `A`,
`h²(M) = h⁰(M^∨(1))` and `h²(M^∨(1)) = h⁰(M)`, with `M^∨(1) = DualMod p (M ⊗ T)`.  This is the
statement of the axiom node `Work.SSGRoute.local_tate_duality_02`. -/
def Deg02Input (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) : Prop :=
  ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A), ∀ (M : Type)
      [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
      (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
        Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)))

/-- The Euler characteristic of the node `Work.SSGRoute.local_tate_duality_euler`. -/
theorem eulerCharInput_of_node (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] : EulerCharInput p k Ω K :=
  fun A hA => Work.SSGRoute.local_tate_duality_euler p k Ω K A hA

/-- The `0`/`2`-duality of the node `Work.SSGRoute.local_tate_duality_02`. -/
theorem deg02Input_of_node (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    Deg02Input p k Ω K ζ hζ hζK T hT :=
  fun A hA M => Work.SSGRoute.local_tate_duality_02 p k Ω K ζ hζ hζK T hT A hA M

section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **The canonical finite-place family** glued from the two `E7` inputs: the `E7Fin` lane's per-place
pairings, assembled into a single family (`Classical.choose` of the proved lemma
`Work.SSGRoute.PT.pt_canonicalFin_clauses_of_euler02`), with the archimedean family cut in at the
groups generated by an involution.  It is this *named* object that the `E8` reciprocity statement is
about, so that the `E8` lane needs to know nothing about the glue. -/
noncomputable def canonicalFin (hE : EulerCharInput p k Ω K)
    (h02 : Deg02Input p k Ω K ζ hζ hζK T hT) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p :=
  fun M _ _ _ _ _ =>
    Classical.choose (pt_canonicalFin_clauses_of_euler02 p k Ω K ζ hζ hζK T hT M hE h02)

/-- The clauses (1)–(4) of `canonicalFin` at the decomposition group of every finite place. -/
theorem canonicalFin_pairClauses (hE : EulerCharInput p k Ω K)
    (h02 : Deg02Input p k Ω K ζ hζ hζK T hT)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      H1Pair.PairClauses p K T M
        (fun a b => canonicalFin p k Ω K ζ hζ hζK T hT hE h02 M (SSGRoute.decomp k A) a b)
        (SSGRoute.decomp k A) :=
  (Classical.choose_spec (pt_canonicalFin_clauses_of_euler02 p k Ω K ζ hζ hζK T hT M hE h02)).1

/-- `canonicalFin` agrees with the canonical archimedean family at every involution group. -/
theorem canonicalFin_arch (hE : EulerCharInput p k Ω K)
    (h02 : Deg02Input p k Ω K ζ hζ hζK T hT)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (c : Ω ≃ₐ[k] Ω), c ^ 2 = 1 → H = Subgroup.zpowers c →
      ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
        canonicalFin p k Ω K ζ hζ hζK T hT hE h02 M H a b =
          Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M H a b :=
  (Classical.choose_spec (pt_canonicalFin_clauses_of_euler02 p k Ω K ζ hζ hζK T hT M hE h02)).2

/-- **The E8 input, in the mixed form, for the canonical glued family** — Hasse reciprocity for the
pairing glued from the two `E7` inputs: the sum over one place per prime of a large enough finite set
`S'` of the finite-place values of `canonicalFin` plus the sum over one involution per real place of
the canonical archimedean family `E7Arch.pairArchFamily` vanishes on global locally constant
cocycles.  For `p ≠ 2` the archimedean sum vanishes identically and this is the finite-only sum. -/
def MixedReciprocity (hE : EulerCharInput p k Ω K)
    (h02 : Deg02Input p k Ω K ζ hζ hζK T hT) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
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
    ∑ A ∈ S', canonicalFin p k Ω K ζ hζ hζK T hT hE h02 M (SSGRoute.decomp k A) a b +
      ∑ c ∈ C', Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M
        (Subgroup.zpowers c) a b = 0

/-- **The E8 input at the two nodes**, as a self-contained proposition: the mixed reciprocity law of
`MixedReciprocity` for the family glued from the (node-derived) `EulerCharInput` and `Deg02Input`.
This is the statement to hand to the `E8` lane: it mentions only names, no glue. -/
def NodeMixedReciprocity : Prop :=
  MixedReciprocity p k Ω K ζ hζ hζK T hT (eulerCharInput_of_node p k Ω K)
    (deg02Input_of_node p k Ω K ζ hζ hζK T hT)

end

end

end Work.SSGRoute.PT
