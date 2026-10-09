import Mathlib
import Submission.Work.SSGRoute.G1_cup_assembly
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Definitions for the `hrecJoint` route (`HRECJOINT_DESIGN.md`)

Elaborated from `HRec/drafts/HrecDefs.lean.txt` (first prover's pass).  Two deviations from the
draft, both forced by elaboration and both making the route *shorter*:

* **The fibre of `LocV` is the cochain space, not `H2loc`.**  The draft's
  `LocV = (Π₀ H, H2loc … H) × 𝔽_p` does not elaborate: type-class search cannot synthesise the
  dependent instance `∀ H, Zero (H2loc … H)` that `DFinsupp` needs (although the fibre instances
  are found at a single subgroup; declaring them explicitly does fix `LocV` itself, but every use
  of `DFinsupp.single` then has to be fed a *class*, which is what the design's `classOf` does).
  Instead we index by subgroups with the **cochain space** `(G_k → G_k → μ_p)` as fibre and put the
  *coboundaries* into `recipSpan`: a functional killing `recipSpan` then kills coboundaries, i.e. it
  is well-defined on classes, which is exactly the property the draft obtains from `mkQ`.
  Consequently the draft's `classOf`, `toLocV` and the whole quotient machinery disappear, and the
  nodes `A4`/`A5` of the design are not needed.
* **`open scoped TensorProduct`** is required for the `M ⊗[ZMod p] T` of the statement.

`invQ H c = recipChi (single H c, 0)` is a plain function on all cochains; its additivity
(`hinv_add`) and its vanishing on coboundaries (`hinv_cob`) are the statements `invQ_add` /
`invQ_cob` of Part A, and on a *cocycle* `c` its value is `recipChi` of the class of `c`, because
`recipChi` kills every coboundary vector.
-/

open scoped Classical TensorProduct
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.HRec

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- The `Π₀`-part of `LocV`: one copy of the cochain space of local classes for every subgroup `H`
(finitely supported).  The finite support is the "locality" of the reciprocity relation; the
coboundary vectors are put into `recipSpan` so that a functional killing `recipSpan` is
well-defined on cohomology classes. -/
abbrev LocPi (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Type :=
  Π₀ _H : Subgroup (Ω ≃ₐ[k] Ω),
    ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T)

/-- The space of local classes: one local cochain space for every subgroup `H` (finitely
supported), plus one scalar slot that carries the archimedean values. -/
abbrev LocV (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] : Type :=
  LocPi p k Ω K T × ZMod p

/-- The hypotheses of `hrecJoint`, bundled: global locally constant cocycles `a`, `b`, a system
`S'` of finite places (one per conjugacy class, containing every bad place) and a system `C'` of
involutions (one per conjugacy class of involutions `≠ 1`). -/
def IsRecipDatum (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (S' : Finset (ValuationSubring Ω)) (C' : Finset (Ω ≃ₐ[k] Ω)) : Prop :=
  SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a ∧ SSGRoute.IsLocConstOn ⊤ a ∧
  SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
  (∀ A ∈ S', SSGRoute.IsFinPlace k A) ∧
  (∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
    ¬ B.valuation (p : Ω) < 1 ∧ ¬ SSGRoute.IsRamifiedIn k K B ∧
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) ∧
  (∀ c ∈ C', c ^ 2 = 1) ∧
  (∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C', ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹) ∧
  (∀ c ∈ C', ∀ c' ∈ C', (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c')

/-- The reciprocity relation vector of a datum: the local cup cochains at the chosen finite places,
and the sum of the archimedean values in the scalar slot. -/
def relVec (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (S' : Finset (ValuationSubring Ω)) (C' : Finset (Ω ≃ₐ[k] Ω)) : LocV p k Ω K T :=
  (∑ A ∈ S', DFinsupp.single (SSGRoute.decomp k A)
      (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b),
    ∑ c ∈ C', Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M
      (Subgroup.zpowers c) a b)

/-- The span of all reciprocity relation vectors, together with the coboundary vectors (so that a
functional killing the span is well-defined on local cohomology classes). -/
def recipSpan : Submodule (ZMod p) (LocV p k Ω K T) :=
  Submodule.span (ZMod p)
    ({v | ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod p) M)
        (_ : DistribMulAction (K ≃ₐ[k] K) M) (_ : SMulCommClass (K ≃ₐ[k] K) (ZMod p) M)
        (_ : Finite M) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (S' : Finset (ValuationSubring Ω)) (C' : Finset (Ω ≃ₐ[k] Ω)),
        IsRecipDatum p k Ω K T M a b S' C' ∧
          v = relVec p k Ω K ζ hζ hζK T hT M a b S' C'} ∪
      {v | ∃ (H : Subgroup (Ω ≃ₐ[k] Ω))
        (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
        c ∈ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) H ∧
          v = (DFinsupp.single H c, 0)})

/-- A functional on local classes is nondegenerate at the finite places: it is nonzero on the class
of every nonzero local class at a finite place (stated on cochains, which the coboundary part of
`recipSpan` makes well-defined). -/
def FinNondeg (χ : LocV p k Ω K T →ₗ[ZMod p] ZMod p) : Prop :=
  ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
    ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
      c ∈ Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) →
      c ∉ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) →
      χ (DFinsupp.single (SSGRoute.decomp k A) c, 0) ≠ 0

/-- Archimedean consistency: some functional kills every reciprocity relation and is `1` on the
scalar slot.  Automatic for odd `p`; for `p = 2` it is the parity law `Parity2`. -/
def ArchConsistent : Prop :=
  ∃ χ : LocV p k Ω K T →ₗ[ZMod p] ZMod p,
    recipSpan p k Ω K ζ hζ hζK T hT ≤ LinearMap.ker χ ∧ χ (0, 1) = 1

/-- The reciprocity functional: nondegenerate at the finite places if possible, else merely
archimedean-consistent if possible, else `0`.  In every branch it kills `recipSpan`. -/
def recipChi : LocV p k Ω K T →ₗ[ZMod p] ZMod p :=
  if h : ∃ χ : LocV p k Ω K T →ₗ[ZMod p] ZMod p,
      recipSpan p k Ω K ζ hζ hζK T hT ≤ LinearMap.ker χ ∧ χ (0, 1) = 1 ∧
        FinNondeg p k Ω K T χ then Classical.choose h
  else if h' : ArchConsistent p k Ω K ζ hζ hζK T hT then Classical.choose h'
  else 0

/-- The local invariant functional fed to `canonical_localPairing_with_reciprocity_of_cupData`:
`invQ H c = recipChi` of the cochain `c` placed at `H`.  This is a plain function; its additivity on
*all* cochains (`hinv_add`) and its vanishing on locally constant coboundaries (`hinv_cob`, from the
coboundary vectors lying in `recipSpan`) are the Part A statements `invQ_add` and `invQ_cob`.  On a
locally constant `2`-cocycle `c` on `H` it agrees with `recipChi` of *the class* of `c`. -/
def invQ (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) → ZMod p :=
  fun c => recipChi p k Ω K ζ hζ hζK T hT (DFinsupp.single H c, 0)

@[simp] theorem invQ_apply (H : Subgroup (Ω ≃ₐ[k] Ω))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) :
    invQ p k Ω K ζ hζ hζK T hT H c
      = recipChi p k Ω K ζ hζ hζK T hT (DFinsupp.single H c, 0) := rfl

/-- The `p = 2` parity law for cup classes (Hilbert reciprocity in support-count form): the number
of finite places of `S'` where the local cup class is nonzero, plus the archimedean values, is even.
The cup cochain is a locally constant `2`-cocycle (`Work.SSGRoute.evCupFun_isCocycle2On`), so its
class vanishes exactly when it is a coboundary. -/
def Parity2 : Prop :=
  p = 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (S' : Finset (ValuationSubring Ω)) (C' : Finset (Ω ≃ₐ[k] Ω)),
    IsRecipDatum p k Ω K T M a b S' C' →
      (∑ A ∈ S', if Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
          Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
            (SSGRoute.decomp k A) then (0 : ZMod p) else 1) +
        ∑ c ∈ C', Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M
          (Subgroup.zpowers c) a b = 0

end

end Work.SSGRoute.HRec
