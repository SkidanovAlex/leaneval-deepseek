import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PT.LocProd
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` localisation vocabulary, relocated *below* the node

`Submission/Work/SSGRoute/ZSplit/levelKCounting.lean` (the `ZSplit` lane) introduces the level-`K`
vocabulary of the `z`-construction: the level-`K` local group `decomp k A ⊓ K.fixingSubgroup`, the
level-`K` local `H¹`, the level-`K` conjugacy of places, the primal class space `kPrimalClasses`, the
predicates `kRealizable` (local data realisable by a global class, unramified at the finite places
outside `S` that are *not* split in the auxiliary field `Λ`) and `kDualSelmer` (the mirror
conditions), and the abstract pairing predicate `kLocalPairing`.

That module imports `Submission.Work.SSGRoute.shafarevich_theorem13`, which imports the node
`Submission.Work.SSGRoute.shafarevich_z_construction`; consequently the whole level-`K` vocabulary
lives *above* the node and cannot be consumed by the node's own development.  This module relocates
the definitions verbatim (into the namespace `Work.SSGRoute.ZConstruction`, so that nothing clashes
with the originals) with an import list that stays strictly below the node.  Everything here is a
definitional copy; the content is the *availability* below the node.

Purpose: `Work.SSGRoute.AuxRealisationNoInv` (the realisation gate of the p. 18 auxiliary class,
`ZConstruction/AuxAssembly.lean`) is, after the §4 analysis, the level-`K` Poitou--Tate
"realisation from the dual Selmer condition" statement in the vocabulary of `kRealizable` /
`kDualSelmer`; with the vocabulary below the node, the gate can be *reduced* to the level-`K`
counting identity of the `ZSplit`/`PT` lanes (see `ZConstruction/AuxRealisationCounting.lean`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- The **level-`K` local group** at the place `A`: the decomposition group of `A` over `K`. -/
abbrev kLocalGroup (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  SSGRoute.decomp k A ⊓ K.fixingSubgroup

/-- The **level-`K` local `H¹`** at the place `A`, with `μ_p`-coefficients (trivial on `G_K`). -/
abbrev kH1loc (A : ValuationSubring Ω) : Type :=
  H1loc p k Ω K (ZMod p) (kLocalGroup k Ω K A)

/-- **Level-`K` conjugacy of places**: `B` is a `G_K`-conjugate of `A`, i.e. `A` and `B` lie over the
same prime of `K`.

This — not `SSGRoute.IsConjPlace k` — is the conjugacy to use in the level-`K` local conditions.  At
the level `⊤` the two agree in effect, because a class on all of `G_k` satisfies
`x (σ⁻¹ h σ) = x σ⁻¹ + σ⁻¹ • x (h σ)`, so its local components at `k`-conjugate places are conjugate
under the canonical identification.  At the level `K` a class `ν` is defined only on
`G_K = K.fixingSubgroup`, and a `σ` conjugating `A` to `B` lies outside `G_K`; the cocycle identity
does not apply and the local components of `ν` at two `k`-conjugate places are *independent*.  So a
condition of the form 'outside the `k`-conjugates of `S`' would be no condition at all at the other
places over the same prime of `k`, and the localisation problem would not be the level-`K` one. -/
def kConj (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    (A B : ValuationSubring Ω) : Prop :=
  ∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ τ • A = B

/-- The **level-`K` primal local class space** at `S ∪ C`: one level-`K` local `H¹`-class at each
place of one place per prime in `S`, and at each involution of `C` (local group
`⟨c⟩ ⊓ K.fixingSubgroup`). -/
abbrev kPrimalClasses (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω)) : Type :=
  ((A : {A : ValuationSubring Ω // A ∈ S}) →
      kH1loc p k Ω K A.1) ×
    ((c : {c : Ω ≃ₐ[k] Ω // c ∈ C}) →
      H1loc p k Ω K (ZMod p) (Subgroup.zpowers c.1 ⊓ K.fixingSubgroup))

/-- The level-`K` local class tuple of a pair of local data families. -/
def kClassOf (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → ZMod p) :
    kPrimalClasses p k Ω K S C :=
  (fun A => toClass p k Ω K (ZMod p) (kLocalGroup k Ω K A.1) (α A.1),
    fun c => toClass p k Ω K (ZMod p) (Subgroup.zpowers c.1 ⊓ K.fixingSubgroup) (β c.1))

/-- **A level-`K` primal class is realizable** if some global locally constant class `ν` over `K`
(a cocycle and locally constant on `K.fixingSubgroup`) has the prescribed local classes at `S ∪ C`
and is unramified at the finite places outside `S` that are not split in `Λ`. -/
def kRealizable (Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (C : Finset (Ω ≃ₐ[k] Ω)) (x : kPrimalClasses p k Ω K S C) : Prop :=
  ∃ (α : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (β : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → ZMod p) (ν : (Ω ≃ₐ[k] Ω) → ZMod p),
    kClassOf p k Ω K S C α β = x ∧
    IsCocycleOn (res k K) K.fixingSubgroup ν ∧ IsLocConstOn K.fixingSubgroup ν ∧
    (∀ A ∈ S, IsCoboundaryOn (res k K) (kLocalGroup k Ω K A)
      (fun σ => ν σ - α A σ)) ∧
    (∀ c ∈ C, IsCoboundaryOn (res k K) (Subgroup.zpowers c ⊓ K.fixingSubgroup)
      (fun σ => ν σ - β c σ)) ∧
    ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ kConj k Ω K A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0

/-- **A level-`K` dual class lies in the relaxed dual Selmer group** if some global locally constant
class `b` over `K` has it as its local class tuple and satisfies the mirror local conditions: it
vanishes (as a local class) at the finite places outside `S` that *are* split in `Λ`, and it is
unramified at the other finite places outside `S`. -/
def kDualSelmer (Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (C : Finset (Ω ≃ₐ[k] Ω)) (y : kPrimalClasses p k Ω K S C) : Prop :=
  ∃ b : (Ω ≃ₐ[k] Ω) → ZMod p,
    kClassOf p k Ω K S C (fun _ => b) (fun _ => b) = y ∧
    IsCocycleOn (res k K) K.fixingSubgroup b ∧ IsLocConstOn K.fixingSubgroup b ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ kConj k Ω K A B) → IsSplitIn k Λ B →
      IsCoboundaryOn (res k K) (kLocalGroup k Ω K B) b) ∧
    ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ kConj k Ω K A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → b σ = 0

/-- **The level-`K` local Tate pairing** on the local class spaces, as it appears in the counting
argument: a pairing on `kPrimalClasses S C` which is `𝔽_p`-bilinear on the class tuples and
non-degenerate in both variables (this is the perfectness of the Tate local pairing, Tate's local
duality, at the level-`K` local groups). -/
def kLocalPairing (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (pair : kPrimalClasses p k Ω K S C → kPrimalClasses p k Ω K S C → ZMod p) : Prop :=
  (∀ x y z, pair (x + y) z = pair x z + pair y z) ∧
  (∀ x y z, pair x (y + z) = pair x y + pair x z) ∧
  (∀ x, (∀ y, pair x y = 0) → x = 0) ∧
  (∀ y, (∀ x, pair x y = 0) → y = 0)

end

end Work.SSGRoute.ZConstruction
