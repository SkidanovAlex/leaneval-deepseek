import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.ZConstruction.ZDataAux
import Submission.Work.SSGRoute.ZDataMup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The three gates of the p. 18 auxiliary-class step (interface)

`Work.SSGRoute.AuxExists` (`ZConstruction/ZDataAux.lean`) is the class `ỹ` of Schmidt--Wingberg
§4, p. 18, and is now the *only* obligation of the node `Work.SSGRoute.shafarevich_z_construction`
(the μ_p half being `Work.SSGRoute.MupGate`, available from the two cores).  This file breaks it
into three gates, each stated in the level-`K` vocabulary of `ZDataMup/Defs.lean`, so that they can
be attacked independently:

* **`AuxPairingGate K`** (gate **P**) -- the canonical level-`K` local Tate pairing on the trivial
  module `ZMod p`: a single family `pair` satisfying the local axioms `IsLocalTateSystem`, the
  Hilbert-symbol product formula `IsProductFormula`, and the *unramified orthogonality*
  `IsUnramifiedOrthogonal` (the local pairing of two classes that are both trivial on the inertia
  vanishes; this is `Br(K_𝔭^{un}/K_𝔭) = 0` and is the local input of the p. 18 chase).

* **`AuxOrthogonalityGate K Λ M S`** (gate **O**) -- the *diagram chase of p. 18*: for any pair with
  the three properties of (P), any datum `y₁` satisfying the hypotheses `ZHyp` at `(Λ,S)`, and any
  *relaxed dual* class `b` (a cocycle on `G_K`, unramified outside the level-`K` conjugacy classes
  of `T`, and locally trivial at the places outside `cs(T)` that split completely in `Λ`),
  the prescribed datum `auxDatum K S y₁` of `y₁` is orthogonal to `b`:
  `∑_{A ∈ T} pair (decomp k A ⊓ K.fixingSubgroup) (auxDatum K S y₁ A) b = 0`.
  The proof is Hilbert reciprocity applied to the global class `y₁` and `b` over a place set
  containing the ramification of `y₁`; the terms at the ramification places of `y₁` vanish because
  those places are `Λ`-split (`hyS` of `ZHyp`) and `b` is locally trivial there (the relaxation),
  and the remaining terms at places outside `cs(S)` vanish by the unramified orthogonality of (P).

* **`AuxRealisationGate K M`** (gate **R**) -- the Tate--Poitou degree-one realisation: local
  data at a finite set `T` of pairwise non-`K`-conjugate finite places which is orthogonal to *all*
  relaxed dual classes is realised by a global cocycle `z` on `G_K` which is unramified outside the
  level-`K` conjugates of `T` and agrees with the datum at `T` (pointwise, i.e. at level `K` the
  local coboundaries are the zero functions).

The assembly (P) + (O) + (R) ⟹ `AuxExists` is the node's business and is *not* in this file.

## The reciprocity bookkeeping: what the p. 18 chase needs from the local system

Writing out the derivation of the orthogonality of `auxDatum` (Hilbert reciprocity over a place set
`T''` containing every place at which `y₁` or `b` is ramified, plus the vanishing of the extra
terms) fixes three requirements, recorded here because they are *not* forced by the four axioms of
`ZDataMup.IsLocalTateSystem`:

1. **The place-set structure.**  `T''` has to *contain* `T` as a set, not merely meet every
   level-`K` class of `T`.  Otherwise the terms of `T` and the corresponding terms of `T''` live on
   `K`-conjugate (but distinct) local groups, and comparing them needs the local system to be
   invariant under level-`K` conjugation — which the four axioms do not provide.  The finite place
   set covering the ramification of `y₁` is produced (up to `G_k`-conjugacy) by
   `Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces`; upgrading that cover to one by
   *level-`K`* classes is the technical point, and it is the reason that the term at a place of
   `T ∖ cs(S)` is not controlled by the four axioms alone.

2. **The level-`K` cover.**  The product formula's unramifiedness hypothesis is stated in terms of
   *level-`K`* conjugacy, whereas the finiteness statement of the workspace
   (`exists_finset_ramifiedPlaces`) is stated in terms of `G_k`-conjugacy.  A `G_k`-class is a
   finite union of level-`K` classes, so the two are inter-derivable, but the passage has to be
   made.

3. **The dual condition has to be global at the non-split places** —
   `Work.SSGRoute.IsRelaxedDualStrong`: with the unconstrained condition `IsRelaxedDual`, the terms
   at the places of `T ∖ cs(S)` are not controlled and the chase needs the additional hypothesis
   `hνS₀` ("the datum has no component at `S₀ ∖ T`"), which is unavailable for the line component of
   the §4 datum; with the strengthened condition those terms vanish by the unramified orthogonality
   of gate (P), because a place of `T ∖ cs(S)` on which the §4 construction puts data is ramified in
   the level `M` of the other summand, hence *not* `M`-split, and `y₁` is unramified there (all its
   ramification outside `cs(S)` is `Λ`-split, hence `M`-split).

## Notes on the level-`K` conjugacy

At level `K` the local components of a cocycle on `G_K` at two `G_k`-conjugate places are
*independent* (`ZSplit/LEVELK_STATUS.md`), so every condition has to be checked at one place per
`G_K`-class (`KConj`), and the prescription `auxDatum` is consistent over `G_k`-conjugates because
the cochain is additive, hence conjugation-invariant by elements of `G_K`
(`Work.SSGRoute.zadd_conj`).
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **Level-`K` conjugacy of places**: `A` and `B` lie over the same prime of `K`.  At level `K`
this (and not `G_k`-conjugacy) is the equivalence relation along which local conditions are
constant. -/
def KConj (K : IntermediateField k Ω) (A B : ValuationSubring Ω) : Prop :=
  ∃ τ ∈ K.fixingSubgroup, τ • A = B

/-- **The prescribed datum of the auxiliary construction**: the local data of `y₁` at the places
conjugate into `S` (over `k`), extended by zero at every other place.  In the paper this is the
datum which the class `ỹ` of p. 18 has to realise at the places of `S` while vanishing at the
places of `S' ∖ S`. -/
noncomputable def auxDatum (K : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (y₁ : (Ω ≃ₐ[k] Ω) → ZMod p) : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p :=
  fun B => if ∃ A ∈ S, SSGRoute.IsConjPlace k A B then y₁ else 0

/-- **Unramified orthogonality of a local Tate system.**  The local pairing of two local classes
which are both trivial on the inertia vanishes.  This is the local input
`Br(K_𝔭^{un}/K_𝔭) = 0` of the p. 18 chase; it is *not* among the four axioms of
`ZDataMup.IsLocalTateSystem`. -/
def IsUnramifiedOrthogonal (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) : Prop :=
  ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
    ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) →
      (∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → a σ = 0) →
      (∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → b σ = 0) →
      pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a b = 0

/-- **The relaxed dual Selmer condition at level `K`** (the mirror conditions of
`ZSplit/levelKCounting.lean`): `b` is a cocycle on `G_K` which is unramified outside the level-`K`
conjugacy classes of `T` and *locally trivial* at the places outside `cs(T)` that split completely
in the auxiliary field `Λ`.  This is the range of the orthogonality of the p. 18 chase. -/
def IsRelaxedDual (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (b : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup b ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → b σ = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
    SSGRoute.IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → b σ = 0)

/-- **The *strengthened* relaxed dual Selmer condition**: as `IsRelaxedDual`, but the
unramifiedness is required at *every* finite place that is not split in `M`, not only outside
`cs(T)`.

This is the condition under which the p. 18 chase actually closes for a place set `T` that contains
the places of `cs(S') ∖ cs(S)`: at such a place `A` (which is ramified in the level `N = M` of the
other summand, hence *not* `M`-split) the datum `y₁` is unramified (all ramification of `y₁` outside
`cs(S)` is `Λ`-split, hence `M`-split, by `hyS`), so the reciprocity term `pair A y₁ b` vanishes by
the unramified orthogonality of gate (P), with *no* hypothesis on the datum at `A`.  With the
unconstrained condition `IsRelaxedDual` this term is not controlled and the chase needs the extra
hypothesis `hνS₀` of `ZSplit/levelK_datum_orthogonality.lean` (the datum has no component at
`S₀ ∖ T`), which is not available for the line component of the datum of §4.

`IsRelaxedDualStrong` implies `IsRelaxedDual` (`relaxedDual_of_strong`), so a gate stated with the
strengthened condition implies the corresponding gate with the unconstrained one. -/
def IsRelaxedDualStrong (K Λ M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (b : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup b ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → ¬ SSGRoute.IsSplitIn k M B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → b σ = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
    SSGRoute.IsSplitIn k M B →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → b σ = 0)

/-- The strengthened relaxed dual condition implies the unconstrained one. -/
theorem relaxedDual_of_strong {K Λ M : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    {T : Finset (ValuationSubring Ω)} {b : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsRelaxedDualStrong (p := p) K Λ M T b) : IsRelaxedDual (p := p) K M T b := by
  obtain ⟨hc, hl, hunr, htriv⟩ := h
  refine ⟨hc, hl, ?_, htriv⟩
  intro B hB hnot σ hσK hσI
  by_cases hsp : SSGRoute.IsSplitIn k M B
  · exact htriv B hB hnot hsp σ hσK hσI.1
  · exact hunr B hB hsp σ hσK hσI

/-- **Gate (P): the level-`K` local Tate pairing with the product formula and unramified
orthogonality.**  One family `pair`, with the local axioms at every level-`K` local group, the
Hilbert-symbol product formula, and the vanishing of the pairing of two inertia-trivial classes. -/
def AuxPairingGate (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
    ZDataMup.IsLocalTateSystem p k Ω K pair ∧ ZDataMup.IsProductFormula p k Ω K pair ∧
      IsUnramifiedOrthogonal (p := p) K pair

/- **Gate (O): RETRACTED, and replaced by a theorem.**  The diagram chase of p. 18 is *not* a gate:
it is proved outright, from the local axioms of the pairing alone, as
`Work.SSGRoute.auxDatum_orthogonal_of_productFormula`
(`Submission/Work/SSGRoute/ZConstruction/AuxChase.lean`).

The statement which used to stand here asked for the orthogonality of the prescribed datum against
the classes which are relaxed dual *at a level `M ⊇ Λ`*, and it is **false** as written: the
reciprocity argument needs the prescribed datum to be compared with the global datum `y₁` over a
place set containing the ramification of `y₁`, and the extra places are `Λ`-split (by `ZHyp.hyS`)
but need not be `M`-split (for `Λ ≤ M`, `M`-split implies `Λ`-split, because `fixingSubgroup` is
antitone).  Hence the relaxation level must be `Λ` itself, and the duals must be relaxed *at `Λ`*,
which is exactly what `auxDatum_orthogonal_of_productFormula` proves (with no extra hypothesis: the
places at which `y₁` ramifies outside `cs(S)` lie outside `cs(T)` -- `T` being a cover of the
level-`K` classes of `cs(S)` -- and are `Λ`-split, where a `Λ`-relaxed dual is locally trivial).
A prover of the retracted statement produced the counterexample `k = ℚ`, `K = ℚ(ζ₃)`, `Λ = ℚ`,
`M = ℚ(∛2, ζ₃)`.

Also retracted: the confinement/killing clauses of `Submission/Work/SSGRoute/z_data_mup_level.lean`
and `z_data_two_level.lean` (see those files). -/

/-- **Gate (R): the Tate--Poitou degree-one realisation at level `K`, in the relaxed form.**
SUPERSEDED by `Work.SSGRoute.AuxRealisationExt` (`ZConstruction/AuxAssembly.lean`), which is the form
the §4 assembly consumes: the realisation runs at a place set `T'` inside `cs(S')` containing a base
set `T` of level-`K` representatives of `cs(S)`, the orthogonality hypothesis is stated with the
relaxed duals at the *base* set `T` (the stronger form, which the proved chase supplies), and the
conclusion carries the vanishing on the involutions (free for odd `p`, part of the `p = 2`
correction).  The statement below is kept for the record.  Local
data at a finite set `T` of pairwise non-`K`-conjugate finite places which is orthogonal to every
relaxed dual class (with respect to the relaxation level `M`) is realised by a global cocycle `z` on
`G_K` which is unramified outside the level-`K` conjugates of `T` *at the places that are not split
completely in `M`*, and agrees pointwise with the datum at `T`.

The relative-field exception at the `M`-split places is the relaxation of the level-`K` localisation
(`ZSplit/levelKCounting.lean`, `kRealizable Λ S C x`), and it is what makes the conclusion exactly
the hypothesis `hyS` of `ZHyp` at the pair `(M, T)` as it is used by the §4 assembly
`Work.SSGRoute.hasZData_sum_of_level_data`.  This is the below-node counterpart of
`Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation` (whose statement file lies above this node in the
import order, hence cannot be consumed here); the odd-`p` case. -/
def AuxRealisationGate (K M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p),
    ZDataMup.IsLocalTateSystem p k Ω K pair →
    ZDataMup.IsProductFormula p k Ω K pair →
    IsUnramifiedOrthogonal (p := p) K pair →
    ∀ (T : Finset (ValuationSubring Ω)),
    (∀ A ∈ T, SSGRoute.IsFinPlace k A) →
    (∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B) →
    ∀ (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p),
    (∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
    (∀ A ∈ T, SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A)) →
    (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p, IsRelaxedDual (p := p) K M T b →
      ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0) →
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
        ¬ SSGRoute.IsSplitIn k M B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0)

end Work.SSGRoute
