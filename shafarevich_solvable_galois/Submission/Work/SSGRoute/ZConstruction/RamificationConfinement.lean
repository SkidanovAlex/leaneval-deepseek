import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
import Submission.Work.SSGRoute.ZConstruction.exists_level_vanishing_minimal_ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The confinement of the ramification of a `z`-data witness

(Module `Submission.Work.SSGRoute.ZConstruction.RamificationConfinement`, namespace
`Work.SSGRoute.ZConstruction`.)

This file records the two structural facts about the ramification of a `z`-data witness
`Work.SSGRoute.HasZData K Λ S y z` which decide the architecture of the induction step of
Schmidt--Wingberg §4 (the level step `Work.SSGRoute.hasZData_sum_of_level_data`) and which settle
one of the open design questions recorded in `ZConstruction/NOTE_p18_interface.lean`.

## 1. The confinement

`Work.SSGRoute.HasZData`'s fifth clause says that `z` kills the inertia of every finite place outside
`cs(S)` that is *not* split in the auxiliary field `Λ`.  Contrapositively (`SSGRoute.IsInertia` is
the pair "(decomposition) + (trivial on the residue field)", so `z` is "ramified at `B`" exactly
when some element of `K.fixingSubgroup` lies in the inertia of `B` and has `z ≠ 0` there):

  `hasZData_ramification_confined`: **the ramification of `z` outside `cs(S)` is confined to the
  places splitting completely in `Λ`**.

This is the *confinement* that the sixth clause of the `z`-data is about: the sharpened condition
(b) of the paper is only imposed at the places outside `cs(S)` that split in `Λ`, and the fifth
clause says precisely that there are no others.  Consequently the sixth clause is not a condition on
"the ramification of `z`" but on *all* the ramification of `z` outside `cs(S)`.

## 2. The new places of the level step are split in `Λ`

In the level step the enlarged place set is `S' = S ∪ Ram(N|k)`, where `N` is a finite Galois level
over which `z₀` (the witness of the induction hypothesis) vanishes; the "new" places of the step are
the places of `cs(S') ∖ cs(S)`, i.e. the places ramified in `N` and not conjugate into `S`.

`isSplitIn_of_ramified_explained` shows: **if every place ramified in `N` is `k`-conjugate to a place
at which `z₀` is ramified, then every new place is split completely in `Λ`.**  (Proof: such a place
is conjugate to a place `Q` at which `z₀` ramifies, `Q` is again outside `cs(S)`, so `Q` is split in
`Λ` by §1, and splitting in `Λ` is invariant under `k`-conjugation because `Λ/k` is Galois.)

For the *intended* choice of the level (`N` = the Galois closure over `k` of the field cut out by
`z₀`, or any level whose ramification is explained by that of `z₀`) the hypothesis of
`isSplitIn_of_ramified_explained` is met, so:

> **the new places of the level step are all split completely in `Λ`.**

## 3. What this settles

This is the precise reason why the *weakened* level step
`Work.SSGRoute.ZConstruction.hasZData_sum_of_level_data_unram`
(`ZConstruction/hasZData_sum_of_level_data_unram.lean`) is *not* applicable to the intended
application: that variant replaces the vanishing hypothesis `hvanish` at the new places by the
inertia-killing of the auxiliary class and the side condition `hnoSplitS'` ("no place of
`cs(S') ∖ cs(S)` is split in `Λ`"), and by §2 the side condition *fails at every new place*.

The level step therefore genuinely needs the auxiliary class to vanish (pointwise, on the
decomposition groups) at the places of `cs(S') ∖ cs(S)` — i.e. the third prescription of
`Work.SSGRoute.AuxExists`/`Work.SSGRoute.ZConstruction.AuxExistsWeakened`, the clause which the
relaxed Poitou--Tate realisation of p. 18 has to supply.  See `ZConstruction/NOTE_gate_state.lean`
for the resulting list of gates.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

namespace ZConstruction

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {E : Type} [AddCommGroup E]

/-- **The confinement of the ramification of a `z`-data witness.**  A finite place `B` that is not
conjugate into `S` and at which `z` is ramified (i.e. on whose inertia `z` does not vanish) splits
completely in the auxiliary field `Λ`.  This is the contrapositive of the fifth clause of
`Work.SSGRoute.HasZData`. -/
theorem hasZData_ramification_confined
    {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : HasZData K Λ S y z)
    {B : ValuationSubring Ω} (hB : IsFinPlace k B)
    (hram : ∃ σ ∈ K.fixingSubgroup, IsInertia k B σ ∧ z σ ≠ 0)
    (hnotS : ∀ A ∈ S, ¬ IsConjPlace k A B) :
    IsSplitIn k Λ B := by
  by_contra hns
  obtain ⟨σ, hσK, hσI, hσne⟩ := hram
  exact hσne (h.2.2.2.2.1 B hB hnotS hns σ hσK hσI)

/-- **The new places of the level step are split in `Λ`.**  If every place ramified in a level `N`
is `k`-conjugate to a place at which the `z`-data witness `z` is ramified, then every place ramified
in `N` and not conjugate into `S` splits completely in `Λ`.

The hypothesis `hcov` is the abstracted form of "`N` is the Galois closure over `k` of the field cut
out by `z`" (equivalently: the ramification of `N` is explained by the ramification of `z`), which is
how the level of the paper's level step is chosen. -/
theorem isSplitIn_of_ramified_explained
    {K Λ N : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    (hNorm : (Λ.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal)
    {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : HasZData K Λ S y z)
    (hcov : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      IsRamifiedIn k N B →
      ∃ Q : ValuationSubring Ω, IsConjPlace k B Q ∧
        ∃ σ ∈ K.fixingSubgroup, IsInertia k Q σ ∧ z σ ≠ 0)
    {B : ValuationSubring Ω} (hB : IsFinPlace k B)
    (hram : IsRamifiedIn k N B)
    (hnotS : ∀ A ∈ S, ¬ IsConjPlace k A B) :
    IsSplitIn k Λ B := by
  obtain ⟨Q, hBQ, hQram⟩ := hcov B hB hram
  have hQfin : IsFinPlace k Q := by
    obtain ⟨σ, rfl⟩ := hBQ
    rwa [isFinPlace_smul_iff]
  have hnotS' : ∀ A ∈ S, ¬ IsConjPlace k A Q := by
    intro A hA hAQ
    exact hnotS A hA (isConjPlace_trans hAQ (isConjPlace_symm hBQ))
  have hQ : IsSplitIn k Λ Q :=
    hasZData_ramification_confined h hQfin hQram hnotS'
  obtain ⟨τ, hτ⟩ := hBQ
  exact (isSplitIn_conj Λ hNorm B τ).mp (by rw [hτ]; exact hQ)

/-- The existential form of `isSplitIn_of_ramified_explained`: if there is a place ramified in `N`
and outside `cs(S)`, and the ramification of `N` is explained by that of `z`, then there is a place
ramified in `N` and outside `cs(S)` which splits completely in `Λ`.  (This is the failure of the side
condition `hnoSplitS'` of the weakened level step in its intended application.) -/
theorem exists_isSplitIn_of_exists_ramified_explained
    {K Λ N : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    (hNorm : (Λ.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal)
    {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : HasZData K Λ S y z)
    (hcov : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      IsRamifiedIn k N B →
      ∃ Q : ValuationSubring Ω, IsConjPlace k B Q ∧
        ∃ σ ∈ K.fixingSubgroup, IsInertia k Q σ ∧ z σ ≠ 0)
    (hex : ∃ B : ValuationSubring Ω, IsFinPlace k B ∧ IsRamifiedIn k N B ∧
      ∀ A ∈ S, ¬ IsConjPlace k A B) :
    ∃ B : ValuationSubring Ω, IsFinPlace k B ∧ IsRamifiedIn k N B ∧
      (∀ A ∈ S, ¬ IsConjPlace k A B) ∧ IsSplitIn k Λ B := by
  obtain ⟨B, hB, hram, hnotS⟩ := hex
  exact ⟨B, hB, hram, hnotS, isSplitIn_of_ramified_explained hNorm h hcov hB hram hnotS⟩

/-- **The new places of the level step are split in `Λ`, in the form in which the level step can
consume it.**  If `z` carries the `z`-data `HasZData K Λ S y z`, then there is a finite Galois level
`N ⊇ K` on which `z` vanishes and *whose ramification outside `cs(S)`* (and away from the places
ramified in `K|k`) consists of places splitting completely in `Λ`.

This is `exists_level_vanishing_minimal_ramification` (the minimal level: the level of `z` has a
ramification explained by that of `z`, whence every place ramified in it and outside `cs(S)` is
`Λ`-split by the confinement) followed by `isSplitIn_of_ramified_explained`.  It is the precise
statement of the session finding: for the level chosen by the level step, every new place is
`Λ`-split, so the side condition `hnoSplitS'` of
`Work.SSGRoute.ZConstruction.hasZData_sum_of_level_data_unram` cannot be met. -/
theorem exists_level_vanishing_newPlaces_isSplitIn
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    {S : Finset (ValuationSubring Ω)}
    (hNorm : (Λ.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal)
    {E : Type} [AddCommGroup E] {y z : (Ω ≃ₐ[k] Ω) → E}
    (h : HasZData K Λ S y z) :
    ∃ N : IntermediateField k Ω, K ≤ N ∧ FiniteDimensional k N ∧ IsGalois k N ∧
      (∀ g ∈ N.fixingSubgroup, z g = 0) ∧
      ∀ B : ValuationSubring Ω, IsFinPlace k B → ¬ IsRamifiedIn k K B →
        (∀ A ∈ S, ¬ IsConjPlace k A B) → IsRamifiedIn k N B → IsSplitIn k Λ B := by
  classical
  obtain ⟨N, hKN, hNfin, hNgal, hNv, hNunr⟩ :=
    exists_level_vanishing_minimal_ramification (K := K) h.1 h.2.1
  refine ⟨N, hKN, hNfin, hNgal, hNv, ?_⟩
  intro B hB hKunram hnotS hram
  -- the minimal-level result, contrapositively: some conjugate of `B` is ramified for `z`
  have hQ : ∃ Q : ValuationSubring Ω, IsConjPlace k B Q ∧
      ∃ σ ∈ K.fixingSubgroup, IsInertia k Q σ ∧ z σ ≠ 0 := by
    by_contra hcon
    refine hNunr B hB hKunram (fun τ σ hσ hI => ?_) hram
    by_contra hne
    exact hcon ⟨τ • B, ⟨τ, rfl⟩, σ, hσ, hI, hne⟩
  obtain ⟨Q, hBQ, hQram⟩ := hQ
  have hQfin : IsFinPlace k Q := by
    obtain ⟨σ, rfl⟩ := hBQ
    rwa [isFinPlace_smul_iff]
  have hnotS' : ∀ A ∈ S, ¬ IsConjPlace k A Q := by
    intro A hA hAQ
    exact hnotS A hA (isConjPlace_trans hAQ (isConjPlace_symm hBQ))
  have hQsplit : IsSplitIn k Λ Q := hasZData_ramification_confined h hQfin hQram hnotS'
  obtain ⟨τ, hτ⟩ := hBQ
  exact (isSplitIn_conj Λ hNorm B τ).mp (by rw [hτ]; exact hQsplit)

end ZConstruction

end Work.SSGRoute
