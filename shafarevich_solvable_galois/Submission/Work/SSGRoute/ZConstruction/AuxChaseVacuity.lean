import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The honest p. 18 chase is *vacuous* in the ramified case (a no-go theorem)

`Work.SSGRoute.ZConstruction.auxDatum_orthogonalToDual`
(`ZConstruction/auxDatum_orthogonalToDual.lean`) proves the honest orthogonality
`ZDataMup.IsOrthogonalToDual K pair T (auxDatum K S y₁)` under the hypothesis package

* `hlev` : `y₁` vanishes on the Galois group `G_N` of a level `N ⊇ Λ`;
* `hT''ram` : the place set `T''` covers the places ramified in `N` up to level-`K` conjugacy;
* `hT''noSplit` : a place of `T''` which is *not* level-`K`-conjugate to `T` is not split in `Λ`.

Those three conditions are meant to let the reciprocity sum over `T''` be evaluated: `y₁` is
inertia-trivial outside `cs(T'')` by `hlev` + `hT''ram`, and the terms at the new places
`T'' ∖ T` die by the unramified orthogonality of the local system *provided* those places are not
`Λ`-split (otherwise `y₁` may be ramified there while the dual class is only unramified).

**The hypothesis package is inconsistent with the ramification of `y₁` outside `cs(S)`.**  Indeed
`ZHyp.hyS` says that `y₁` kills inertia at every finite place outside `cs(S)` that is *not* split in
`Λ`.  If `y₁` is ramified at such a place `B`, then (contrapositive) `B` is `Λ`-split; but `B` is
also ramified in the level `N` of `hlev` (a nonzero value of `y₁` on the inertia of `B` witnesses
`IsRamifiedIn k N B`), so `hT''ram` puts `B` into the level-`K` classes of `T''`, while `B` is not
level-`K`-conjugate to `T` (the places of `T` are `k`-conjugate into `S` and `B` is not), so
`hT''noSplit` says that `B` is *not* `Λ`-split — a contradiction.

Consequently, under the chase's hypotheses `y₁` is unramified outside `cs(S)` (the statement
`Work.SSGRoute.ZConstruction.unramified_outside_cs_of_chase_hypotheses` below), and the chase can
never be applied to a datum that is ramified outside `cs(S)` — which is exactly the case the node
`Work.SSGRoute.shafarevich_z_construction` has to handle (`Work.SSGRoute.z_data_general_of_ramified`
carries the hypothesis `hyram` that `y` is ramified outside `cs(S)`).

**Consequence for the node.**  The honest route to `Work.SSGRoute.AuxExists` — honest chase plus the
honest realisation `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual_odd` — is
closed.  The viable route is the *relaxed* one: the corrected p. 18 chase
`Work.SSGRoute.auxDatum_orthogonal_of_productFormula` (`ZConstruction/AuxChase.lean`, which chooses
the level and the enlarged place set internally and uses the local triviality of the relaxed duals at
the `Λ`-split places) produces the orthogonality hypothesis of the gate
`Work.SSGRoute.AuxRealisationExt`, and `Work.SSGRoute.auxExists_of_pairing_and_realisation_odd`
assembles `Work.SSGRoute.AuxExists` from that gate and `Work.SSGRoute.AuxPairingGate`.  The single
arithmetic obligation is therefore the realisation with the *relaxed* dual family (equivalently the
level-`K` Tate--Poitou middle exactness of the `ZSplit` lane, `kRealizable`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- A place which is level-`K`-conjugate to a place of `T` is `k`-conjugate into `S`, whenever every
place of `T` is `k`-conjugate into `S`. -/
theorem exists_isConjPlace_of_kConj {K : IntermediateField k Ω} {S T : Finset (ValuationSubring Ω)}
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A) :
    ∀ A ∈ T, ∀ B : ValuationSubring Ω, KConj K A B → ∃ A' ∈ S, SSGRoute.IsConjPlace k A' B := by
  intro A hA B hc
  obtain ⟨A', hA', hA'A⟩ := hTconj A hA
  exact ⟨A', hA', SSGRoute.isConjPlace_trans hA'A (kConj_isConjPlace hc)⟩

/-- **The chase's hypotheses force `y₁` to be unramified outside `cs(S)`.**  See the module
docstring: `hlev` + `hT''ram` + `hT''noSplit` + `ZHyp.hyS` leave no room for a place outside `cs(S)`
which is ramified for `y₁` and not split in `Λ`. -/
theorem unramified_outside_cs_of_chase_hypotheses
    {K Λ N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S T T'' : Finset (ValuationSubring Ω)}
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hT''ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      SSGRoute.IsRamifiedIn k N B → ∃ A ∈ T'', KConj K A B)
    (hT''noSplit : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ T'', KConj K A B) → (∀ A ∈ T, ¬ KConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B)
    {y₁ : (Ω ≃ₐ[k] Ω) → ZMod p} (hy₁ : ZHyp (p := p) K Λ S y₁)
    (hlev : ∀ g ∈ N.fixingSubgroup, y₁ g = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y₁ σ = 0 := by
  intro B hB hnotS σ hσK hσI
  by_contra hne
  -- (`y₁ σ ≠ 0` makes `B` ramified in the level `N` of `hlev`)
  have hσN : σ ∉ N.fixingSubgroup := fun hσN => hne (hlev σ hσN)
  have hram : SSGRoute.IsRamifiedIn k N B := ⟨σ, hσI, hσN⟩
  obtain ⟨A, hA, hc⟩ := hT''ram B hB hram
  -- `B` is not level-`K`-conjugate to a place of `T`
  have hnotT : ∀ A₀ ∈ T, ¬ KConj K A₀ B := by
    intro A₀ hA₀ hc₀
    obtain ⟨A', hA', hA'conj⟩ := exists_isConjPlace_of_kConj (K := K) hTconj A₀ hA₀ B hc₀
    exact hnotS A' hA' hA'conj
  -- hence `B` is not `Λ`-split …
  have hnotsplit : ¬ SSGRoute.IsSplitIn k Λ B := hT''noSplit B hB ⟨A, hA, hc⟩ hnotT
  -- … which contradicts `hyS`
  exact hne (hy₁.hyS B hB hnotS hnotsplit σ hσK hσI)

/-- **The chase's hypotheses are inconsistent with a ramified datum.**  Under the hypotheses of
`Work.SSGRoute.ZConstruction.auxDatum_orthogonalToDual`, `y₁` cannot be ramified outside `cs(S)`;
in particular the honest chase is never applicable in the ramified case of
`Work.SSGRoute.z_data_general_of_ramified`. -/
theorem not_ramified_outside_cs_of_chase_hypotheses
    {K Λ N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S T T'' : Finset (ValuationSubring Ω)}
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hT''ram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      SSGRoute.IsRamifiedIn k N B → ∃ A ∈ T'', KConj K A B)
    (hT''noSplit : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ T'', KConj K A B) → (∀ A ∈ T, ¬ KConj K A B) → ¬ SSGRoute.IsSplitIn k Λ B)
    {y₁ : (Ω ≃ₐ[k] Ω) → ZMod p} (hy₁ : ZHyp (p := p) K Λ S y₁)
    (hlev : ∀ g ∈ N.fixingSubgroup, y₁ g = 0) :
    ¬ (∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y₁ σ ≠ 0) := by
  rintro ⟨B, hB, hnotS, σ, hσK, hσI, hne⟩
  exact hne (unramified_outside_cs_of_chase_hypotheses hTconj hT''ram hT''noSplit hy₁ hlev
    B hB hnotS σ hσK hσI)

/-- **Confinement of a cochain vanishing above a level**: a cochain on `G_k` which vanishes on the
Galois group of `N` is unramified at every finite place outside the level-`k` conjugacy classes of a
place set `S'` which covers (up to conjugacy) the places ramified in `N`.

This is the structural fact on which the whole auxiliary-class design of §4 rests: a `z`-data witness
`z₀` produced at the pair `(Λ, S)` with a level `N₀` (i.e. `z₀ = 0` on `G_{N₀}`) has its ramification
*confined* to `cs(S')` as soon as `S'` covers `Ram(N₀|k)`, so that at a place `B ∉ cs(S')` the first
summand of the level step contributes nothing to the inertia — which is the case `(b2)` of
`Work.SSGRoute.hasZData_sum_of_level_data` and the place-set argument of Schmidt--Wingberg, p. 19. -/
theorem isUnramifiedOutside_of_vanishes_on_level
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {N : IntermediateField k Ω} {E : Type} [AddCommGroup E]
    {z : (Ω ≃ₐ[k] Ω) → E}
    (hlev : ∀ g ∈ N.fixingSubgroup, z g = 0)
    {S' : Finset (ValuationSubring Ω)}
    (hram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k N B →
      ∃ A ∈ S', SSGRoute.IsConjPlace k A B) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → z σ = 0 := by
  intro B hB hnot σ hσI
  by_contra hne
  have hσN : σ ∉ N.fixingSubgroup := fun hσN => hne (hlev σ hσN)
  obtain ⟨A, hA, hconj⟩ := hram B hB ⟨σ, hσI, hσN⟩
  exact hnot A hA hconj

end Work.SSGRoute.ZConstruction

