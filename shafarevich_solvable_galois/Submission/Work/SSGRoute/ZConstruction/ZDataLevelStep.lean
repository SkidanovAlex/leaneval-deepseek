import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The induction step of Schmidt--Wingberg §4 (pp. 18--19), correctly wired

`Work.SSGRoute.HasZData` packages the six clauses of the auxiliary class `z` of Schmidt--Wingberg's
Theorem 13.  The *induction step* on `dim_{𝔽_p} E` of the paper (pp. 18--19) splits the cochain
`y = y₀ + y₁` according to a decomposition `E = E₀ ⊕ μ_p` of the coefficient module, applies the
induction hypothesis to `y₀` at the given pair `(Λ, S)` and the *one-dimensional* case to an
auxiliary class `yAux` at the **enlarged pair** `(N, S')`, where

* `N = K̃` is the Galois closure over `k` of the field `K⁰` cut out by the class `z₀` produced by the
  induction hypothesis (in the formalisation: any finite Galois intermediate field `N ⊇ K` with
  `z₀ = 0` on `G_N`, supplied by `Work.SSGRoute.exists_fixingField_vanishing_finite`), and
* `S' = S ∪ {places over Ram(N|k)}` is the enlargement of the place set that the paper's `T'` is;
  its defining property, used below, is that every place ramified in `N` is conjugate to one of its
  elements.

The class `yAux` is the one the paper obtains by the Poitou--Tate diagram chase of p. 19: it agrees with
`y₁` on the decomposition groups of the places of `cs(S)` and *vanishes* on the local groups of the
places of `cs(S') ∖ cs(S)`, i.e. of the places over the ramification of `N`.

This file proves the assembly — the paper's "it is now easily verified that the class
`z = z⁰ + inf z⁰⁰` satisfies (a) and (b)" — in the form needed by the induction:

  `Work.SSGRoute.hasZData_sum_of_level_data`:
  `HasZData K Λ S y₀ z₀ →` (level `N` with `z₀ = 0` on `G_N`) `→ HasZData K N S' yAux z₁ →`
  (agreement and vanishing of `yAux`) `→ HasZData K Λ S y (z₀ + z₁)`.

The verification is the case analysis of the paper:

* at a place of `cs(S')` the summand `z₁` is pinned to `yAux` (clause 3 of its data) and `yAux` is
  prescribed (`hagree`/`hvanish`), while `z₀` contributes the paper's (b') at the places of
  `S' ∖ S` — this is `Case (a)` below;
* at a place `B ∉ cs(S')` that splits completely in `N`, the summand `z₀` vanishes on the local
  group of `B` (the level change `kills_decomp_of_split_of_vanishes`), so the sum is `z₁` there and
  its data applies — `Case (b1)`;
* at a place `B ∉ cs(S')` that does not split in `N`, both summands kill the inertia: `z₁` by
  clause 5 of its data, `z₀` because a place ramified in `N` lies in `cs(S')`
  (`mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn`) — `Case (b2)`, where the clause is
  vacuous.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {E : Type} [AddCommGroup E]

/-- Conjugation preserves the property of being a finite place, in the `IsConjPlace` form. -/
theorem isFinPlace_of_isConjPlace {B Q : ValuationSubring Ω} (hB : SSGRoute.IsFinPlace k B)
    (h : SSGRoute.IsConjPlace k B Q) : SSGRoute.IsFinPlace k Q := by
  obtain ⟨σ, rfl⟩ := h
  rwa [isFinPlace_smul_iff]

/-- `cs(S)` is conjugation-invariant: a conjugate of a place conjugate into `S` is conjugate into
`S`.  (Stated for a `Finset` of representatives.) -/
theorem exists_conj_of_conj {S : Finset (ValuationSubring Ω)} {B Q : ValuationSubring Ω}
    (hBQ : SSGRoute.IsConjPlace k B Q)
    (h : ∃ A ∈ S, SSGRoute.IsConjPlace k A B) : ∃ A ∈ S, SSGRoute.IsConjPlace k A Q := by
  obtain ⟨A, hA, hAB⟩ := h
  exact ⟨A, hA, SSGRoute.isConjPlace_trans hAB hBQ⟩

/-- The complement of `cs(S)` is conjugation-invariant. -/
theorem forall_not_conj_of_conj {S : Finset (ValuationSubring Ω)} {B Q : ValuationSubring Ω}
    (hBQ : SSGRoute.IsConjPlace k B Q)
    (h : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A Q := by
  intro A hA hAQ
  exact h A hA (SSGRoute.isConjPlace_trans hAQ (SSGRoute.isConjPlace_symm hBQ))

/-- **The induction step of Schmidt--Wingberg §4 (pp. 18--19).**

Let `y = y₀ + y₁` be a decomposition of the given cochain, `z₀` a `z`-data witness for `y₀` relative
to `(Λ, S)` that vanishes on the Galois group of the finite level `N ⊇ Λ`, and `z₁` a `z`-data
witness for the auxiliary class `yAux` relative to the enlarged pair `(N, S')`.  Assume

* `cs(S) ⊆ cs(S')` (so clause 3 of the data of `z₁` applies at the places of `S`),
* every place ramified in `N` is conjugate into `S'` (the defining property of `S' = S ∪ Ram(N|k)`),
* `yAux` agrees with `y₁` on the decomposition groups of the places of `cs(S)`, and vanishes on the
  local groups of the places of `cs(S') ∖ cs(S)`.

Then `z₀ + z₁` has the `z`-data for `y` relative to the *original* pair `(Λ, S)`. -/
theorem hasZData_sum_of_level_data
    {K Λ N : IntermediateField k Ω} {S S' : Finset (ValuationSubring Ω)}
    {y y₀ y₁ yAux z₀ z₁ : (Ω ≃ₐ[k] Ω) → E}
    (hNnorm : (N.fixingSubgroup).Normal) (hΛN : Λ ≤ N)
    (hSS' : ∀ B : ValuationSubring Ω, (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∃ A' ∈ S', SSGRoute.IsConjPlace k A' B)
    (hramS' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      SSGRoute.IsRamifiedIn k N B → ∃ A ∈ S', SSGRoute.IsConjPlace k A B)
    (hy : ∀ σ, y₀ σ + y₁ σ = y σ)
    (h₀ : HasZData K Λ S y₀ z₀) (hlev : ∀ g ∈ N.fixingSubgroup, z₀ g = 0)
    (h₁ : HasZData K N S' yAux z₁)
    (hagree : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = y₁ σ)
    (hvanish : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, yAux σ = 0) :
    HasZData K Λ S y (z₀ + z₁) := by
  classical
  obtain ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ := h₀
  obtain ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ := h₁
  -- `K ≤ Λ ≤ N`, so `G_N ≤ G_Λ ≤ G_K`
  have hle : N.fixingSubgroup ≤ Λ.fixingSubgroup := IntermediateField.fixingSubgroup_le hΛN
  -- `z₁` vanishes on the local group of a place of `cs(S')` outside `cs(S)`
  have hz₁_of_S' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      (∃ A ∈ S', SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₁ σ = 0 := by
    intro B hB hnot hS' σ hσ
    rw [hg₁ B hB hS' σ (Subgroup.mem_inf.mp hσ).2 (Subgroup.mem_inf.mp hσ).1,
      hvanish B hB hnot hS' σ hσ]
  -- `z₀` kills the local group of a place that splits completely in `N`
  have hz₀_of_split : ∀ B : ValuationSubring Ω, SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₀ σ = 0 :=
    fun B hB => kills_decomp_of_split_of_vanishes hlev hB
  -- `z₀` kills the inertia of a place that is unramified in `N`
  have hz₀_of_unram : ∀ B : ValuationSubring Ω, ¬ SSGRoute.IsRamifiedIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z₀ σ = 0 :=
    fun B hnr σ _ hσI => hlev σ (mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn N B hnr σ hσI)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 1: additivity
    intro g hg h hh
    simp only [Pi.add_apply]
    rw [ha₀ g hg h hh, ha₁ g hg h hh]
    abel
  · -- clause 2: local constancy
    obtain ⟨U₀, hU₀, hc₀⟩ := hl₀
    obtain ⟨U₁, hU₁, hc₁⟩ := hl₁
    exact ⟨U₀ ⊓ U₁, hU₀.inter hU₁, fun g hg u hu huK => by
      obtain ⟨hu₀, hu₁⟩ := Subgroup.mem_inf.mp hu
      simp only [Pi.add_apply]
      rw [hc₀ g hg u hu₀ huK, hc₁ g hg u hu₁ huK]⟩
  · -- clause 3: agreement with `y` on `cs(S)`
    intro B hB hconj σ hσK hσd
    obtain ⟨A', hA', hc'⟩ := hSS' B hconj
    simp only [Pi.add_apply]
    rw [hg₀ B hB hconj σ hσK hσd, hg₁ B hB ⟨A', hA', hc'⟩ σ hσK hσd,
      hagree B hB hconj σ (Subgroup.mem_inf.mpr ⟨hσd, hσK⟩)]
    exact hy σ
  · -- clause 4: involutions
    intro c hc hc2
    simp only [Pi.add_apply]
    rw [hi₀ c hc hc2, hi₁ c hc hc2, add_zero]
  · -- clause 5: vanishing on the inertia of the places outside `cs(S)` not split in `Λ`
    intro B hB hnot hnsΛ σ hσK hσI
    have hz₀ : z₀ σ = 0 := hs₀ B hB hnot hnsΛ σ hσK hσI
    have hz₁ : z₁ σ = 0 := by
      by_cases hS' : ∃ A ∈ S', SSGRoute.IsConjPlace k A B
      · exact hz₁_of_S' B hB hnot hS' σ (Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩)
      · have hnotS' : ∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B :=
          fun A hA hc => hS' ⟨A, hA, hc⟩
        have hnsN : ¬ SSGRoute.IsSplitIn k N B :=
          fun hsplit => hnsΛ (le_trans hsplit (IntermediateField.fixingSubgroup_le hΛN))
        exact hs₁ B hB hnotS' hnsN σ hσK hσI
    simp only [Pi.add_apply]
    rw [hz₀, hz₁, add_zero]
  · -- clause 6: the sharpened condition (b)
    intro B hB hnot hspΛ hram
    obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hram
    have hmem₀ : σ₀ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨hσ₀I.1, hσ₀K⟩
    by_cases hS' : ∃ A ∈ S', SSGRoute.IsConjPlace k A B
    · -- ## Case (a): `B` lies over a prime of `T' = S' ∖ S`
      have hz₁B : ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₁ δ = 0 :=
        hz₁_of_S' B hB hnot hS'
      have hz₀ne : z₀ σ₀ ≠ 0 := fun hz => hσ₀ne (by
        simp only [Pi.add_apply]; rw [hz, hz₁B σ₀ hmem₀, add_zero])
      obtain ⟨hcyc₀, hkill₀⟩ := hb₀ B hB hnot hspΛ ⟨σ₀, hσ₀I, hσ₀K, hz₀ne⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨g, hg, hgc⟩ := hcyc₀
        refine ⟨g, hg, fun δ hδ => ?_⟩
        have hg' : (z₀ + z₁) g = z₀ g := by
          simp only [Pi.add_apply]; rw [hz₁B g hg, add_zero]
        have hδ' : (z₀ + z₁) δ = z₀ δ := by
          simp only [Pi.add_apply]; rw [hz₁B δ hδ, add_zero]
        rw [hg', hδ']
        exact hgc δ hδ
      · intro Q hQ hnconj τ hτ
        have hQS' : ∃ A ∈ S', SSGRoute.IsConjPlace k A Q := exists_conj_of_conj hQ hS'
        have hQnot : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A Q := forall_not_conj_of_conj hQ hnot
        have hQfin : SSGRoute.IsFinPlace k Q := isFinPlace_of_isConjPlace hB hQ
        have hz₁τ : z₁ τ = 0 := hz₁_of_S' Q hQfin hQnot hQS' τ hτ
        have hz₀τ : z₀ τ = 0 := hkill₀ Q hQ hnconj τ hτ
        simp only [Pi.add_apply]
        rw [hz₀τ, hz₁τ, add_zero]
    · -- ## Case (b): `B ∉ cs(S')`
      have hnotS' : ∀ A ∈ S', ¬ SSGRoute.IsConjPlace k A B := fun A hA hc => hS' ⟨A, hA, hc⟩
      by_cases hsplitN : SSGRoute.IsSplitIn k N B
      · -- ### Case (b1): `B` splits completely in `N`, so `z₀` dies at `B`
        have hz₀B := hz₀_of_split B hsplitN
        have hz₁ne : z₁ σ₀ ≠ 0 := fun hz => hσ₀ne (by
          simp only [Pi.add_apply]; rw [hz₀B σ₀ hmem₀, hz, zero_add])
        obtain ⟨hcyc₁, hkill₁⟩ := hb₁ B hB hnotS' hsplitN ⟨σ₀, hσ₀I, hσ₀K, hz₁ne⟩
        refine ⟨?_, ?_⟩
        · obtain ⟨g, hg, hgc⟩ := hcyc₁
          refine ⟨g, hg, fun δ hδ => ?_⟩
          have hg' : (z₀ + z₁) g = z₁ g := by
            simp only [Pi.add_apply]; rw [hz₀B g hg, zero_add]
          have hδ' : (z₀ + z₁) δ = z₁ δ := by
            simp only [Pi.add_apply]; rw [hz₀B δ hδ, zero_add]
          rw [hg', hδ']
          exact hgc δ hδ
        · intro Q hQ hnconj τ hτ
          have hQg : SSGRoute.IsConjPlace k B Q := hQ
          obtain ⟨σ, hσ⟩ := hQg
          have hsplitNQ : SSGRoute.IsSplitIn k N Q := by
            rw [← hσ]
            exact (isSplitIn_conj N hNnorm B σ).mpr hsplitN
          have hz₀τ : z₀ τ = 0 := hz₀_of_split Q hsplitNQ τ hτ
          have hz₁τ : z₁ τ = 0 := hkill₁ Q hQ hnconj τ hτ
          simp only [Pi.add_apply]
          rw [hz₀τ, hz₁τ, add_zero]
      · -- ### Case (b2): `B` is ramified in `N`; both summands kill the inertia
        have hnr : ¬ SSGRoute.IsRamifiedIn k N B := fun hr => hS' (hramS' B hB hr)
        have hz₁I : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z₁ σ = 0 :=
          hs₁ B hB hnotS' hsplitN
        exact absurd (by
          simp only [Pi.add_apply]
          rw [hz₀_of_unram B hnr σ₀ hσ₀K hσ₀I, hz₁I σ₀ hσ₀K hσ₀I, add_zero]) hσ₀ne

end Work.SSGRoute
