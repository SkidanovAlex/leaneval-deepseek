import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `z`-data calculus of Schmidt--Wingberg Theorem 13

`Work.SSGRoute.shafarevich_z_construction` is proved from the existence of a cochain `z`
satisfying the six properties of Schmidt--Wingberg's Theorem 13 (§4): additivity and local
constancy on `G_K = K.fixingSubgroup`, agreement with `y` on the decomposition groups of the
places conjugate to `S`, vanishing on the involutions, vanishing on the inertia of the places
outside `cs(S)` that do not split in `Λ`, and the sharpened condition (b) at the places outside
`cs(S)` that *do* split in `Λ` (Schmidt--Wingberg's `z_P` cyclic and `z^σ_P = 0` for `σ ≠ 1`).

This file packages those six properties as the predicate `Work.SSGRoute.HasZData` and proves the
structural lemmas used by the induction of Schmidt--Wingberg (§4, pp. 18--19), which assembles the
answer for a general coefficient module `E` from answers for the components of a decomposition
`E = E₀ ⊕ μ_p`:

* `Work.SSGRoute.hasZData_add` -- the `z`-data is closed under addition.  The two hypotheses are
  exactly the two facts the paper verifies separately for the summands: **disjointness** of the
  ramification at a good place (so that at a place where the sum is ramified only one summand
  contributes, and its local group, being that of a one-dimensional coefficient module, is cyclic)
  and the **vanishing at the conjugates** of the good places.  This is the paper's "it is now easily
  verified that the class `z = z⁰ + inf z⁰⁰` satisfies conditions (a) and (b)";
* `Work.SSGRoute.kills_decomp_of_split_of_vanishes` -- the **level change**: a cochain vanishing on
  the Galois group `G_L` of an intermediate field `L ⊇ K` kills the local group of every place
  splitting completely in `L`.  In the paper this is the mechanism by which the primes of
  `T'(K) ∖ T(K)` receive no contribution from `z⁰` (they split completely in the Galois closure
  `K̃` of the field cut out by `z⁰`), which is the disjointness hypothesis above;
* `Work.SSGRoute.zadd_conj` -- **conjugation triviality**: for an additive cochain on `G_K` with
  abelian coefficients, conjugating by an element of `G_K` does not change values.  Consequently the
  sharpened condition (b) has to be checked at only one place per prime of `K` over a given prime
  of `k`: the conditions at the `G_K`-conjugate places are automatically equivalent.  (This is why
  the statement of (b) with "every conjugate `Q` that is not `G_K`-conjugate to `B`" is the paper's
  `z^σ_P = 0` for `σ ∈ G(K|k) ∖ {1}` and no more.)
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {E : Type} [AddCommGroup E]

section Basics

/-- For an additive cochain on `G_K`, the value at `1` is zero. -/
lemma zadd_one {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) :
    z 1 = 0 := by
  have h := hzadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
  rw [mul_one] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

/-- For an additive cochain on `G_K`, the value at an inverse is the negative. -/
lemma zadd_inv {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup) : z g⁻¹ = -z g := by
  have h := hzadd g hg g⁻¹ (K.fixingSubgroup.inv_mem hg)
  rw [mul_inv_cancel] at h
  have h2 : z g + z g⁻¹ = 0 := by rw [← h, zadd_one hzadd]
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h2)

/-- **Conjugation triviality.**  For an additive cochain on `G_K` with abelian coefficients,
conjugation by an element of `G_K` does not change the values.  Hence the sharpened condition (b),
which requires the vanishing of `z` on the local group of *every* conjugate `Q` of a good place `B`
that is not `G_K`-conjugate to `B`, is a condition at one place per prime of `K` over a given prime
of `k`. -/
theorem zadd_conj {K : IntermediateField k Ω} {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {τ u : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup) (hu : u ∈ K.fixingSubgroup) :
    z (τ * u * τ⁻¹) = z u := by
  have hτu : τ * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hτ hu
  have h1 : z (τ * u * τ⁻¹) = z (τ * u) + z τ⁻¹ :=
    hzadd (τ * u) hτu τ⁻¹ (K.fixingSubgroup.inv_mem hτ)
  rw [h1, hzadd τ hτ u hu, zadd_inv hzadd hτ]
  abel

/-- **Level change.**  A cochain vanishing on the Galois group of an intermediate field `L ⊇ K`
kills the local group (intersected with `G_K`) of every place that splits completely in `L`.  In
Schmidt--Wingberg's induction this is the reason why the field cut out by the class `z⁰` (whose
Galois group contains `G_{K̃}`, `K̃` the Galois closure of the cut-out field) contributes nothing at
the new primes of the second summand, which are chosen to split completely in `K̃`. -/
theorem kills_decomp_of_split_of_vanishes {K L : IntermediateField k Ω}
    {z : (Ω ≃ₐ[k] Ω) → E} (hz : ∀ g ∈ L.fixingSubgroup, z g = 0)
    {B : ValuationSubring Ω} (hsplit : SSGRoute.IsSplitIn k L B) :
    ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z τ = 0 := by
  intro τ hτ
  exact hz τ (hsplit (Subgroup.mem_inf.mp hτ).1)

end Basics

/-! ## The `z`-data -/

/-- A finite place `B` of `Ω` is a **good place** for the pair `(Λ, S)`: it lies over a prime of `k`
outside the conjugates of `S` and splits completely in `Λ`.  These are exactly the places at which
the sharpened condition (b) of the `z`-data is triggered. -/
def IsGoodPlace (Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (B : ValuationSubring Ω) : Prop :=
  SSGRoute.IsFinPlace k B ∧ (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
    SSGRoute.IsSplitIn k Λ B

/-- **The `z`-data of Schmidt--Wingberg Theorem 13, relative to a cochain `y`.**  The six
properties that the auxiliary class `z` has to satisfy; only its values on
`K.fixingSubgroup` occur. -/
def HasZData (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (y z : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
  SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
  (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
  (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
    (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
    (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        z δ ∈ AddSubgroup.zmultiples (z g)) ∧
    (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0))

/-- **The `z`-data is closed under addition** (Schmidt--Wingberg §4, the final verification of the
induction on `dim_{𝔽_p} E`).

The hypotheses are exactly the two facts verified separately for the summands in the paper:

* **disjointness** at a good place: if the sum is ramified at `B`, then one of the summands vanishes
  identically on the local group of `B`; then the local group of the sum at `B` is the local group
  of the *other* summand, and the cyclicity clause for the sum follows from the cyclicity clause for
  that summand;
* **vanishing at the conjugates**: both summands kill the local group of every conjugate `Q` of `B`
  that is not `G_K`-conjugate to `B`. -/
theorem hasZData_add {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E} (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hdisj : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        (z₀ σ ≠ 0 ∨ z₁ σ ≠ 0)) →
      ((∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₀ τ = 0) ∨
       (∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₁ τ = 0)))
    (hconj : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
        (z₀ σ ≠ 0 ∨ z₁ σ ≠ 0)) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₀ τ = 0 ∧ z₁ τ = 0) :
    HasZData K Λ S (y₀ + y₁) (z₀ + z₁) := by
  obtain ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ := h₀
  obtain ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ := h₁
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    simp only [Pi.add_apply]
    rw [ha₀ g hg h hh, ha₁ g hg h hh]
    abel
  · obtain ⟨U₀, hU₀o, hU₀⟩ := hl₀
    obtain ⟨U₁, hU₁o, hU₁⟩ := hl₁
    refine ⟨U₀ ⊓ U₁, hU₀o.inter hU₁o, ?_⟩
    intro g hg u hu huH
    obtain ⟨hu₀, hu₁⟩ := Subgroup.mem_inf.mp hu
    simp only [Pi.add_apply]
    rw [hU₀ g hg u hu₀ huH, hU₁ g hg u hu₁ huH]
  · intro B hB hconjB σ hσK hσd
    simp only [Pi.add_apply]
    rw [hg₀ B hB hconjB σ hσK hσd, hg₁ B hB hconjB σ hσK hσd]
  · intro c hc hc2
    simp only [Pi.add_apply]
    rw [hi₀ c hc hc2, hi₁ c hc hc2, add_zero]
  · intro B hB hnot hsp σ hσK hσI
    simp only [Pi.add_apply]
    rw [hs₀ B hB hnot hsp σ hσK hσI, hs₁ B hB hnot hsp σ hσK hσI, add_zero]
  · intro B hB hnot hsp htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    have hzne : z₀ σ ≠ 0 ∨ z₁ σ ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hσne (by simp only [Pi.add_apply]; rw [hc.1, hc.2, add_zero])
    have hgood : IsGoodPlace Λ S B := ⟨hB, hnot, hsp⟩
    have hram : ∃ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧
        (z₀ s ≠ 0 ∨ z₁ s ≠ 0) := ⟨σ, hσI, hσK, hzne⟩
    have hσmem : σ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩
    refine ⟨?_, ?_⟩
    · rcases hdisj B hgood hram with hz₀ | hz₁
      · -- the first summand is locally zero, so the second one carries the local group
        have hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
            SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0 := by
          refine ⟨σ, hσI, hσK, ?_⟩
          rcases hzne with h | h
          · exact absurd (hz₀ σ hσmem) h
          · exact h
        obtain ⟨g, hg, hgc⟩ := (hb₁ B hB hnot hsp hram₁).1
        refine ⟨g, hg, fun δ hδ => ?_⟩
        have h1 : z₀ g = 0 := hz₀ g hg
        have h2 : z₀ δ = 0 := hz₀ δ hδ
        have h3 : z₁ δ ∈ AddSubgroup.zmultiples (z₁ g) := hgc δ hδ
        simp only [Pi.add_apply]
        simpa only [h1, h2, zero_add] using h3
      · have hram₀ : ∃ s : Ω ≃ₐ[k] Ω,
            SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₀ s ≠ 0 := by
          refine ⟨σ, hσI, hσK, ?_⟩
          rcases hzne with h | h
          · exact h
          · exact absurd (hz₁ σ hσmem) h
        obtain ⟨g, hg, hgc⟩ := (hb₀ B hB hnot hsp hram₀).1
        refine ⟨g, hg, fun δ hδ => ?_⟩
        have h1 : z₁ g = 0 := hz₁ g hg
        have h2 : z₁ δ = 0 := hz₁ δ hδ
        have h3 : z₀ δ ∈ AddSubgroup.zmultiples (z₀ g) := hgc δ hδ
        simp only [Pi.add_apply]
        simpa only [h1, h2, add_zero] using h3
    · intro Q hQ hnconj τ hτ
      obtain ⟨hτ₀, hτ₁⟩ := hconj B hgood hram Q hQ hnconj τ hτ
      simp only [Pi.add_apply]
      rw [hτ₀, hτ₁, add_zero]

/-- **The induction step of Schmidt--Wingberg §4, with the two mechanisms made explicit.**

This replaces the two abstract hypotheses of `hasZData_add` by the two facts that the paper's §4
construction supplies for the two summands:

* `hz₀` -- the class `z₀` (the induction-hypothesis part, with a coefficient module of smaller
  dimension) **vanishes on the Galois group of a level `L'`**;
* `hconf` -- every good place at which `z₁` (the one-dimensional part) is **ramified splits
  completely, together with all its conjugates, in `L'`**.  Then the level change
  `kills_decomp_of_split_of_vanishes` shows that `z₀` kills the local group of the place and of all
  its conjugates, which is the disjointness needed at the new primes of `z₁`;
* `hkill` -- `z₁` **vanishes on the local groups of the conjugates** of every good place at which
  `z₀` is ramified (in the paper: the auxiliary class `ỹ` is prescribed to vanish at `T'(K) ∖ T(K)`,
  the places over the ramification of `z⁰`).

With these, `z₀ + z₁` satisfies the `z`-data for `y₀ + y₁`. -/
theorem hasZData_add_of_split_confined {K Λ L' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E}
    (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hz₀ : ∀ g ∈ L'.fixingSubgroup, z₀ g = 0)
    (hconf : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₁ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q → SSGRoute.IsSplitIn k L' Q)
    (hkill : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₀ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₁ τ = 0) :
    HasZData K Λ S (y₀ + y₁) (z₀ + z₁) := by
  obtain ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ := h₀
  obtain ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ := h₁
  have hlev : ∀ B : ValuationSubring Ω, SSGRoute.IsSplitIn k L' B →
      ∀ τ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z₀ τ = 0 :=
    fun B hB => kills_decomp_of_split_of_vanishes hz₀ hB
  refine hasZData_add ⟨ha₀, hl₀, hg₀, hi₀, hs₀, hb₀⟩ ⟨ha₁, hl₁, hg₁, hi₁, hs₁, hb₁⟩ ?_ ?_
  · -- disjointness of the ramification at a good place
    intro B hgood hram
    obtain ⟨σ, hσI, hσK, hzne⟩ := hram
    by_cases hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0
    · exact Or.inl (hlev B (hconf B hgood hram₁ B (isConjPlace_refl B)))
    · have hz₁ : ∀ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s → s ∈ K.fixingSubgroup →
          z₁ s = 0 := fun s hIs hm => by
        by_contra hne
        exact hram₁ ⟨s, hIs, hm, hne⟩
      refine Or.inr (hkill B hgood ?_ B (isConjPlace_refl B))
      rcases hzne with h | h
      · exact ⟨σ, hσI, hσK, h⟩
      · exact absurd (hz₁ σ hσI hσK) h
  · -- vanishing on the conjugates that are not `G_K`-conjugates
    intro B hgood hram Q hQ hnconj τ hτ
    obtain ⟨σ, hσI, hσK, hzne⟩ := hram
    by_cases hram₁ : ∃ s : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₁ s ≠ 0
    · -- `z₀` dies at `Q` by the level change, since `Q` is a conjugate of `B`
      refine ⟨hlev Q (hconf B hgood hram₁ Q hQ) τ hτ,
        (hb₁ B hgood.1 hgood.2.1 hgood.2.2 hram₁).2 Q hQ hnconj τ hτ⟩
    · have hz₁ : ∀ s : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B s → s ∈ K.fixingSubgroup →
          z₁ s = 0 := fun s hIs hm => by
        by_contra hne
        exact hram₁ ⟨s, hIs, hm, hne⟩
      have hram₀ : ∃ s : Ω ≃ₐ[k] Ω,
          SSGRoute.IsInertia k B s ∧ s ∈ K.fixingSubgroup ∧ z₀ s ≠ 0 := by
        rcases hzne with h | h
        · exact ⟨σ, hσI, hσK, h⟩
        · exact absurd (hz₁ σ hσI hσK) h
      exact ⟨(hb₀ B hgood.1 hgood.2.1 hgood.2.2 hram₀).2 Q hQ hnconj τ hτ,
        hkill B hgood hram₀ Q hQ τ hτ⟩

/-- **Change of coefficients along an injective additive map.**  All six clauses of the `z`-data are
equalities between values of the two cochains or vanishings of one of them, so they are preserved
(and reflected) by an injective additive map.  This is how the induction of Schmidt--Wingberg passes
from the submodule `ker π` of `E` back to `E`, and how the stated `z`-data for a subquotient is
transported to the ambient module. -/
theorem hasZData_map {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) {K Λ : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → A} {z : (Ω ≃ₐ[k] Ω) → A}
    (h : HasZData K Λ S y z) :
    HasZData K Λ S (fun σ => f (y σ)) (fun σ => f (z σ)) := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg' h hh'
    show f (z (g * h)) = f (z g) + f (z h)
    rw [ha g hg' h hh', map_add]
  · obtain ⟨U, hUo, hU⟩ := hl
    refine ⟨U, hUo, ?_⟩
    intro g hg' u hu huK
    show f (z (g * u)) = f (z g)
    rw [hU g hg' u hu huK]
  · intro B hB hc σ hσK hσd
    show f (z σ) = f (y σ)
    rw [hg B hB hc σ hσK hσd]
  · intro c hc hc2
    show f (z c) = 0
    rw [hi c hc hc2, map_zero]
  · intro B hB hn hs' σ hσK hσI
    show f (z σ) = 0
    rw [hs B hB hn hs' σ hσK hσI, map_zero]
  · intro B hB hn hs' htrig
    have htrig' : ∃ σ : Ω ≃ₐ[k] Ω,
        SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0 := by
      obtain ⟨σ, hI, hK, hne⟩ := htrig
      exact ⟨σ, hI, hK, fun h0 => hne (by show f (z σ) = 0; rw [h0, map_zero])⟩
    obtain ⟨hcyc, hvan⟩ := hb B hB hn hs' htrig'
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg', hgc⟩ := hcyc
      refine ⟨g, hg', fun δ hδ => ?_⟩
      show f (z δ) ∈ AddSubgroup.zmultiples (f (z g))
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgc δ hδ)
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, by rw [← hm, map_zsmul]⟩
    · intro Q hQ hn' τ hτ
      show f (z τ) = 0
      rw [hvan Q hQ hn' τ hτ, map_zero]

/-- The `z`-data only depends on the cochain `y` through its pointwise values (only the agreement
clause mentions `y`).  This lets one replace `y₀ + y₁` by the given cochain `y` at the end of the
induction step. -/
theorem hasZData_congr {K Λ : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {y y' z : (Ω ≃ₐ[k] Ω) → E} (h : ∀ σ, y' σ = y σ) (hz : HasZData K Λ S y' z) :
    HasZData K Λ S y z := by
  obtain ⟨ha, hl, hg, hi, hs, hb⟩ := hz
  refine ⟨ha, hl, ?_, hi, hs, hb⟩
  intro B hB hc σ hσK hσd
  rw [← h σ]
  exact hg B hB hc σ hσK hσd

/-- **The induction step with the coefficient module decomposed componentwise.**

This is the shape in which the induction on `dim_{𝔽_p} E` of Schmidt--Wingberg §4 is assembled.
Given a decomposition `y = y₀ + y₁` of the given cochain (in the paper: `E = E₀ ⊕ μ_p`, `y₀` the
`E₀`-component obtained from the induction hypothesis, `y₁ = π ∘ y` the one-dimensional part), a
`z`-data witness `z₀` for `y₀` (the induction hypothesis), a level `L'` on whose Galois group `z₀`
vanishes (the Galois closure of the field cut out by `z₀`), and a `z`-data witness `z₁` for `y₁`
whose ramification at good places is confined to places split completely in `L'` and which kills the
local groups of the conjugates of the good places where `z₀` is ramified (the auxiliary class `ỹ`),
the sum `z₀ + z₁` satisfies the `z`-data for `y`. -/
theorem hasZData_of_component_data {K Λ L' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {y y₀ y₁ z₀ z₁ : (Ω ≃ₐ[k] Ω) → E}
    (hy : ∀ σ, y₀ σ + y₁ σ = y σ)
    (h₀ : HasZData K Λ S y₀ z₀) (h₁ : HasZData K Λ S y₁ z₁)
    (hz₀ : ∀ g ∈ L'.fixingSubgroup, z₀ g = 0)
    (hconf : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₁ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q → SSGRoute.IsSplitIn k L' Q)
    (hkill : ∀ B : ValuationSubring Ω, IsGoodPlace Λ S B →
      (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z₀ σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z₁ τ = 0) :
    HasZData K Λ S y (z₀ + z₁) :=
  hasZData_congr (fun σ => by rw [Pi.add_apply, hy σ])
    (hasZData_add_of_split_confined h₀ h₁ hz₀ hconf hkill)

end Work.SSGRoute
