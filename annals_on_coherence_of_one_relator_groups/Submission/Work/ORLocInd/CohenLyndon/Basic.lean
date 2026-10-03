/-
# The Cohen--Lyndon basis theorem: the statement and its two forms

Let `G` be a group and `r ∈ G`, and let `N := Subgroup.normalClosure ({r} : Set G)` be the normal
closure of `r`.

The **Cohen--Lyndon theorem** (Cohen--Lyndon 1963; Karrass--Solitar 1972; see Putnam, *One-relator
groups*, Theorem 6.1) says: for a *free* group `G` and `r ≠ 1` not a proper power, the conjugates
`t * r * t⁻¹` of `r` by a transversal `T` of the cosets of `N` form a free basis of `N`.

This file records that statement in two equivalent forms and proves the equivalence:

* `Work.CohenLyndon.CohenLyndon r` -- the "transversal" (or "Λ-set") form: a set `T` meeting every
  coset of `N` exactly once, together with an isomorphism `FreeGroup T ≃* N` sending the generator
  `t` to the conjugate `t r t⁻¹`;
* `Work.CohenLyndon.CohenLyndonIso r` -- the "quotient" form: an isomorphism
  `FreeGroup (G ⧸ N) ≃* N` sending the generator `q` to a conjugate `s r s⁻¹` where `s` is an
  element of `G` with `QuotientGroup.mk s = q`.  This is the form in which the theorem is consumed
  by `Submission/Work/ORLocInd/FKSKernel/cohenLyndonBasis.lean`.
-/
import Mathlib

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.CohenLyndon

variable {G : Type u} [Group G]

/-- **The Cohen--Lyndon basis theorem, transversal form.**  There is a transversal `T` of the
cosets of the normal closure `N` of `r` such that the conjugates `t * r * t⁻¹` (`t ∈ T`) form a
free basis of `N`. -/
def CohenLyndon (r : G) : Prop :=
  ∃ T : Set G,
    (∀ g : G,
      ∃! t : G, t ∈ T ∧
        QuotientGroup.mk t = (QuotientGroup.mk g : G ⧸ Subgroup.normalClosure ({r} : Set G))) ∧
    ∃ e : FreeGroup T ≃* ↥(Subgroup.normalClosure ({r} : Set G)),
      ∀ t : T,
        ((e (FreeGroup.of t) : ↥(Subgroup.normalClosure ({r} : Set G))) : G) = (t : G) * r * (t : G)⁻¹

/-- **The Cohen--Lyndon basis theorem, quotient form.**  There is an isomorphism
`FreeGroup (G ⧸ N) ≃* N` (`N` the normal closure of `r`) sending each generator `q` to a conjugate
`s * r * s⁻¹` of `r` with `QuotientGroup.mk s = q`. -/
def CohenLyndonIso (r : G) : Prop :=
  ∃ e : FreeGroup (G ⧸ Subgroup.normalClosure ({r} : Set G)) ≃*
      ↥(Subgroup.normalClosure ({r} : Set G)),
    ∀ q : G ⧸ Subgroup.normalClosure ({r} : Set G),
      ∃ s : G,
        QuotientGroup.mk (s := Subgroup.normalClosure ({r} : Set G)) s = q ∧
        ((e (FreeGroup.of q) : ↥(Subgroup.normalClosure ({r} : Set G))) : G) = s * r * s⁻¹

theorem cohenLyndon_iso {r : G} (h : CohenLyndon r) : CohenLyndonIso r := by
  obtain ⟨T, hT, e, he⟩ := h
  classical
  let φ : T → G ⧸ Subgroup.normalClosure ({r} : Set G) := fun t => QuotientGroup.mk (t : G)
  have hφinj : Function.Injective φ := by
    intro t₁ t₂ h12
    exact Subtype.ext ((hT (t₁ : G)).unique ⟨t₁.2, rfl⟩ ⟨t₂.2, h12.symm⟩)
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨(hT g).choose, (hT g).choose_spec.1.1⟩, (hT g).choose_spec.1.2⟩
  let Φ : T ≃ G ⧸ Subgroup.normalClosure ({r} : Set G) := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hΦ : ∀ t : T, Φ t = QuotientGroup.mk (t : G) := fun t => rfl
  refine ⟨(FreeGroup.freeGroupCongr Φ.symm).trans e, ?_⟩
  intro q
  refine ⟨((Φ.symm q : T) : G), ?_, ?_⟩
  · show QuotientGroup.mk ((Φ.symm q : T) : G) = q
    rw [← hΦ (Φ.symm q)]
    exact Φ.apply_symm_apply q
  · have hcongr : FreeGroup.freeGroupCongr Φ.symm (FreeGroup.of q) = FreeGroup.of (Φ.symm q) :=
      FreeGroup.map.of
    have hval : (((FreeGroup.freeGroupCongr Φ.symm).trans e) (FreeGroup.of q) :
        ↥(Subgroup.normalClosure ({r} : Set G))) = e (FreeGroup.of (Φ.symm q)) := by
      rw [MulEquiv.trans_apply, hcongr]
    rw [hval]
    exact he (Φ.symm q)

theorem cohenLyndon_of_iso {r : G} (h : CohenLyndonIso r) : CohenLyndon r := by
  obtain ⟨e, he⟩ := h
  classical
  choose s hs hconj using he
  -- `Ψ : Set.range s ≃ G ⧸ N`
  let Ψ : Set.range s ≃ G ⧸ Subgroup.normalClosure ({r} : Set G) :=
    { toFun := fun t => QuotientGroup.mk (t : G)
      invFun := fun q => ⟨s q, q, rfl⟩
      left_inv := by
        rintro ⟨t, ⟨q, rfl⟩⟩
        refine Subtype.ext ?_
        show s (QuotientGroup.mk (s q)) = s q
        exact congrArg s (hs q)
      right_inv := fun q => hs q }
  refine ⟨Set.range s, ?_, ?_⟩
  · intro g
    refine ⟨s (QuotientGroup.mk g), ⟨⟨QuotientGroup.mk g, rfl⟩, ?_⟩, ?_⟩
    · show QuotientGroup.mk (s (QuotientGroup.mk g)) = QuotientGroup.mk g
      exact hs (QuotientGroup.mk g)
    · rintro y ⟨⟨q, rfl⟩, hy⟩
      show s q = s (QuotientGroup.mk g)
      have hq : QuotientGroup.mk (s q) = QuotientGroup.mk (g : G) := hy
      rw [← hs q, ← hq]
  · refine ⟨(FreeGroup.freeGroupCongr Ψ).trans e, ?_⟩
    intro t
    have hcongr : FreeGroup.freeGroupCongr Ψ (FreeGroup.of t) = FreeGroup.of (Ψ t) :=
      FreeGroup.map.of
    have hval : (((FreeGroup.freeGroupCongr Ψ).trans e) (FreeGroup.of t) :
        ↥(Subgroup.normalClosure ({r} : Set G))) = e (FreeGroup.of (Ψ t)) := by
      rw [MulEquiv.trans_apply, hcongr]
    rw [hval]
    have hst : s (Ψ t) = (t : G) := by
      obtain ⟨t, ⟨q, rfl⟩⟩ := t
      show s (QuotientGroup.mk (s q)) = s q
      exact congrArg s (hs q)
    rw [← hst]
    exact hconj (Ψ t)

theorem cohenLyndon_iff_isoForm {r : G} : CohenLyndon r ↔ CohenLyndonIso r :=
  ⟨cohenLyndon_iso, cohenLyndon_of_iso⟩

end Work.CohenLyndon
