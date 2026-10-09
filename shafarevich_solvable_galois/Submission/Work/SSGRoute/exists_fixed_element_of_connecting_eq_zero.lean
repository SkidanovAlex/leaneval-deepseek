import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Degree-zero lift along a short exact sequence** — the degree-`0` part of the covariant long
exact sequence of `Ext` groups (Mathlib's `Ext.covariant_sequence_exact₃`).

If the connecting map `Ext X S.X₃ 0 → Ext X S.X₁ 1` (the Yoneda product with the extension class
`hS.extClass`) kills the class `Ext.mk₀ a` of a morphism `a : X ⟶ S.X₃`, then `a` lifts through
the projection `S.g` of the short exact sequence. -/
lemma exists_comp_eq_of_extClass_comp_eq_zero {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X : C} {S : ShortComplex C} (hS : S.ShortExact) {a : X ⟶ S.X₃}
    (h : (Abelian.Ext.mk₀ a).comp hS.extClass (zero_add 1) = 0) :
    ∃ b : X ⟶ S.X₂, b ≫ S.g = a := by
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS (Abelian.Ext.mk₀ a) (zero_add 1) h
  refine ⟨Abelian.Ext.addEquiv₀ x₂, ?_⟩
  apply (Abelian.Ext.mk₀_bijective (X := X) (Y := S.X₃)).1
  rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_addEquiv₀_apply]
  have hzz : (zero_add (0 : ℕ) : (0 : ℕ) + 0 = 0) = (add_zero (0 : ℕ) : (0 : ℕ) + 0 = 0) :=
    Subsingleton.elim _ _
  rw [hzz]
  exact hx₂

/-- **Vanishing of the connecting class produces a fixed generator.** Let `f : G ↠ D` be a
surjection of groups, `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` a short exact sequence of `D`-modules and
`e : S.X₃ ≅ 𝔽_p` a `D`-module isomorphism onto the trivial module. Let `one₃ : ℤ → S.X₃` be the
`G`-map of `ℤ` into the restriction of `S.X₃` determined by an element which `e` sends to `1`, and
assume that its Yoneda product with the extension class of the restricted sequence vanishes. Then
there is a `D`-fixed `m ∈ S.X₂` with `e (S.g m) = 1`. -/
theorem exists_fixed_element_of_connecting_eq_zero (p : ℕ) [Fact p.Prime] {G D : Type}
    [Group G] [Group D] (f : G →* D) (hf : Function.Surjective f)
    (S : ShortComplex (Rep Coeff D)) (hS : S.ShortExact)
    (e : S.X₃ ≅ Rep.trivial Coeff D (ZMod p))
    (one₃ : unitRep G ⟶ Rep.res f S.X₃) (hone : e.hom (one₃ 1) = 1)
    (hzero : (Abelian.Ext.mk₀ one₃).comp ((hS.map_of_exact (Rep.resFunctor f)).extClass)
      (zero_add 1) = 0) :
    ∃ m : S.X₂, (∀ δ : D, S.X₂.ρ δ m = m) ∧ e.hom (S.g m) = 1 := by
  -- Restrict the short exact sequence of `D`-modules to `G`; it stays short exact because
  -- `Rep.resFunctor f` preserves (and reflects) exactness.
  have hS' : (S.map (Rep.resFunctor f)).ShortExact := hS.map_of_exact (Rep.resFunctor f)
  -- Exactness of `Ext(ℤ, -)` in degree `0` turns the vanishing of the connecting class
  -- `mk₀ one₃ ∘ extClass` into a lift of `one₃` through the middle term.
  obtain ⟨b, hb⟩ := exists_comp_eq_of_extClass_comp_eq_zero hS' hzero
  -- `b` is a `G`-map `ℤ → S.X₂`; its value at `1` is the element we are looking for.
  refine ⟨b 1, ?_, ?_⟩
  · -- `b` is `G`-equivariant and `ℤ` is the trivial module, so `b 1` is `G`-fixed; `D`-fixedness
    -- follows from surjectivity of `f`.
    intro δ
    obtain ⟨σ, rfl⟩ := hf δ
    exact (Rep.hom_comm_apply b σ (1 : Coeff)).symm
  · -- Evaluate the compatibility `b ≫ S.g = one₃` at `1` and use `e (one₃ 1) = 1`.
    have h1 : S.g (b 1) = one₃ 1 := by
      have hc := congrArg (fun k : unitRep G ⟶ (S.map (Rep.resFunctor f)).X₃ => k 1) hb
      exact hc
    rw [h1, hone]

end Work.SSGRoute
