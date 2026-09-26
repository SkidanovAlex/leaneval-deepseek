import Mathlib
import Submission.Work.Smooth.SphereJordan.janiszewskiDisjointSphere
import Submission.Work.Smooth.SphereJordan.janiszewski_sphere

/-!
# Janiszewski's theorem for two compact plane sets with connected intersection

`Work.Smooth.JordanSeparation.janiszewskiConnectedInterCompact`: if `F₁ F₂ ⊆ ℂ` are compact, their
intersection is non-empty and preconnected, and `x y ∉ F₁ ∪ F₂` lie in the same connected component
both of `F₁ᶜ` and of `F₂ᶜ`, then they lie in the same connected component of `(F₁ ∪ F₂)ᶜ`.

This is Janiszewski's theorem (Z. Janiszewski, *Sur les continus irréductibles entre deux points*,
J. École Polytech. (2) 16 (1911), 79–170; see also R. Luisto, *Proof of the Jordan curve theorem*,
Theorem 2.3 and Lemma 2.4).

The proof here is a *reduction* of the plane statement to the Riemann-sphere form
`Work.Smooth.SphereJordan.janiszewski_sphere` (proved in the sibling file), which is the analytic
core of the argument: there `A₁, A₂` are closed subsets of `S² = ℂ ∪ {∞}` and `a, b ∈ S²`.

Concretely, view the compact (hence closed-and-bounded) sets `F₁, F₂ ⊆ ℂ` inside `S² = OnePoint ℂ`
as `↑ '' F₁`, `↑ '' F₂`, and take `a = ↑x`, `b = ↑y`.  The transfer of the hypotheses (and of the
conclusion) between the plane and the sphere is `connectedComponentIn_compl_coe`
(`A ⊆ ℂ` compact: the sphere-component of a finite point meets `ℂ` exactly in the plane-component).
-/

namespace Work.Smooth.JordanSeparation

open Set

theorem janiszewskiConnectedInterCompact
    {F₁ F₂ : Set ℂ} (h₁ : IsCompact F₁) (h₂ : IsCompact F₂)
    (hne : (F₁ ∩ F₂).Nonempty) (hcon : IsPreconnected (F₁ ∩ F₂)) {x y : ℂ}
    (hx : x ∉ F₁ ∪ F₂) (hy : y ∉ F₁ ∪ F₂)
    (h₁' : y ∈ connectedComponentIn F₁ᶜ x) (h₂' : y ∈ connectedComponentIn F₂ᶜ x) :
    y ∈ connectedComponentIn (F₁ ∪ F₂)ᶜ x := by
  rcases eq_or_ne x y with rfl | hxy
  · exact mem_connectedComponentIn (by simpa using hx)
  · -- transport to the Riemann sphere `OnePoint ℂ`
    set A₁ : Set (OnePoint ℂ) := (↑) '' F₁ with hA₁
    set A₂ : Set (OnePoint ℂ) := (↑) '' F₂ with hA₂
    have hcl₁ : IsClosed A₁ := OnePoint.isClosed_image_coe.mpr ⟨h₁.isClosed, h₁⟩
    have hcl₂ : IsClosed A₂ := OnePoint.isClosed_image_coe.mpr ⟨h₂.isClosed, h₂⟩
    have hne' : (A₁ ∩ A₂).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      refine ⟨(z : OnePoint ℂ), ?_⟩
      rw [hA₁, hA₂]
      exact ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩
    have hcon' : IsPreconnected (A₁ ∩ A₂) := by
      have h : A₁ ∩ A₂ = (↑) '' (F₁ ∩ F₂) := by
        rw [hA₁, hA₂, Set.image_inter OnePoint.coe_injective]
      rw [h]
      exact hcon.image _ OnePoint.continuous_coe.continuousOn
    have ha : (x : OnePoint ℂ) ∉ A₁ ∪ A₂ := by
      simp only [hA₁, hA₂, Set.mem_union, Set.mem_image, OnePoint.coe_injective.eq_iff,
        exists_eq_right]
      exact hx
    have hb : (y : OnePoint ℂ) ∉ A₁ ∪ A₂ := by
      simp only [hA₁, hA₂, Set.mem_union, Set.mem_image, OnePoint.coe_injective.eq_iff,
        exists_eq_right]
      exact hy
    have h₁'' : (y : OnePoint ℂ) ∈ connectedComponentIn A₁ᶜ (x : OnePoint ℂ) := by
      have h := (Set.ext_iff.mp
        (Work.Smooth.SphereJordan.connectedComponentIn_compl_coe h₁ x) y).mpr h₁'
      simpa only [Set.mem_ofPred_eq, hA₁] using h
    have h₂'' : (y : OnePoint ℂ) ∈ connectedComponentIn A₂ᶜ (x : OnePoint ℂ) := by
      have h := (Set.ext_iff.mp
        (Work.Smooth.SphereJordan.connectedComponentIn_compl_coe h₂ x) y).mpr h₂'
      simpa only [Set.mem_ofPred_eq, hA₂] using h
    have key := Work.Smooth.SphereJordan.janiszewski_sphere hcl₁ hcl₂ hne' hcon'
      (a := (x : OnePoint ℂ)) (b := (y : OnePoint ℂ)) (by simpa using hxy) ha hb h₁'' h₂''
    have hunion : A₁ ∪ A₂ = (↑) '' (F₁ ∪ F₂) := by
      rw [hA₁, hA₂, Set.image_union]
    rw [hunion] at key
    exact (Set.ext_iff.mp
      (Work.Smooth.SphereJordan.connectedComponentIn_compl_coe (h₁.union h₂) x) y).mp key

end Work.Smooth.JordanSeparation
