import Mathlib

namespace Work.WilC4aP

/-- Two continuous lifts of the same map to a covering space that agree at one point of a
preconnected base agree everywhere. -/
theorem eq_of_eq_at_of_lifts {E X A : Type*} [TopologicalSpace E] [T2Space E] [TopologicalSpace X]
    [TopologicalSpace A] [PreconnectedSpace A] {p : E → X} {s : Set X} (cov : IsCoveringMapOn p s)
    {f : A → X} (hf : ∀ a, f a ∈ s) {F G : A → E} (hFc : Continuous F) (hGc : Continuous G)
    (hF : p ∘ F = f) (hG : p ∘ G = f) {a₀ : A} (h : F a₀ = G a₀) : F = G := by
  have hcompF : ∀ a, p (F a) = f a := fun a => by
    have h1 := congrFun hF a; simpa only [Function.comp_apply] using h1
  have hcompG : ∀ a, p (G a) = f a := fun a => by
    have h1 := congrFun hG a; simpa only [Function.comp_apply] using h1
  have hFmem : ∀ a, p (F a) ∈ s := fun a => by rw [hcompF a]; exact hf a
  have hGmem : ∀ a, p (G a) ∈ s := fun a => by rw [hcompG a]; exact hf a
  let F' : A → p ⁻¹' s := fun a => ⟨F a, hFmem a⟩
  let G' : A → p ⁻¹' s := fun a => ⟨G a, hGmem a⟩
  have hF'c : Continuous F' := hFc.subtype_mk hFmem
  have hG'c : Continuous G' := hGc.subtype_mk hGmem
  have he : (s.restrictPreimage p) ∘ F' = (s.restrictPreimage p) ∘ G' := by
    funext a
    apply Subtype.ext
    show p (F a) = p (G a)
    rw [hcompF a, hcompG a]
  have h' : F' a₀ = G' a₀ := by
    apply Subtype.ext
    simpa only [F', G'] using h
  have key := (cov.isCoveringMap_restrictPreimage).eq_of_comp_eq hF'c hG'c he a₀ h'
  funext a
  exact congrArg Subtype.val (congrFun key a)

end Work.WilC4aP
