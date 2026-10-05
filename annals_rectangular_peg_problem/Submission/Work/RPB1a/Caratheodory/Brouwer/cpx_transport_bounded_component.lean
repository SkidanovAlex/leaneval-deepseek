import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.isBounded_image_continuousLinearEquiv

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **Transport of "there is a bounded complementary component" along a homeomorphism that preserves
boundedness.**  If `h : X ≃ₜ Y` maps bounded sets to bounded sets with bounded inverse (expressed as
the hypothesis `hbdd : ∀ s, IsBounded (h '' s) ↔ IsBounded s`), then for any `γ : Circle → X` there
is a point of `X` outside `range γ` whose complementary component is bounded if and only if there is
a point of `Y` outside `range (h ∘ γ)` whose complementary component is bounded.

Indeed `h` identifies the connected components of `(range γ)ᶜ` with those of `(range (h ∘ γ))ᶜ`
(`Homeomorph.image_connectedComponentIn`) and `hbdd` says exactly that it preserves boundedness of
these components. -/
theorem transport_exists_bounded_component {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : X ≃ₜ Y) (hbdd : ∀ s : Set X, Bornology.IsBounded (h '' s) ↔ Bornology.IsBounded s)
    (γ : Circle → X) :
    (∃ x : X, x ∉ Set.range γ ∧
        Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x)) ↔
    (∃ y : Y, y ∉ Set.range (fun z : Circle => h (γ z)) ∧
        Bornology.IsBounded
          (connectedComponentIn (((Set.range (fun z : Circle => h (γ z)))ᶜ)) y)) := by
  have hrange : Set.range (fun z : Circle => h (γ z)) = h '' Set.range γ := by
    change Set.range (h ∘ γ) = h '' Set.range γ
    rw [Set.range_comp]
  have hcompl : h '' (Set.range γ)ᶜ = ((Set.range (fun z : Circle => h (γ z)))ᶜ) := by
    rw [Set.image_compl_eq h.bijective, ← hrange]
  have key : ∀ x : X, x ∈ (Set.range γ)ᶜ →
      h '' connectedComponentIn ((Set.range γ)ᶜ) x
      = connectedComponentIn (((Set.range (fun z : Circle => h (γ z)))ᶜ)) (h x) := by
    intro x hx
    rw [Homeomorph.image_connectedComponentIn h hx, hcompl]
  constructor
  · rintro ⟨x, hx, hb⟩
    refine ⟨h x, ?_, ?_⟩
    · intro hmem
      rcases hmem with ⟨z, hz⟩
      exact hx ⟨z, h.injective hz⟩
    · rw [← key x hx]
      exact (hbdd _).2 hb
  · rintro ⟨y, hy, hb⟩
    have hx : h.symm y ∉ Set.range γ := by
      intro hmem
      rcases hmem with ⟨z, hz⟩
      exact hy ⟨z, by
        show h (γ z) = y
        rw [hz, Homeomorph.apply_symm_apply]⟩
    refine ⟨h.symm y, hx, ?_⟩
    have hkey := key (h.symm y) hx
    rw [Homeomorph.apply_symm_apply] at hkey
    rw [← hkey] at hb
    exact (hbdd _).1 hb

/-- **Transferring "there is a bounded complementary component" between `ℝ × ℝ` and `ℂ`.**

`Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ` is a linear homeomorphism whose two directions are both
Lipschitz (the product norm of `ℝ × ℝ` and the Euclidean norm of `ℂ` are equivalent), so it identifies
the connected components of the complement of `range γ` with those of the complement of
`range (fun z => Complex.equivRealProdCLM.symm (γ z))` and preserves boundedness. -/
theorem cpx_transport_bounded_component (γ : Circle → ℝ × ℝ) :
    (∃ x : ℝ × ℝ, x ∉ Set.range γ ∧
        Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x)) ↔
    (∃ y : ℂ, y ∉ Set.range (fun z : Circle => Complex.equivRealProdCLM.symm (γ z)) ∧
        Bornology.IsBounded
          (connectedComponentIn (((Set.range (fun z : Circle => Complex.equivRealProdCLM.symm (γ z)))ᶜ)) y)) := by
  refine transport_exists_bounded_component Complex.equivRealProdCLM.symm.toHomeomorph
    (fun s => ?_) γ
  exact isBounded_image_continuousLinearEquiv Complex.equivRealProdCLM.symm s

end Work.RPB1a.Caratheodory.Brouwer
