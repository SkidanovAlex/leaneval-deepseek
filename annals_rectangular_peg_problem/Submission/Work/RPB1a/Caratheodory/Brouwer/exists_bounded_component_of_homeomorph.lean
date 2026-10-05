import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **Transfer of a bounded complementary component along a homeomorphism.**  If `e : ℂ ≃ₜ ℂ` sends
bounded sets to bounded sets via its inverse (e.g. `e` is an affine similarity), and the complement of
the range of `fun c => e (γ c)` has a bounded connected component containing `x`, then the complement
of the range of `γ` itself has a bounded connected component: namely the one containing `e.symm x`. -/
theorem exists_bounded_component_of_homeomorph (e : ℂ ≃ₜ ℂ)
    (hbdd : ∀ S : Set ℂ, Bornology.IsBounded S → Bornology.IsBounded (e.symm '' S))
    (γ : Circle → ℂ) (x : ℂ) (hx : x ∉ Set.range (fun c => e (γ c)))
    (hb : Bornology.IsBounded (connectedComponentIn ((Set.range (fun c => e (γ c)))ᶜ) x)) :
    ∃ y : ℂ, y ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) y) := by
  refine ⟨e.symm x, ?_, ?_⟩
  · -- `e.symm x` is outside `range γ`
    intro hmem
    obtain ⟨c, hc⟩ := hmem
    refine hx ⟨c, ?_⟩
    show e (γ c) = x
    rw [hc, Homeomorph.apply_symm_apply]
  · -- the complementary component of `e.symm x` is the image under `e.symm` of that of `x`
    have hrange : e.symm '' Set.range (fun c => e (γ c)) = Set.range γ := by
      have h : (⇑e.symm ∘ (fun c => e (γ c))) = γ :=
        funext fun c => Homeomorph.symm_apply_apply e (γ c)
      rw [← Set.range_comp, h]
    have hcompl : e.symm '' ((Set.range (fun c => e (γ c)))ᶜ) = (Set.range γ)ᶜ := by
      rw [Set.image_compl_eq e.symm.bijective, hrange]
    have himg := Homeomorph.image_connectedComponentIn
      (s := ((Set.range (fun c => e (γ c)))ᶜ)) (x := x) e.symm hx
    rw [hcompl] at himg
    rw [← himg]
    exact hbdd _ hb

end Work.RPB1a.Caratheodory.Brouwer
