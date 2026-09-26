import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaFoundation
import Submission.Work.Smooth.SphereJordan.thetaSpansOfPlane
import Submission.Work.Smooth.SphereJordan.thetaOddCore
import Submission.Work.Smooth.SphereJordan.thetaFlip
import Submission.Work.Smooth.SphereJordan.thetaPlaneSpansUp

/-!
# The theta graph of two discs joined by two arcs has two disc-shaped halves

`Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane`: the complement, on the Riemann sphere, of
two disjoint embedded discs `D₁`, `D₂` joined by two disjoint arcs `α`, `β` (interiors off the
discs, mutually separated, distinct endpoints) is the disjoint union of two non-empty open
preconnected sets `P₁`, `P₂`, each of which is a *disc*: `closure Pᵢ` is the image of the model
disc `𝔻` under a continuous injection.

The proof reduces, along a Möbius chart moving a point off the graph to `∞`, to the corresponding
planar statement (`Work.Smooth.SphereJordan.thetaSpansOfPlane`, imported here, which carries out the
transposition back to the sphere), whose input is the planar theta statement with the disc-spanning
clause (module `thetaPlaneSpansUp`).

The elementary winding-number facts used below (`windNumber_eq_of_preconnected`,
`windNumber_eq_zero_of_mem_U`) live in the module `Submission.Work.Smooth.SphereJordan.thetaFoundation`
so that they can be imported without this module.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem thetaTwoHalvesSphereOfPlane (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set Work.Smooth.SphereJordan.RiemannSphere}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, Work.Smooth.SphereJordan.RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, le_refl 0, zero_le_one⟩ ∈ D₁) (hα₁ : α ⟨1, zero_le_one, le_refl 1⟩ ∈ D₂)
    (hβ₀ : β ⟨0, le_refl 0, zero_le_one⟩ ∈ D₁) (hβ₁ : β ⟨1, zero_le_one, le_refl 1⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, le_refl 0, zero_le_one⟩ ≠ β ⟨0, le_refl 0, zero_le_one⟩)
    (hαβ₁ : α ⟨1, zero_le_one, le_refl 1⟩ ≠ β ⟨1, zero_le_one, le_refl 1⟩) :
    ∃ P₁ P₂ : Set Work.Smooth.SphereJordan.RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ f₁ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective f₁ ∧ Set.range f₁ = closure P₁) ∧
      (∃ f₂ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective f₂ ∧ Set.range f₂ = closure P₂) := by
  have e0 : (⟨0, le_refl 0, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) =
      (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext rfl
  have e1 : (⟨1, zero_le_one, le_refl 1⟩ : Set.Icc (0 : ℝ) 1) =
      (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext rfl
  have hα₀' : α (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ D₁ := by rw [← e0]; exact hα₀
  have hα₁' : α (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ D₂ := by rw [← e1]; exact hα₁
  have hβ₀' : β (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ D₁ := by rw [← e0]; exact hβ₀
  have hβ₁' : β (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ D₂ := by rw [← e1]; exact hβ₁
  have hαβ₀' : α (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ≠ β (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
    rw [← e0]; exact hαβ₀
  have hαβ₁' : α (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ≠ β (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
    rw [← e1]; exact hαβ₁
  exact thetaSpansOfPlane h (thetaPlaneSpansUp h) hD₁ hD₂ hdisj α β hαinj hβinj
    hα₀' hα₁' hβ₀' hβ₁' hαint hβint hsep hαβ₀' hαβ₁'


end

end Work.Smooth.SphereJordan
