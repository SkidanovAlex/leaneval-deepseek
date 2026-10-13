import Mathlib
import Submission.Work.WilE2.VcbDefs

set_option autoImplicit false
noncomputable section

open Set

namespace Work.WilE2

/-- If `Φ : ℝ^k → ℝ^l` is continuous, `S ⊆ ℝ^k`, `X ⊆ ℝ^l`, `Φ` maps `S` into `X`, and there is a
section `Ψ : X → S` of `Φ` (i.e. `Φ (Ψ x) = x` for all `x ∈ X`), then the image under `Φ` of a
hitting set of `S` is a hitting set of `X`.

Indeed, given `x ∈ X`, the component of `Ψ x` in `S` contains a point `y` of the hitting set of `S`;
the continuous image of that component is a connected subset of `X` containing both `x` and `Φ y`,
whence `Φ y` lies in the component of `x` in `X`. -/
theorem hits_image {k l : ℕ} (Φ : (Fin k → ℝ) → (Fin l → ℝ)) (hΦ : Continuous Φ)
    (Ψ : (Fin l → ℝ) → (Fin k → ℝ)) {S : Set (Fin k → ℝ)} {X : Set (Fin l → ℝ)}
    (hSX : ∀ y ∈ S, Φ y ∈ X) (hXS : ∀ x ∈ X, Ψ x ∈ S) (hΨΦ : ∀ x ∈ X, Φ (Ψ x) = x)
    (s : Finset (Fin k → ℝ)) (hs : (↑s : Set (Fin k → ℝ)) ⊆ S) (hhits : Work.WilE2.Hits S s) :
    Work.WilE2.Hits X (s.image Φ) := by
  intro x hx
  obtain ⟨z, hz, hcomp⟩ := hhits (Ψ x) (hXS x hx)
  refine ⟨Φ z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
  have hzS : z ∈ S := hs hz
  have hzmem : z ∈ connectedComponentIn S (Ψ x) := by
    rw [hcomp]; exact mem_connectedComponentIn hzS
  have hpre : IsPreconnected (Φ '' connectedComponentIn S (Ψ x)) :=
    IsPreconnected.image isPreconnected_connectedComponentIn Φ hΦ.continuousOn
  have hsub : Φ '' connectedComponentIn S (Ψ x) ⊆ X := by
    rintro _ ⟨w, hw, rfl⟩
    exact hSX w (connectedComponentIn_subset S (Ψ x) hw)
  have hPsi : Ψ x ∈ connectedComponentIn S (Ψ x) := mem_connectedComponentIn (hXS x hx)
  have hxIm : x ∈ Φ '' connectedComponentIn S (Ψ x) := ⟨Ψ x, hPsi, hΨΦ x hx⟩
  have hsub2 : Φ '' connectedComponentIn S (Ψ x) ⊆ connectedComponentIn X x :=
    hpre.subset_connectedComponentIn hxIm hsub
  exact connectedComponentIn_eq (hsub2 ⟨z, hzmem, rfl⟩)

end Work.WilE2
