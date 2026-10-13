import Mathlib
import Submission.Work.WilE7.FaceAux.FaceDefs

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.FaceAux

open WilkiesDesign WilkiesDesign.E

/-! ## Continuity of the pinning map -/

/-- `facePoint` is continuous: it is the identity on the first `p + (m+1)` coordinates and the
constant `1` on the last coordinate. -/
theorem continuous_facePoint (p m : ℕ) :
    Continuous (facePoint (p := p) (m := m)) := by
  apply continuous_pi
  intro i
  by_cases h : (i : ℕ) < faceN p m
  · have hfun : (fun u : Fin (p + (m+1)) → ℝ => facePoint u i)
        = fun u => u ⟨(i : ℕ), h⟩ := by
      funext u
      show (if h' : (i : ℕ) < faceN p m then u ⟨(i : ℕ), h'⟩ else 1)
          = u ⟨(i : ℕ), h⟩
      rw [dif_pos h]
    rw [hfun]
    exact continuous_apply _
  · have hfun : (fun u : Fin (p + (m+1)) → ℝ => facePoint u i) = fun _ => (1 : ℝ) := by
      funext u
      show (if h' : (i : ℕ) < faceN p m then u ⟨(i : ℕ), h'⟩ else 1) = 1
      rw [dif_neg h]
    rw [hfun]
    exact continuous_const

/-! ## A general topological fact -/

/-- If `φ : α → β` and `ψ : β → α` are continuous, `ψ ∘ φ = id`, `φ ∘ ψ = id` on `S`, `φ` maps
`X` into `S` and `ψ` maps `S` into `X`, then `φ` carries the connected component of `u₀` in `X`
bijectively onto the connected component of `φ u₀` in `S`. -/
theorem image_connectedComponentIn_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {X : Set α} {S : Set β} (φ : α → β) (ψ : β → α)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hψφ : ∀ x, ψ (φ x) = x) (hφψ : ∀ y ∈ S, φ (ψ y) = y)
    (hφX : ∀ x ∈ X, φ x ∈ S) (hψS : ∀ y ∈ S, ψ y ∈ X) {u₀ : α} (hu₀ : u₀ ∈ X) :
    φ '' connectedComponentIn X u₀ = connectedComponentIn S (φ u₀) := by
  apply Set.Subset.antisymm
  · -- the image of the component of `u₀` is a preconnected subset of `S` containing `φ u₀`
    have hmem : φ u₀ ∈ φ '' connectedComponentIn X u₀ :=
      ⟨u₀, mem_connectedComponentIn hu₀, rfl⟩
    have hsub : φ '' connectedComponentIn X u₀ ⊆ S := by
      rintro z ⟨x, hx, rfl⟩
      exact hφX x (connectedComponentIn_subset X u₀ hx)
    exact IsPreconnected.subset_connectedComponentIn
      (isPreconnected_connectedComponentIn.image φ hφc.continuousOn) hmem hsub
  · -- the `ψ`-image of the component of `φ u₀` is a preconnected subset of `X` containing `u₀`
    have hmem : u₀ ∈ ψ '' connectedComponentIn S (φ u₀) :=
      ⟨φ u₀, mem_connectedComponentIn (hφX u₀ hu₀), hψφ u₀⟩
    have hsub : ψ '' connectedComponentIn S (φ u₀) ⊆ X := by
      rintro z ⟨y, hy, rfl⟩
      exact hψS y (connectedComponentIn_subset S (φ u₀) hy)
    have hkey : ψ '' connectedComponentIn S (φ u₀) ⊆ connectedComponentIn X u₀ :=
      IsPreconnected.subset_connectedComponentIn
        (isPreconnected_connectedComponentIn.image ψ hψc.continuousOn) hmem hsub
    rintro y hy
    have hyS : y ∈ S := connectedComponentIn_subset S (φ u₀) hy
    exact ⟨ψ y, hkey ⟨y, hy, rfl⟩, hφψ y hyS⟩

/-! ## The component of the top face -/

theorem faceY1_component {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m+1)))
    (u₀ : Fin (p + (m+1)) → ℝ) (hu₀ : u₀ ∈ Z.set) :
    connectedComponentIn (Work.WilE7.FaceAux.faceY1 Z).set (Work.WilE7.FaceAux.facePoint u₀)
      = Work.WilE7.FaceAux.facePoint '' connectedComponentIn Z.set u₀ := by
  exact (image_connectedComponentIn_eq (X := Z.set) (S := (faceY1 Z).set)
    facePoint (Work.WilE7.takeZ (faceN_le_faceK p m))
    (continuous_facePoint p m) (Work.WilE7.continuous_takeZ (faceN_le_faceK p m))
    takeZ_facePoint (fun y hy => facePoint_takeZ_self Z hy)
    (fun x hx => facePoint_mem Z hx) (fun y hy => takeZ_mem_of_mem_faceY1 Z hy)
    hu₀).symm

end Work.WilE7.FaceAux
