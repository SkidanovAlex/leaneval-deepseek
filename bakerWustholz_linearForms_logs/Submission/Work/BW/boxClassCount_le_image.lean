import Mathlib
import Submission.Work.BW.subgroup_rayDegAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If a `ℤ`-linear map `Ψ : ℤ^N → ℤ^{N-ρ}` has kernel exactly the row lattice `rowLat N ρ M`, then the number of classes of the box `∏ᵢ [0, mᵢ]` modulo `rowLat M` is at most the number of distinct values that `Ψ` takes on the box. (Two box points with the same value of `Ψ` differ by an element of the kernel, hence lie in the same class, so the quotient map is a function of `Ψ`.) -/
theorem boxClassCount_le_image {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ)
    (Ψ : (Fin N → ℤ) →ₗ[ℤ] (Fin (N - ρ) → ℤ))
    (hker : LinearMap.ker Ψ = rowLat N ρ M) (m : Fin N → ℕ) :
    boxClassCount N ρ M m ≤ ((boxPts N m).image Ψ).card := by
  classical
  -- The quotient projection `q : ℤ^N → ℤ^N/𝒵`.
  set q : (Fin N → ℤ) → (Fin N → ℤ) ⧸ rowLat N ρ M :=
    fun v => Submodule.Quotient.mk v with hq
  -- Two points have the same image under `Ψ` exactly when they are equal modulo `𝒵`,
  -- because `ker Ψ = 𝒵`.
  have key : ∀ v w : Fin N → ℤ, q v = q w ↔ Ψ v = Ψ w := by
    intro v w
    show (Submodule.Quotient.mk v : (Fin N → ℤ) ⧸ rowLat N ρ M) = Submodule.Quotient.mk w ↔
      Ψ v = Ψ w
    rw [Submodule.Quotient.eq, ← hker, LinearMap.mem_ker]
    simp [map_sub, sub_eq_zero]
  -- Hence the class of a box point is a function of the value of `Ψ` on it: any preimage
  -- of that value under `Ψ` has the same class.
  let f : (Fin (N - ρ) → ℤ) → (Fin N → ℤ) ⧸ rowLat N ρ M :=
    fun y => if h : ∃ v, Ψ v = y then (Submodule.Quotient.mk (Classical.choose h) :
      (Fin N → ℤ) ⧸ rowLat N ρ M) else 0
  have hf : ∀ b ∈ boxPts N m, f (Ψ b) =
      (Submodule.Quotient.mk b : (Fin N → ℤ) ⧸ rowLat N ρ M) := by
    intro b _
    have hex : ∃ v, Ψ v = Ψ b := ⟨b, rfl⟩
    dsimp only [f]
    rw [dite_eq_left hex]
    exact (key (Classical.choose hex) b).mpr (Classical.choose_spec hex)
  have hcomp : (boxPts N m).image q = (boxPts N m).image (f ∘ Ψ) :=
    Finset.image_congr (fun b hb => by
      show q b = f (Ψ b)
      exact (hf b hb).symm)
  calc boxClassCount N ρ M m
      = ((boxPts N m).image q).card := rfl
    _ = ((boxPts N m).image (f ∘ Ψ)).card := by rw [hcomp]
    _ = (((boxPts N m).image Ψ).image f).card := by rw [Finset.image_image]
    _ ≤ ((boxPts N m).image Ψ).card := Finset.card_image_le

end Work.BW
