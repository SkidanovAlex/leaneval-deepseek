import Mathlib
import Submission.Work.Mostow.stabFlatDefs

/-!
# The linear part of a horospherical similarity acts tangentially to the horosphere

For `ξ ∈ Sph n` the two null vectors `θ_ξ = (ξ,1)` and `η_ξ = (ξ,-1)` satisfy `⟨θ,θ⟩ = 0`,
`⟨η,η⟩ = 0`, `⟨θ,η⟩ = 2`.  Hence a vector `z` of `V^⊥` — the `⟨·,·⟩`-orthogonal complement of
`span{θ,η}`, on which the horospheres at `ξ` are modelled as a flat space — has *both* its time
coordinate and its inner product against `ξ` equal to `0`:

  `⟨z,θ⟩ = inner ℝ (hspat z) ξ - htime z = 0`,  `⟨z,η⟩ = inner ℝ (hspat z) ξ + htime z = 0`.

The linear part `Work.Mostow.flatLin ξ M` of the action of `M` on the horospheres at `ξ` is
`hspat ∘ horoProj ξ ∘ (M *ᵥ ·) ∘ wvec`, and `horoProj ξ` lands in `V^⊥`; therefore its image
lies in `ξ^⊥ ⊆ E n`, i.e. in the tangent space of the horosphere.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- A vector `z` of `V^⊥ = {x | ⟨x,θ_ξ⟩ = ⟨x,η_ξ⟩ = 0}` has `inner ℝ (hspat z) ξ = 0`; i.e. its
spatial part is orthogonal to `ξ` in the Euclidean space `E n`. -/
lemma inner_hspat_eq_zero_of_mform_theta_eta (ξ : E n)
    {z : Fin n ⊕ Fin 1 → ℝ} (h1 : mform z (theta ξ) = 0) (h2 : mform z (horoEta ξ) = 0) :
    inner ℝ (hspat z) ξ = 0 := by
  rw [mform_eq] at h1 h2
  simp only [hspat_theta, htime_theta, hspat_horoEta, htime_horoEta, mul_one, mul_neg] at h1 h2
  linarith

/-- The linear part of a horospherical similarity acts tangentially to every horosphere at `ξ`. -/
theorem flatLinInnerZero {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (y : Submission.Mostow.E n) :
    inner ℝ (Work.Mostow.flatLin ξ M y) ξ = 0 := by
  have := inner_hspat_eq_zero_of_mform_theta_eta ξ
    (mform_horoProj_theta ξ hξ (M.mulVec (wvec y)))
    (mform_horoProj_eta ξ hξ (M.mulVec (wvec y)))
  simpa [flatLin_apply] using this

end

end Work.Mostow
