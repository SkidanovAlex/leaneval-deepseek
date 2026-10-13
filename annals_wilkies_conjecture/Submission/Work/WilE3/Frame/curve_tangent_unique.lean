/-
  annals_wilkies_conjecture, AREA E3, frame step: the algebraic core of the tangency of the
  straightened curve.

  The frame vector `VcoefC c h ι l z` (`Vcoef.lean`) is the vector with `ιᶜ`-coordinates `e_l` which
  is tangent to `{h = 0}` at `z` (`VcoefC_tangent`).  Its uniqueness among such vectors is what turns
  the chain rule identity `DΦ (d) = (e_l, 0)` — obtained by differentiating `Φ (Ψ (v,0)) = (v,0)` —
  into `d = VcoefC c h ι l z`: the difference is supported on the `ι`-coordinates and kills the
  `ι`-Jacobian, so it vanishes because that Jacobian is invertible.

  This file provides that uniqueness in the form needed by
  `Work.WilE3.Frame.fderiv_slice_eq_VcoefC_eventual`: a vector supported off `Set.range ι` and
  tangent to `{h = 0}` is zero.
-/
import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.injective_iota_of_jacValC_ne_zero

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E

variable {k r j : ℕ}

/-- **Uniqueness of a vector supported on the `ι`-coordinates and tangent to `{h = 0}`.**  If
`δ : Fin k → ℂ` vanishes outside `Set.range ι` and `∑ i, δ i * (∂_i h_a)(z) = 0` for every `a`, at a
complex point `z` where the `ι`-Jacobian of `h` is invertible, then `δ = 0`. -/
theorem eq_zero_of_support_and_tangent (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (z : Fin k → ℂ) (hz : jacValC c h ι z ≠ 0) (δ : Fin k → ℂ)
    (hδ : ∀ i : Fin k, i ∉ Set.range ι → δ i = 0)
    (hT : ∀ a : Fin j, ∑ i, δ i * eaEvalC c (eaD c i (h a)) z = 0) :
    δ = 0 := by
  classical
  have hinj : Function.Injective ι := injective_iota_of_jacValC_ne_zero c h ι z hz
  -- The tangency sums only see the `ι`-coordinates of `δ`.
  have hsum : ∀ a : Fin j, (∑ i : Fin k, δ i * eaEvalC c (eaD c i (h a)) z)
      = ∑ b : Fin j, δ (ι b) * eaEvalC c (eaD c (ι b) (h a)) z := by
    intro a
    have hsub : (Finset.univ.filter fun i : Fin k => i ∈ Set.range ι) ⊆ Finset.univ :=
      fun x _ => Finset.mem_univ x
    rw [← Finset.sum_subset hsub (fun x _ hxs => by
      rw [Finset.mem_filter] at hxs
      have hxr : x ∉ Set.range ι := fun hxr => hxs ⟨Finset.mem_univ x, hxr⟩
      rw [hδ x hxr, zero_mul])]
    have hfilter : (Finset.univ.filter fun i : Fin k => i ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image]
    intro x _ y _ hxy
    exact hinj hxy
  -- The matrix-vector form of the tangency condition.
  have hMv : (jacMatC c h ι z) *ᵥ (fun b : Fin j => δ (ι b)) = 0 := by
    funext a
    rw [Matrix.mulVec_apply_eq_sum]
    have h1 : (∑ j : Fin j, jacMatC c h ι z a j * δ (ι j))
        = ∑ j : Fin j, δ (ι j) * eaEvalC c (eaD c (ι j) (h a)) z := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [jacMatC, Matrix.of_apply]
      ring
    rw [h1, ← hsum a]
    exact hT a
  have hdet : (jacMatC c h ι z).det ≠ 0 := by
    rw [← jacValC_eq_det]
    exact hz
  have hx : (fun b : Fin j => δ (ι b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hMv
  funext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨b, rfl⟩ := hi
    exact congrFun hx b
  · exact hδ i hi

end

end Work.WilE3.Frame
