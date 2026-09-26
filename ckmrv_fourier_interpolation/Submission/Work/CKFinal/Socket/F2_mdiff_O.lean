/-
# Holomorphy of the socket layer `F₂` on `O`

`Socket.F2` is the glued function: on `U0 ∪ W1` it is the glued layer `G`, and on `Wm1` it is
the value forced by the first recurrence,

  `F₂(τ) = 2 G(τ+1) - G(τ+2) - T2op (gaussTerm · r) (τ)`.

This file proves that `F₂` is holomorphic on `O = U0 ∪ W1 ∪ Wm1`, given that the layer
`layerFn` is holomorphic on `U0`.  The proof splits `O` into three pieces:

* on `Wm1` (open), the above explicit formula holds near the point, and each of its three
  summands is holomorphic at the point: `G` at `τ+1 ∈ U0` and at `τ+2 ∈ W1` (where `U0 ∪ W1`
  is open), the shifts `σ ↦ c +ᵥ σ` being holomorphic
  (`mdifferentiable_vadd_real`), and `T2op (gaussTerm · r)` being holomorphic;
* on `U0`, `F₂` agrees with the layer `layerFn` (`Socket.F2_agree_U0`), which is
  holomorphic there by hypothesis;
* on the rest, i.e. on `W1`, the point has a neighbourhood contained in `W1`, hence disjoint
  from `Wm1` (`Socket.Wm1_disjoint_W1`), and there `F₂ = G`, holomorphic on `U0 ∪ W1`.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.F2_agree_U0
import Submission.Work.Asymptotics.exists_pair_of_propagated_F2

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- Translation of the upper half-plane by a real number is holomorphic. -/
lemma mdifferentiable_vadd_real (x : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : ℍ => x +ᵥ τ) := by
  have hpt : ∀ τ : ℍ, ofComplex ((τ : ℂ) + (x : ℂ)) = x +ᵥ τ := by
    intro τ
    have hz : 0 < ((τ : ℂ) + (x : ℂ)).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact τ.im_pos
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    apply UpperHalfPlane.ext_iff.mpr
    rw [UpperHalfPlane.coe_vadd]
    ring
  have hfun : (fun τ : ℍ => x +ᵥ τ)
      = ofComplex ∘ ((fun τ : ℍ => (τ : ℂ)) + (fun _ : ℍ => (x : ℂ))) := by
    funext τ
    simp only [Function.comp_apply, Pi.add_apply]
    exact (hpt τ).symm
  rw [hfun]
  intro τ
  have hB : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ((fun τ : ℍ => (τ : ℂ)) + (fun _ : ℍ => (x : ℂ))) τ :=
    UpperHalfPlane.mdifferentiable_coe.mdifferentiableAt.add mdifferentiableAt_const
  have hA : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      ofComplex (((fun τ : ℍ => (τ : ℂ)) + (fun _ : ℍ => (x : ℂ))) τ) :=
    UpperHalfPlane.mdifferentiableAt_ofComplex (by
      rw [Pi.add_apply, Complex.add_im, Complex.ofReal_im, add_zero]; exact τ.im_pos)
  exact MDifferentiableAt.comp (f := (fun τ : ℍ => (τ : ℂ)) + (fun _ : ℍ => (x : ℂ))) τ hA hB

theorem F2_mdiff_O (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hU0 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (Work.CKFinal.Socket.layerFn ℓ d r) Work.CKFinal.U0) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (Work.CKFinal.Socket.F2 ℓ d hd r) (Work.CKFinal.Socket.O ℓ d hd) := by
  have hG := G_mdiff ℓ d hd r hU0
  have hopen : IsOpen (U0 ∪ W1 ℓ d hd) := isOpen_U0.union (isOpen_W1 ℓ d hd)
  intro τ hτ
  by_cases hm1 : τ ∈ Wm1 ℓ d hd
  · -- on the recurrence region `F₂` is the explicit combination
    have hspec := mem_Wm1.mp hm1
    have hG1 : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (G ℓ d hd r) ((1 : ℝ) +ᵥ τ) :=
      hG.mdifferentiableAt (hopen.mem_nhds (Or.inl hspec.1))
    have hG2 : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (G ℓ d hd r) ((2 : ℝ) +ᵥ τ) :=
      hG.mdifferentiableAt (hopen.mem_nhds (Or.inr hspec.2.1))
    have hc2 : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun σ : ℍ => G ℓ d hd r ((2 : ℝ) +ᵥ σ)) τ :=
      MDifferentiableAt.comp (f := fun σ : ℍ => (2 : ℝ) +ᵥ σ) τ hG2
        (mdifferentiable_vadd_real 2).mdifferentiableAt
    have hc1 : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun σ : ℍ => G ℓ d hd r ((1 : ℝ) +ᵥ σ)) τ :=
      MDifferentiableAt.comp (f := fun σ : ℍ => (1 : ℝ) +ᵥ σ) τ hG1
        (mdifferentiable_vadd_real 1).mdifferentiableAt
    have hmul : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun σ : ℍ => (2 : ℂ) * G ℓ d hd r ((1 : ℝ) +ᵥ σ)) τ :=
      mdifferentiableAt_const.mul hc1
    have hT : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r)) τ :=
      (Work.Asymptotics.mdifferentiable_T2op_gaussTerm r).mdifferentiableAt
    have hcomb : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun σ : ℍ => 2 * G ℓ d hd r ((1 : ℝ) +ᵥ σ) - G ℓ d hd r ((2 : ℝ) +ᵥ σ)
          - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) σ) τ :=
      (hmul.sub hc2).sub hT
    have hcongr : (fun σ : ℍ => F2 ℓ d hd r σ) =ᶠ[𝓝 τ]
        (fun σ : ℍ => 2 * G ℓ d hd r ((1 : ℝ) +ᵥ σ) - G ℓ d hd r ((2 : ℝ) +ᵥ σ)
          - Work.Kernels.T2op (fun σ : ℍ => Work.Kernels.gaussTerm σ r) σ) := by
      filter_upwards [(isOpen_Wm1 ℓ d hd).mem_nhds hm1] with σ hσ
      exact F2_of_mem_Wm1 ℓ d hd r hσ
    exact (hcomb.congr_of_eventuallyEq hcongr).mdifferentiableWithinAt
  · by_cases hU : τ ∈ U0
    · -- on `U₀`, `F₂` agrees with the layer
      have hcongr : (fun σ : ℍ => F2 ℓ d hd r σ) =ᶠ[𝓝 τ] (fun σ : ℍ => layerFn ℓ d r σ) := by
        filter_upwards [isOpen_U0.mem_nhds hU] with σ hσ
        exact F2_agree_U0 ℓ d hd r hσ
      have hlayer : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (layerFn ℓ d r) τ :=
        hU0.mdifferentiableAt (isOpen_U0.mem_nhds hU)
      exact (hlayer.congr_of_eventuallyEq hcongr).mdifferentiableWithinAt
    · -- otherwise `τ ∈ W₁`, which is disjoint from `Wm1`
      have h1 : τ ∈ W1 ℓ d hd := by
        rcases hτ with h | h
        · rcases h with h | h
          · exact absurd h hU
          · exact h
        · exact absurd h hm1
      have hcongr : (fun σ : ℍ => F2 ℓ d hd r σ) =ᶠ[𝓝 τ] (fun σ : ℍ => G ℓ d hd r σ) := by
        filter_upwards [(isOpen_W1 ℓ d hd).mem_nhds h1] with σ hσ
        exact F2_of_not_mem_Wm1 ℓ d hd r
          (fun hmem => (Set.disjoint_left.mp (Wm1_disjoint_W1 ℓ d hd)) hmem hσ)
      have hGat : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (G ℓ d hd r) τ :=
        hG.mdifferentiableAt (hopen.mem_nhds (Or.inr h1))
      exact (hGat.congr_of_eventuallyEq hcongr).mdifferentiableWithinAt

end Socket
end Work.CKFinal
