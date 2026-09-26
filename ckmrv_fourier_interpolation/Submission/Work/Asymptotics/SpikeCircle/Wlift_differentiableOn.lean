import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SpikeDefs
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip

namespace Work.Asymptotics.SpikeCircle

open Work.Kernels

/-- `w ↦ Tleft τ w` is holomorphic on the upper half plane: it is a `(2π)⁻¹`-multiple of the
difference of the two divided differences `D1`, `D2` of `w ↦ j(τ) − j(w)`, which is holomorphic
on `{w | 0 < w.im}`; a `dslope` of a function holomorphic near its base point is again
holomorphic there. -/
lemma differentiableOn_Tleft (τ : UpperHalfPlane) :
    DifferentiableOn ℂ (Tleft τ) {w : ℂ | 0 < w.im} := by
  set S : Set ℂ := {w : ℂ | 0 < w.im} with hS
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_im
  -- `w ↦ j(τ) - j(w)` is holomorphic on the upper half plane.
  have hj : DifferentiableOn ℂ (fun w : ℂ => jInvariantFun (UpperHalfPlane.ofComplex w)) S :=
    (UpperHalfPlane.mdifferentiable_iff (f := jInvariantFun)).mp
      Work.Asymptotics.mdifferentiable_jInvariantFun
  have hjl : DifferentiableOn ℂ (jlDiff τ) S := by
    have h : (jlDiff τ)
        = fun w : ℂ => jInvariantFun τ - jInvariantFun (UpperHalfPlane.ofComplex w) := rfl
    rw [h]
    exact (differentiableOn_const (jInvariantFun τ)).sub hj
  -- The two base points are in the upper half plane.
  have hmem1 : S ∈ nhds ((τ : ℂ) - 1) :=
    hSopen.mem_nhds (by simp only [hS, Set.mem_ofPred_eq]; rw [im_sub_one]; exact τ.im_pos)
  have hmem2 : S ∈ nhds ((τ : ℂ) + 1) :=
    hSopen.mem_nhds (by simp only [hS, Set.mem_ofPred_eq]; rw [im_add_one]; exact τ.im_pos)
  have hD1 : DifferentiableOn ℂ (dslope (jlDiff τ) ((τ : ℂ) - 1)) S :=
    (Complex.differentiableOn_dslope (f := jlDiff τ) (s := S) (c := (τ : ℂ) - 1) hmem1).mpr hjl
  have hD2 : DifferentiableOn ℂ (dslope (jlDiff τ) ((τ : ℂ) + 1)) S :=
    (Complex.differentiableOn_dslope (f := jlDiff τ) (s := S) (c := (τ : ℂ) + 1) hmem2).mpr hjl
  have h : (Tleft τ)
      = fun w : ℂ => (1 / (2 * (Real.pi : ℂ)))
          * (dslope (jlDiff τ) ((τ : ℂ) - 1) w - dslope (jlDiff τ) ((τ : ℂ) + 1) w) := by
    funext w
    simp only [Tleft, D1, D2]
  rw [h]
  exact (differentiableOn_const _).mul (hD1.sub hD2)

theorem Wlift_differentiableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) : DifferentiableOn ℂ (Work.Asymptotics.SpikeCircle.Wlift ℓ d τ) {w : ℂ | 0 < w.im} := by
  set S : Set ℂ := {w : ℂ | 0 < w.im} with hS
  have hDelta : DifferentiableOn ℂ
      (fun w : ℂ => DeltaFun (UpperHalfPlane.ofComplex w)) S :=
    (UpperHalfPlane.mdifferentiable_iff (f := DeltaFun)).mp Work.Asymptotics.mdiff_DeltaFun
  have hAfun : DifferentiableOn ℂ
      (fun w : ℂ => AfunFun ℓ d τ (UpperHalfPlane.ofComplex w)) S :=
    (UpperHalfPlane.mdifferentiable_iff (f := fun z : UpperHalfPlane => AfunFun ℓ d τ z)).mp
      (Work.Asymptotics.mdifferentiable_AfunFun_snd ℓ d hd τ)
  have hT : DifferentiableOn ℂ (Tleft τ) S := differentiableOn_Tleft τ
  have h : (Wlift ℓ d τ)
      = fun w : ℂ => DeltaFun τ * DeltaFun (UpperHalfPlane.ofComplex w)
          * (AfunFun ℓ d τ (UpperHalfPlane.ofComplex w) - Tleft τ w) := by
    funext w
    simp only [Wlift]
  rw [h]
  exact ((differentiableOn_const (DeltaFun τ)).mul hDelta).mul (hAfun.sub hT)

end Work.Asymptotics.SpikeCircle
