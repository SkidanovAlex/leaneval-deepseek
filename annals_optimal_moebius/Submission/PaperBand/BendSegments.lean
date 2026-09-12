import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Submission.PaperBand.SecondDeriv

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix
open InnerProductGeometry

set_option autoImplicit false
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Straight bend segments (kernel-direction segments of the band)

(Roadmap item (1), continue.)  These are the geometric consequences of the
second-derivative bridge (`Submission.PaperBand.SecondDeriv`):  on a
*straight segment of the flat band* whose direction `v` is a kernel direction
of the shape operator at every point of the segment (`dN f y v = 0`), the
unit normal is constant along the segment and the immersion `f` is affine on
it — so such a segment is a **pre-bend** and its image a straight **bend**
(paper §2.1).

The proofs are one-dimensional analysis along `s ↦ x + s • v`, using the
interval versions of the mean value theorem for functions `ℝ → ℝ³`
(`Mathlib.Analysis.Calculus.MeanValue`):  a function with zero (right)
derivative on `[A,B]` is constant there; two functions with equal
(right) derivatives on `[A,B]` and equal at `A` coincide.
-/

noncomputable section
namespace Submission.PaperBand

/-- The derivative of the affine parameterisation `s ↦ x + s • v` of a
straight segment of the flat band is the direction `v`. -/
lemma hasDerivAt_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (s : ℝ) : HasDerivAt (fun t : ℝ => x + t • v) v s := by
  have hmain : HasDerivAt (fun t : ℝ => t • v) v s := by
    simpa using (HasDerivAt.smul_const (hasDerivAt_id s) v)
  exact HasDerivAt.const_add x hmain

/-- The derivative of an affine function `s ↦ y₀ + (s − A) • c`. -/
lemma hasDerivAt_affine_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y₀ : E) (A : ℝ) (c : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => y₀ + (t - A) • c) c s := by
  have hmain := hasDerivAt_segment (x := y₀ + (-A) • c) (v := c) s
  have hEq : (fun t : ℝ => y₀ + (t - A) • c) = fun t : ℝ => (y₀ + (-A) • c) + t • c := by
    funext t
    rw [sub_eq_add_neg, add_smul]
    abel
  rwa [hEq]

/-- The unit normal is `C^∞` (hence differentiable) at every point of the
interior of the strip. -/
lemma differentiableAt_unitNormal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, DifferentiableAt ℝ (fun y : ℝ² => unitNormal f y) x := by
  intro x hx
  exact ((contDiffOn_unitNormal hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- The derivative family `y ↦ fderiv f y v` is differentiable at every point
of the interior of the strip. -/
lemma differentiableAt_fderiv_apply {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, ∀ v : ℝ²,
      DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ f y v) x := by
  intro x hx v
  have hdA : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ f y !₂[1, 0]) x :=
    differentiableAt_fderiv_dir₀ hf x hx
  have hdB : DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ f y !₂[0, 1]) x :=
    differentiableAt_fderiv_dir₁ hf x hx
  have hmain : DifferentiableAt ℝ (fun y : ℝ² =>
      (v 0) • (fderiv ℝ f y !₂[1, 0]) + (v 1) • (fderiv ℝ f y !₂[0, 1])) x :=
    (hdA.const_smul (v 0)).add (hdB.const_smul (v 1))
  have hEq : (fun y : ℝ² => fderiv ℝ f y v) =ᶠ[𝓝 x] (fun y : ℝ² =>
      (v 0) • (fderiv ℝ f y !₂[1, 0]) + (v 1) • (fderiv ℝ f y !₂[0, 1])) := by
    filter_upwards with y
    exact fderiv_apply_vec_decomp (f := f) y v
  exact hmain.congr_of_eventuallyEq hEq

/-- The normal is **constant along a kernel segment**: if every point of the
straight segment `{x + s • v | s ∈ [A,B]}` lies in the interior of the band
and has `v` in the kernel of the shape operator there, then the unit normal
of the image is the same at every point of the segment. -/
lemma normal_const_on_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x v : ℝ²} {A B : ℝ}
    (hseg : ∀ s ∈ Set.Icc A B, x + s • v ∈ stripInterior)
    (hk : ∀ s ∈ Set.Icc A B, dN f (x + s • v) v = 0) :
    ∀ s ∈ Set.Icc A B, unitNormal f (x + s • v) = unitNormal f (x + A • v) := by
  intro s₀ hs₀
  have hdiffAt : ∀ s ∈ Set.Icc A B, DifferentiableAt ℝ
      (fun t : ℝ => unitNormal f (x + t • v)) s := by
    intro s hs
    exact DifferentiableAt.comp (g := fun y : ℝ² => unitNormal f y)
      (f := fun t : ℝ => x + t • v) (x := s)
      (differentiableAt_unitNormal hf (x + s • v) (hseg s hs))
      (hasDerivAt_segment x v s).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => unitNormal f (x + t • v)) (Set.Icc A B) := by
    intro s hs
    exact (hdiffAt s hs).continuousAt.continuousWithinAt
  have hder0 : ∀ s ∈ Set.Ico A B, HasDerivWithinAt
      (fun t : ℝ => unitNormal f (x + t • v)) 0 (Set.Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc A B := Set.Ico_subset_Icc_self hs
    have hdN : HasFDerivAt (fun y : ℝ² => unitNormal f y) (dN f (x + s • v)) (x + s • v) := by
      have hd := (differentiableAt_unitNormal hf (x + s • v) (hseg s hsIcc)).hasFDerivAt
      rw [show fderiv ℝ (fun y : ℝ² => unitNormal f y) (x + s • v) = dN f (x + s • v) by
            exact (dN_eq_fderiv (f := f) (hseg s hsIcc)).symm] at hd
      exact hd
    have hch := HasFDerivAt.comp_hasDerivAt (x := s) hdN (hasDerivAt_segment x v s)
    have hzero : (dN f (x + s • v)) v = 0 := hk s hsIcc
    rw [hzero] at hch
    exact hch.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero (a := A) (b := B) hcont hder0
  exact hconst s₀ hs₀

/-- The tangent map along a kernel segment is **constant**: if every point of
the straight segment `{x + s • v | s ∈ [A,B]}` has `v` in the kernel of the
shape operator there, then `fderiv f y v` is the same at every point of the
segment (the second-derivative bridge `secondDeriv_vec_zero_all`). -/
lemma tangent_const_on_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x v : ℝ²} {A B : ℝ}
    (hseg : ∀ s ∈ Set.Icc A B, x + s • v ∈ stripInterior)
    (hk : ∀ s ∈ Set.Icc A B, dN f (x + s • v) v = 0) :
    ∀ s ∈ Set.Icc A B, fderiv ℝ f (x + s • v) v = fderiv ℝ f (x + A • v) v := by
  intro s₀ hs₀
  have hdiffAt : ∀ s ∈ Set.Icc A B, DifferentiableAt ℝ
      (fun t : ℝ => fderiv ℝ f (x + t • v) v) s := by
    intro s hs
    exact DifferentiableAt.comp (g := fun y : ℝ² => fderiv ℝ f y v)
      (f := fun t : ℝ => x + t • v) (x := s)
      (differentiableAt_fderiv_apply hf (x + s • v) (hseg s hs) v)
      (hasDerivAt_segment x v s).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ f (x + t • v) v) (Set.Icc A B) := by
    intro s hs
    exact (hdiffAt s hs).continuousAt.continuousWithinAt
  have hder0 : ∀ s ∈ Set.Ico A B, HasDerivWithinAt
      (fun t : ℝ => fderiv ℝ f (x + t • v) v) 0 (Set.Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc A B := Set.Ico_subset_Icc_self hs
    have hdG : HasFDerivAt (fun y : ℝ² => fderiv ℝ f y v)
        (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) (x + s • v)) (x + s • v) :=
      (differentiableAt_fderiv_apply hf (x + s • v) (hseg s hsIcc) v).hasFDerivAt
    have hch := HasFDerivAt.comp_hasDerivAt (x := s) hdG (hasDerivAt_segment x v s)
    have hzero : (fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) (x + s • v)) v = 0 := by
      exact secondDeriv_vec_zero_all hf (x + s • v) (hseg s hsIcc) v (hk s hsIcc) v
    rw [hzero] at hch
    exact hch.hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero (a := A) (b := B) hcont hder0
  have hmain := hconst s₀ hs₀
  -- hmain : fderiv ℝ f (x + s₀ • v) v = fderiv ℝ f (x + A • v) v
  exact hmain

/-- **Affineness of a kernel segment**: if every point of the straight
segment `{x + s • v | s ∈ [A,B]}` of the flat band has `v` in the kernel of
the shape operator there, then the image of the segment is the straight line
segment with the same endpoints:

    f (x + s • v) = f (x + A • v) + (s − A) • fderiv f (x + A • v) v.  -/
lemma affine_on_kernel_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x v : ℝ²} {A B : ℝ}
    (hseg : ∀ s ∈ Set.Icc A B, x + s • v ∈ stripInterior)
    (hk : ∀ s ∈ Set.Icc A B, dN f (x + s • v) v = 0) :
    ∀ s ∈ Set.Icc A B,
      f (x + s • v) = f (x + A • v) + (s - A) • (fderiv ℝ f (x + A • v) v) := by
  intro s₀ hs₀
  let c : ℝ³ := fderiv ℝ f (x + A • v) v
  have hdiffAt_h : ∀ s ∈ Set.Icc A B, DifferentiableAt ℝ
      (fun t : ℝ => f (x + t • v)) s := by
    intro s hs
    exact DifferentiableAt.comp (g := f)
      (f := fun t : ℝ => x + t • v) (x := s)
      (((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
        (x + s • v) (hseg s hs)).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen (hseg s hs)))
      (hasDerivAt_segment x v s).differentiableAt
  have hcont_h : ContinuousOn (fun t : ℝ => f (x + t • v)) (Set.Icc A B) := by
    intro s hs
    exact (hdiffAt_h s hs).continuousAt.continuousWithinAt
  have hcont_g : ContinuousOn (fun t : ℝ => f (x + A • v) + (t - A) • c) (Set.Icc A B) := by
    intro s hs
    exact ((hasDerivAt_affine_sub (y₀ := f (x + A • v)) A c s).differentiableAt.continuousAt
      ).continuousWithinAt
  have hder_h : ∀ s ∈ Set.Ico A B, HasDerivWithinAt
      (fun t : ℝ => f (x + t • v)) c (Set.Ici s) s := by
    intro s hs
    have hsIcc : s ∈ Set.Icc A B := Set.Ico_subset_Icc_self hs
    have hdF : HasFDerivAt f (fderiv ℝ f (x + s • v)) (x + s • v) :=
      (((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
        (x + s • v) (hseg s hsIcc)).differentiableAt
        (IsOpen.mem_nhds stripInterior_isOpen (hseg s hsIcc))).hasFDerivAt
    have hch := HasFDerivAt.comp_hasDerivAt (x := s) hdF (hasDerivAt_segment x v s)
    have hcv : fderiv ℝ f (x + s • v) v = c := by
      dsimp [c]
      exact tangent_const_on_kernel_segment hf hseg hk s hsIcc
    rw [hcv] at hch
    exact hch.hasDerivWithinAt
  have hder_g : ∀ s ∈ Set.Ico A B, HasDerivWithinAt
      (fun t : ℝ => f (x + A • v) + (t - A) • c) c (Set.Ici s) s := by
    intro s hs
    exact ((hasDerivAt_affine_sub (y₀ := f (x + A • v)) A c s).hasDerivWithinAt (s := Set.Ici s))
  have hstart : (fun t : ℝ => f (x + t • v)) A =
      (fun t : ℝ => f (x + A • v) + (t - A) • c) A := by
    simp
  have heq := eq_of_has_deriv_right_eq (a := A) (b := B)
    (f := fun t : ℝ => f (x + t • v))
    (g := fun t : ℝ => f (x + A • v) + (t - A) • c)
    hder_h hder_g hcont_h hcont_g hstart
  have : f (x + s₀ • v) = f (x + A • v) + (s₀ - A) • c := by
    simpa using heq s₀ hs₀
  simpa [c] using this

end Submission.PaperBand
end
