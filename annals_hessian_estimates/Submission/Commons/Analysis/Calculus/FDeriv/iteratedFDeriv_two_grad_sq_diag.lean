import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_grad_sq_directional
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_apply_directional
import Submission.Commons.Analysis.Calculus.FDeriv.secondPartial_directional_deriv
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_three_swap
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_iteratedFDeriv_apply

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem iteratedFDeriv_two_grad_sq_diag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s) (i : ι) :
    (iteratedFDeriv ℝ 2 (fun z => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) x) ![v i, v i] =
      2 * (∑ k : ι, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2)
        + 2 * ∑ k : ι, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
  classical
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  -- Smoothness of `z ↦ (fderiv ℝ u z) (v k)` and of the sum.
  have hfdu : ContDiffAt ℝ 2 (fun y => fderiv ℝ u y) x := huAt.fderiv_right (m := 2) (by norm_num)
  have hAcd : ∀ k : ι, ContDiffAt ℝ 2 (fun y : E => (fderiv ℝ u y) (v k)) x := by
    intro k
    have h := (ContinuousLinearMap.apply ℝ ℝ (v k)).contDiff.comp_contDiffAt x hfdu
    convert h using 1
    ext y
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hGcd : ContDiffAt ℝ 2 (fun z => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) x := by
    have hsum := ContDiffAt.sum (s := Finset.univ)
        (f := fun k (z : E) => ((fderiv ℝ u z) (v k)) ^ 2) (fun k _ => (hAcd k).pow 2)
    simpa using hsum
  have hG1 : DifferentiableAt ℝ
      (fderiv ℝ (fun z : E => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2)) x :=
    (hGcd.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  -- Rewrite the second derivative as the derivative of the directional first derivative.
  have hbridge : (iteratedFDeriv ℝ 2
        (fun z => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) x) ![v i, v i]
      = fderiv ℝ (fun y : E =>
          fderiv ℝ (fun z : E => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) y (v i)) x (v i) := by
    rw [iteratedFDeriv_two_apply]
    rw [fderiv_clm_apply hG1 (differentiableAt_const (v i))]
    simp [ContinuousLinearMap.flip_apply]
  -- Abbreviations.
  let A : ι → E → ℝ := fun k y => (fderiv ℝ u y) (v k)
  let B : ι → E → ℝ := fun k y => (iteratedFDeriv ℝ 2 u y) ![v i, v k]
  -- The directional first derivative near `x`.
  have hev : (fun y : E =>
        fderiv ℝ (fun z : E => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) y (v i))
      =ᶠ[𝓝 x] (fun y : E => 2 * ∑ k : ι, A k y * B k y) := by
    filter_upwards [hxmem] with y hy
    rw [fderiv_grad_sq_directional (u := u) (v := v) hs hy hu2 (v i)]
  -- Differentiability of the pieces.
  have hAdiff : ∀ k : ι, DifferentiableAt ℝ (A k) x := fun k =>
    (hAcd k).differentiableAt (by norm_num)
  have hBdiff : ∀ k : ι, DifferentiableAt ℝ (B k) x := fun k =>
    (hasFDerivAt_iteratedFDeriv_apply (u := u) hs hx (n := 2) hu
      (![v i, v k] : Fin 2 → E)).differentiableAt
  -- The derivative of the sum, by product and sum rules.
  have hprod : ∀ k : ι, HasFDerivAt (fun y : E => A k y * B k y)
      (A k x • fderiv ℝ (B k) x + B k x • fderiv ℝ (A k) x) x := fun k =>
    (hAdiff k).hasFDerivAt.mul (hBdiff k).hasFDerivAt
  have hsum : HasFDerivAt (fun y : E => ∑ k : ι, A k y * B k y)
      (∑ k : ι, (A k x • fderiv ℝ (B k) x + B k x • fderiv ℝ (A k) x)) x := by
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => hprod k)
    simpa using this
  have h2 : HasFDerivAt (fun y : E => 2 * ∑ k : ι, A k y * B k y)
      ((2 : ℝ) • (∑ k : ι, (A k x • fderiv ℝ (B k) x + B k x • fderiv ℝ (A k) x))) x :=
    hsum.const_mul 2
  have hLHS : (iteratedFDeriv ℝ 2
        (fun z => ∑ k : ι, ((fderiv ℝ u z) (v k)) ^ 2) x) ![v i, v i]
      = ((2 : ℝ) • (∑ k : ι, (A k x • fderiv ℝ (B k) x + B k x • fderiv ℝ (A k) x))) (v i) := by
    rw [hbridge, hev.fderiv_eq, h2.fderiv]
  -- Evaluate the derivative on `v i`.
  have key : (∑ k : ι, (A k x • fderiv ℝ (B k) x + B k x • fderiv ℝ (A k) x)) (v i)
      = ∑ k : ι, ((fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]
          + ((iteratedFDeriv ℝ 2 u x) ![v i, v k]) ^ 2) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hAd : fderiv ℝ (A k) x (v i) = (iteratedFDeriv ℝ 2 u x) ![v i, v k] := by
      show fderiv ℝ (fun y : E => (fderiv ℝ u y) (v k)) x (v i) = _
      rw [fderiv_fderiv_apply_directional (u := u) hs hx hu2 (z := v i) (w := v k)]
    have hBd : fderiv ℝ (B k) x (v i) = (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k] := by
      show fderiv ℝ (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x (v i) = _
      rw [secondPartial_directional_deriv (u := u) hs hx hu (v i) (v k) (v i)]
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hAd, hBd]
    show (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]
        + (iteratedFDeriv ℝ 2 u x) ![v i, v k] * (iteratedFDeriv ℝ 2 u x) ![v i, v k]
      = (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]
        + ((iteratedFDeriv ℝ 2 u x) ![v i, v k]) ^ 2
    ring
  -- Symmetry of the second and third derivatives.
  have hsymm2 : IsSymmSndFDerivAt ℝ u x :=
    ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) (n := 2) (hu2.contDiffAt hxmem) (by simp)
  have hsym2 : ∀ k : ι, (iteratedFDeriv ℝ 2 u x) ![v i, v k]
      = (iteratedFDeriv ℝ 2 u x) ![v k, v i] := fun k => hsymm2.iteratedFDeriv_cons
  have hsym3 : ∀ k : ι, (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]
      = (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
    intro k
    have h1 := (iteratedFDeriv_three_swap hs hx hu (v i) (v i) (v k)).2
    have h2 := (iteratedFDeriv_three_swap hs hx hu (v i) (v k) (v i)).1
    exact h1.trans h2
  have hsumBsq : ∑ k : ι, ((iteratedFDeriv ℝ 2 u x) ![v i, v k]) ^ 2
      = ∑ k : ι, ((iteratedFDeriv ℝ 2 u x) ![v k, v i]) ^ 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsym2 k]
  have hsumAD3 : ∑ k : ι, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]
      = ∑ k : ι, (fderiv ℝ u x) (v k) * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsym3 k]
  rw [hLHS, smul_apply, smul_eq_mul, key, Finset.sum_add_distrib, mul_add,
    hsumBsq, hsumAD3]
  ring

end Commons.Analysis.Calculus.FDeriv
