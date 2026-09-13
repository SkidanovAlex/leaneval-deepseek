import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem second_fderiv_laplacian_diag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 4 u s) (i : ι) :
    (iteratedFDeriv ℝ 2 (fun z => (Laplacian.laplacian u) z) x) ![v i, v i] =
      ∑ k : ι, (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k] := by
  have hsx : s ∈ 𝓝 x := hs.mem_nhds hx
  have hu4 : ContDiffAt ℝ 4 u x := hu.contDiffAt hsx
  -- Abbreviate the summands appearing in the orthonormal-basis formula for the Laplacian.
  set g : ι → E → ℝ := fun k z => (iteratedFDeriv ℝ 2 u z) ![v k, v k] with hg
  -- The Laplacian is, pointwise, the sum of the second derivatives in the basis directions.
  have hlap : (fun z => (Laplacian.laplacian u) z) = fun z => ∑ k, g k z := by
    funext z
    have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v) z
    simp only [hg]
    simpa using h
  have hA2 : ContDiffAt ℝ 2 (iteratedFDeriv ℝ 2 u) x :=
    hu4.iteratedFDeriv_right (i := 2) (m := 2) (by norm_num)
  -- Each summand `g k` is `C²` at `x`, as the composition of `z ↦ D²u(z)` with evaluation.
  have hgc : ∀ k : ι, ContDiffAt ℝ 2 (g k) x := by
    intro k
    have h1 : ContDiffAt ℝ 2 (fun z => (iteratedFDeriv ℝ 2 u z) ![v k, v k]) x :=
      ContDiff.comp_contDiffAt x
        (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v k, v k]).contDiff hA2
    simpa only [hg] using h1
  -- The second derivative of a finite sum is the sum of the second derivatives.
  have hA2sum : iteratedFDeriv ℝ 2 (fun z => ∑ k : ι, g k z) x
      = ∑ k : ι, iteratedFDeriv ℝ 2 (g k) x := by
    have h := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (n := 2) (x := x) (u := Finset.univ) (f := g)
      (fun k _ => hgc k)
    simpa using h
  rw [hlap, hA2sum, sum_apply]
  -- It remains to identify each summand.
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hgc_k : ContDiffAt ℝ 2 (g k) x := hgc k
  have hfdg : DifferentiableAt ℝ (fderiv ℝ (g k)) x :=
    (hgc_k.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hA3d : DifferentiableAt ℝ (iteratedFDeriv ℝ 3 u) x :=
    hu4.differentiableAt_iteratedFDeriv (m := 3) (by norm_num)
  -- On a neighbourhood of `x`, the third derivative of `u` in the directions `(v i, v k, v k)`
  -- coincides with the first derivative of `g k` in the direction `v i`.
  have hev : (fun y => iteratedFDeriv ℝ 3 u y ![v i, v k, v k]) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (g k) y (v i)) := by
    filter_upwards [hsx] with y hy
    have huy : ContDiffAt ℝ 4 u y := hu.contDiffAt (hs.mem_nhds hy)
    have hdy : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) y :=
      huy.differentiableAt_iteratedFDeriv (m := 2) (by norm_num)
    rw [iteratedFDeriv_succ_apply_left]
    simp only [hg]
    rw [fderiv_continuousMultilinear_apply_const_apply hdy]
    simp
  calc
    (iteratedFDeriv ℝ 2 (g k) x) ![v i, v i]
        = (fderiv ℝ (fderiv ℝ (g k)) x) (v i) (v i) := by
          rw [iteratedFDeriv_two_apply]; simp
    _ = (fderiv ℝ (fun y => fderiv ℝ (g k) y (v i)) x) (v i) := by
          rw [fderiv_clm_apply hfdg (differentiableAt_const (v i))]
          simp [ContinuousLinearMap.flip_apply]
    _ = (fderiv ℝ (fun y => iteratedFDeriv ℝ 3 u y ![v i, v k, v k]) x) (v i) := by
          rw [← hev.fderiv_eq]
    _ = (iteratedFDeriv ℝ 4 u x) ![v i, v i, v k, v k] := by
          have h := hA3d.iteratedFDeriv_succ_apply_left' (n := 3) (m := ![v i, v i, v k, v k])
          simpa using h.symm

end Commons.Analysis.Calculus.FDeriv