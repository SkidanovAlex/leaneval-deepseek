import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_iteratedFDeriv_apply
import Submission.Commons.Analysis.Calculus.FDeriv.secondPartial_directional_deriv

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace
open scoped Topology
open scoped BigOperators

theorem first_deriv_sigma2_coord {v : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
    {u : EuclideanSpace ℝ (Fin 4) → ℝ} {s : Set (EuclideanSpace ℝ (Fin 4))}
    {x : EuclideanSpace ℝ (Fin 4)}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 3 u s) (hx : x ∈ s)
    (hconst : ∀ y ∈ s, (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) = 1)
    (k : Fin 4) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j]
      + (iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j]
      - 2 * ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) * ((iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
      else 0) = 0 := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  -- Differentiability of the coordinate second partials.
  have hTdiff : ∀ a b : Fin 4, DifferentiableAt ℝ
      (fun y => (iteratedFDeriv ℝ 2 u y) ![v a, v b]) x := fun a b =>
    (hasFDerivAt_iteratedFDeriv_apply (u := u) hs hx (n := 2) hu ![v a, v b]).differentiableAt
  have hT : ∀ a b : Fin 4, HasFDerivAt (fun y => (iteratedFDeriv ℝ 2 u y) ![v a, v b])
      (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v a, v b]) x) x :=
    fun a b => (hTdiff a b).hasFDerivAt
  -- Derivative of the sigma-2 coordinate expression.
  have hFhas : HasFDerivAt (fun y => ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0)
      (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u x) ![v i, v i] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v j, v j]) x)
        + (iteratedFDeriv ℝ 2 u x) ![v j, v j] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v i]) x)
        - (2 • ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) ^ (2 - 1)) •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v j]) x)
      else 0) x := by
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ?_)
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ?_)
    by_cases hij : i < j
    · simp only [if_pos hij]
      exact ((hT i i).mul (hT j j)).sub ((hT i j).pow 2)
    · simp only [if_neg hij]
      exact hasFDerivAt_const 0 x
  -- The expression is constant on the open set.
  have hFzero : fderiv ℝ (fun y => ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) x = 0 := by
    have hev : (fun y => ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [hxmem] with y hy
      exact hconst y hy
    rw [Filter.EventuallyEq.fderiv_eq hev]
    simp
  have hval : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u x) ![v i, v i] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v j, v j]) x)
        + (iteratedFDeriv ℝ 2 u x) ![v j, v j] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v i]) x)
        - (2 • ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) ^ (2 - 1)) •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v j]) x)
      else 0) (v k) = 0 := by
    rw [← hFhas.fderiv, hFzero]
    simp
  have hLval : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u x) ![v i, v i] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v j, v j]) x)
        + (iteratedFDeriv ℝ 2 u x) ![v j, v j] •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v i]) x)
        - (2 • ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) ^ (2 - 1)) •
            (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v j]) x)
      else 0) (v k)
      = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j]
      + (iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j]
      - 2 * ((iteratedFDeriv ℝ 2 u x) ![v i, v j]) * ((iteratedFDeriv ℝ 3 u x) ![v k, v i, v j])
      else 0) := by
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij]
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul, pow_one,
        Nat.reduceSub]
      rw [secondPartial_directional_deriv hs hx hu (v j) (v j) (v k),
          secondPartial_directional_deriv hs hx hu (v i) (v i) (v k),
          secondPartial_directional_deriv hs hx hu (v i) (v j) (v k)]
      ring
    · rw [if_neg hij, if_neg hij]
      simp
  rw [← hLval]
  exact hval

end Commons.Analysis.Calculus.FDeriv