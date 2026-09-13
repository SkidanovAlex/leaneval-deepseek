import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.first_deriv_sigma2_coord
import Submission.Commons.Analysis.Calculus.FDeriv.hasFDerivAt_iteratedFDeriv_apply

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace
open scoped BigOperators
open scoped Topology

theorem iteratedFDeriv_directional_deriv_val {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {s : Set E} {x : E} (hs : IsOpen s) (hx : x ∈ s) {n : ℕ}
    (hu : ContDiffOn ℝ (n + 1) u s) (m : Fin n → E) (w : E) :
    fderiv ℝ (fun y => (iteratedFDeriv ℝ n u y) m) x w =
      (iteratedFDeriv ℝ (n + 1) u x) (Fin.cons w m) := by
  rw [(hasFDerivAt_iteratedFDeriv_apply (u := u) hs hx (n := n) hu m).fderiv]
  simp

/- Second-order differentiation of the coordinate form of the sigma_2 equation (Step 1 of
Prop. 2.1, Shankar-Yuan): differentiating the first-order identity of
`first_deriv_sigma2_coord` once more in a direction `v l`.  Suggested proof: the function
`y ↦ sum_{i<j} [ u_kii(y) u_jj(y) + u_ii(y) u_kjj(y) - 2 u_ij(y) u_kij(y) ]` vanishes on the
neighbourhood `s` of `x` by `first_deriv_sigma2_coord`, so its `fderiv` at `x` is `0`
(`Filter.EventuallyEq.fderiv_eq`); compute that `fderiv` with the `Finset` sum/product rules and
`hasFDerivAt_iteratedFDeriv_apply` (for `n = 2` giving the third derivatives and `n = 3` giving
the fourth ones), then evaluate on `v l`. -/
open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem second_deriv_sigma2_coord {v : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
    {u : EuclideanSpace ℝ (Fin 4) → ℝ} {s : Set (EuclideanSpace ℝ (Fin 4))}
    {x : EuclideanSpace ℝ (Fin 4)}
    (hs : IsOpen s) (hu : ContDiffOn ℝ 4 u s) (hx : x ∈ s)
    (hconst : ∀ y ∈ s, (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
        (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j] -
          ((iteratedFDeriv ℝ 2 u y) ![v i, v j]) ^ 2 else 0) = 1)
    (k l : Fin 4) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 4 u x) ![v l, v k, v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j]
      + (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v l, v j, v j]
      + (iteratedFDeriv ℝ 3 u x) ![v l, v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j]
      + (iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 4 u x) ![v l, v k, v j, v j]
      - 2 * (iteratedFDeriv ℝ 3 u x) ![v l, v i, v j] * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j]
      - 2 * (iteratedFDeriv ℝ 2 u x) ![v i, v j] * (iteratedFDeriv ℝ 4 u x) ![v l, v k, v i, v j]
      else 0) = 0 := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have hu3 : ContDiffOn ℝ 3 u s := hu.of_le (by norm_num)
  have hD2 : ∀ a b : Fin 4, HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin 4) => (iteratedFDeriv ℝ 2 u y) ![v a, v b])
      (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v a, v b]) x) x := fun a b =>
    (hasFDerivAt_iteratedFDeriv_apply (u := u) hs hx (n := 2) hu3 ![v a, v b]).differentiableAt.hasFDerivAt
  have hD3 : ∀ a b c : Fin 4, HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin 4) => (iteratedFDeriv ℝ 3 u y) ![v a, v b, v c])
      (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v a, v b, v c]) x) x := fun a b c =>
    (hasFDerivAt_iteratedFDeriv_apply (u := u) hs hx (n := 3) hu ![v a, v b, v c]).differentiableAt.hasFDerivAt
  let g : EuclideanSpace ℝ (Fin 4) → ℝ := fun y => ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 3 u y) ![v k, v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j]
      + (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 3 u y) ![v k, v j, v j]
      - 2 * (iteratedFDeriv ℝ 2 u y) ![v i, v j] * (iteratedFDeriv ℝ 3 u y) ![v k, v i, v j]
      else 0
  let D : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ := ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      ((iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] •
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v j, v j]) x)
        + (iteratedFDeriv ℝ 2 u x) ![v j, v j] •
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v i, v i]) x))
      + ((iteratedFDeriv ℝ 2 u x) ![v i, v i] •
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v j, v j]) x)
        + (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j] •
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v i]) x))
      - ((2 * (iteratedFDeriv ℝ 2 u x) ![v i, v j]) •
          (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v i, v j]) x)
        + (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] •
          ((2 : ℝ) • (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v j]) x)))
      else 0
  have hGhas : HasFDerivAt g D x := by
    dsimp only [g, D]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ?_)
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ?_)
    by_cases hij : i < j
    · simp only [if_pos hij]
      have t1 : HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin 4) =>
            (iteratedFDeriv ℝ 3 u y) ![v k, v i, v i] * (iteratedFDeriv ℝ 2 u y) ![v j, v j])
          ((iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] •
              (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v j, v j]) x)
            + (iteratedFDeriv ℝ 2 u x) ![v j, v j] •
              (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v i, v i]) x)) x :=
        (hD3 k i i).mul (hD2 j j)
      have t2 : HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin 4) =>
            (iteratedFDeriv ℝ 2 u y) ![v i, v i] * (iteratedFDeriv ℝ 3 u y) ![v k, v j, v j])
          ((iteratedFDeriv ℝ 2 u x) ![v i, v i] •
              (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v j, v j]) x)
            + (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j] •
              (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v i]) x)) x :=
        (hD2 i i).mul (hD3 k j j)
      have t3 : HasFDerivAt
          (fun y : EuclideanSpace ℝ (Fin 4) =>
            2 * (iteratedFDeriv ℝ 2 u y) ![v i, v j] * (iteratedFDeriv ℝ 3 u y) ![v k, v i, v j])
          ((2 * (iteratedFDeriv ℝ 2 u x) ![v i, v j]) •
              (fderiv ℝ (fun y => (iteratedFDeriv ℝ 3 u y) ![v k, v i, v j]) x)
            + (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j] •
              ((2 : ℝ) • (fderiv ℝ (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v j]) x))) x :=
        ((hD2 i j).const_mul 2).mul (hD3 k i j)
      exact (t1.add t2).sub t3
    · simp only [if_neg hij]
      exact hasFDerivAt_const 0 x
  have hfder : fderiv ℝ g x = D := hGhas.fderiv
  have hgzero : ∀ y ∈ s, g y = 0 := by
    intro y hy
    dsimp only [g]
    exact first_deriv_sigma2_coord (u := u) (v := v) (x := y) hs hu3 hy hconst k
  have hzero : fderiv ℝ g x = 0 := by
    have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hxmem] with y hy
      exact hgzero y hy
    rw [Filter.EventuallyEq.fderiv_eq hev]
    simp
  have hD0 : D (v l) = 0 := by
    have hDz : D = 0 := by rw [← hfder]; exact hzero
    rw [hDz]; simp
  have hDval : D (v l) = (∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (iteratedFDeriv ℝ 4 u x) ![v l, v k, v i, v i] * (iteratedFDeriv ℝ 2 u x) ![v j, v j]
      + (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v l, v j, v j]
      + (iteratedFDeriv ℝ 3 u x) ![v l, v i, v i] * (iteratedFDeriv ℝ 3 u x) ![v k, v j, v j]
      + (iteratedFDeriv ℝ 2 u x) ![v i, v i] * (iteratedFDeriv ℝ 4 u x) ![v l, v k, v j, v j]
      - 2 * (iteratedFDeriv ℝ 3 u x) ![v l, v i, v j] * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v j]
      - 2 * (iteratedFDeriv ℝ 2 u x) ![v i, v j] * (iteratedFDeriv ℝ 4 u x) ![v l, v k, v i, v j]
      else 0) := by
    dsimp only [D]
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij]
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
      rw [iteratedFDeriv_directional_deriv_val hs hx hu3 (n := 2) (m := ![v j, v j]) (w := v l),
          iteratedFDeriv_directional_deriv_val hs hx hu3 (n := 2) (m := ![v i, v i]) (w := v l),
          iteratedFDeriv_directional_deriv_val hs hx hu (n := 3) (m := ![v k, v i, v i]) (w := v l),
          iteratedFDeriv_directional_deriv_val hs hx hu (n := 3) (m := ![v k, v j, v j]) (w := v l),
          iteratedFDeriv_directional_deriv_val hs hx hu (n := 3) (m := ![v k, v i, v j]) (w := v l),
          iteratedFDeriv_directional_deriv_val hs hx hu3 (n := 2) (m := ![v i, v j]) (w := v l)]
      simp only [Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one, Nat.reduceAdd]
      ring
    · rw [if_neg hij, if_neg hij]
      simp
  rw [← hDval]
  exact hD0

end Commons.Analysis.Calculus.FDeriv
