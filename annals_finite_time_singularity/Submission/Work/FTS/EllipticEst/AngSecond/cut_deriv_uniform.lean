import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

open scoped Topology
open Filter Set

/-!
## Auxiliary facts about `Real.smoothTransition` and its derivative

`ψ = Real.smoothTransition` is `C^∞`, vanishes on `(-∞,0]` and equals `1` on `[1,∞)`.  Hence
`deriv ψ` vanishes off `[0,1]`, so for every `c : ℝ` the function `x ↦ (x + c) · ψ'(x)` is
continuous with support in `[0,1]`, i.e. bounded on `ℝ`.
-/

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

private theorem deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

private theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)

private theorem abs_smoothTransition_le_one (x : ℝ) : |Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem abs_one_sub_smoothTransition_le_one (x : ℝ) :
    |1 - Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [Real.smoothTransition.le_one x])]
  linarith [Real.smoothTransition.nonneg x]

/-- `x ↦ (x + c) · (smoothTransition)' x` is bounded, being continuous with support in `[0,1]`. -/
private theorem exists_bound_shift_mul_deriv_smoothTransition (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c) * deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c) * deriv Real.smoothTransition x) :=
    (continuous_id.add continuous_const).mul continuous_deriv_smoothTransition
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hcont.continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC 0 (by norm_num)
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have h := hC x hx
    rwa [Real.norm_eq_abs] at h
  · simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [deriv_smoothTransition_eq_zero_of_lt_zero hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_smoothTransition_eq_zero_of_one_lt hx, mul_zero, abs_zero]; exact hC0

/-!
## The product rule for `cut n`, in rescaled form

With `t = (n+1)z - 1` and `s = z/(n+1) - 2` one has `(n+1)z = t + 1` and `z/(n+1) = s + 2`, so
`z (cut n)'(z)` rewrites as a difference of two terms of the shape `(t+1)ψ'(t)` and `(s+2)ψ'(s)`.
-/

/-- Product rule for `cut n`: `cut n z = ψ((n+1)z - 1)·(1 - ψ(z/(n+1) - 2))`, so the chain
rule and the product rule give
`(cut n)'(z) = (n+1)ψ'((n+1)z-1)·(1-ψ(z/(n+1)-2)) - ψ((n+1)z-1)·ψ'(z/(n+1)-2)/(n+1)`. -/
private theorem hasDerivAt_cut_aux (n : ℕ) (z : ℝ) :
    HasDerivAt (cut n)
      (((n + 1 : ℝ) * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
        - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2) * (1 / (n + 1 : ℝ)))) z := by
  have hψ : ∀ u : ℝ, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u := fun u =>
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt.hasDerivAt
  have hg1 : HasDerivAt (fun y : ℝ => (n + 1 : ℝ) * y - 1) ((n + 1 : ℝ)) z := by
    simpa using ((hasDerivAt_id z).const_mul ((n + 1 : ℝ))).sub_const 1
  have h1 : HasDerivAt (Real.smoothTransition ∘ fun y : ℝ => (n + 1 : ℝ) * y - 1)
      (deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1) * (n + 1 : ℝ)) z :=
    (hψ ((n + 1 : ℝ) * z - 1)).comp z hg1
  have hg2 : HasDerivAt (fun y : ℝ => y / (n + 1 : ℝ) - 2) (1 / (n + 1 : ℝ)) z := by
    simpa using ((hasDerivAt_id z).div_const ((n + 1 : ℝ))).sub_const 2
  have h2 : HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y / (n + 1 : ℝ) - 2))
      (-(deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2) * (1 / (n + 1 : ℝ)))) z := by
    have h := (hasDerivAt_const (x := z) (c := (1 : ℝ))).sub
      ((hψ (z / (n + 1 : ℝ) - 2)).comp z hg2)
    convert h using 1
    · ext y; simp [Pi.sub_apply, Function.comp_apply]
    · ring
  have hfun : cut n = (Real.smoothTransition ∘ fun y : ℝ => (n + 1 : ℝ) * y - 1)
      * (fun y : ℝ => 1 - Real.smoothTransition (y / (n + 1 : ℝ) - 2)) := by
    funext y
    simp [cut, Function.comp_apply, Pi.mul_apply]
  rw [hfun]
  convert h1.mul h2 using 1
  simp only [Function.comp_apply]
  ring

private theorem deriv_cut_mul_self (n : ℕ) (z : ℝ) :
    z * deriv (cut n) z
      = ((((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
        - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2)) := by
  rw [(hasDerivAt_cut_aux n z).deriv]
  ring

/-- The uniform bound: `|z · (cut n)'(z)| ≤ C₁ + C₂` where `C₁, C₂` bound `(t+1)ψ'(t)` resp.
`(t+2)ψ'(t)`. -/
private theorem abs_z_mul_deriv_cut_le (n : ℕ) (z : ℝ) {C1 C2 : ℝ} (hC1 : 0 ≤ C1)
    (h1 : ∀ x : ℝ, |(x + 1) * deriv Real.smoothTransition x| ≤ C1)
    (hC2 : 0 ≤ C2) (h2 : ∀ x : ℝ, |(x + 2) * deriv Real.smoothTransition x| ≤ C2) :
    |z * deriv (cut n) z| ≤ C1 + C2 := by
  rw [deriv_cut_mul_self]
  have hA : |((((n + 1 : ℝ) * z - 1) + 1)
        * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
      * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C1 := by
    have h1' : |(((n + 1 : ℝ) * z - 1) + 1)
        * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1)| ≤ C1 := h1 _
    have h2' : |1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)| ≤ 1 :=
      abs_one_sub_smoothTransition_le_one _
    calc |((((n + 1 : ℝ) * z - 1) + 1)
          * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
        * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        = |(((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1)|
          * |1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)| := abs_mul _ _
      _ ≤ C1 * 1 := mul_le_mul h1' h2' (abs_nonneg _) hC1
      _ = C1 := mul_one C1
  have hB : |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
      * (((z / (n + 1 : ℝ) - 2) + 2)
          * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C2 := by
    have h1' : |Real.smoothTransition ((n + 1 : ℝ) * z - 1)| ≤ 1 :=
      abs_smoothTransition_le_one _
    have h2' : |(((z / (n + 1 : ℝ) - 2) + 2)
        * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| ≤ C2 := h2 _
    calc |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        = |Real.smoothTransition ((n + 1 : ℝ) * z - 1)|
          * |(((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| := abs_mul _ _
      _ ≤ 1 * C2 := mul_le_mul h1' h2' (abs_nonneg _) zero_le_one
      _ = C2 := one_mul C2
  calc |((((n + 1 : ℝ) * z - 1) + 1)
          * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
        * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))
      - Real.smoothTransition ((n + 1 : ℝ) * z - 1)
        * (((z / (n + 1 : ℝ) - 2) + 2)
            * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
      ≤ |((((n + 1 : ℝ) * z - 1) + 1)
            * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
          * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2))|
        + |Real.smoothTransition ((n + 1 : ℝ) * z - 1)
          * (((z / (n + 1 : ℝ) - 2) + 2)
              * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2))| := by
        simpa using abs_sub_le
          (((((n + 1 : ℝ) * z - 1) + 1)
              * deriv Real.smoothTransition ((n + 1 : ℝ) * z - 1))
            * (1 - Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
          (0 : ℝ)
          (Real.smoothTransition ((n + 1 : ℝ) * z - 1)
            * (((z / (n + 1 : ℝ) - 2) + 2)
                * deriv Real.smoothTransition (z / (n + 1 : ℝ) - 2)))
    _ ≤ C1 + C2 := add_le_add hA hB

/-!
## Eventual constancy of `cut n` near a fixed non-zero point
-/

private theorem eventually_two_div_add_one_lt {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, 2 / ((n : ℝ) + 1) < z := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    simpa only [mul_zero, mul_one_div] using ht
  exact (tendsto_order.1 h).2 z hz

private theorem eventually_le_two_mul_add_one (z : ℝ) :
    ∀ᶠ n : ℕ in atTop, z ≤ 2 * ((n : ℝ) + 1) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds
  exact (tendsto_atTop.1 (hbase.const_mul_atTop (by norm_num))) z

private theorem cut_eventuallyEq_one_of_pos {z : ℝ} (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, cut n =ᶠ[𝓝 z] (fun _ => (1 : ℝ)) := by
  filter_upwards [eventually_two_div_add_one_lt hz,
    eventually_le_two_mul_add_one (z + 1)] with n hn1 hn2
  have hlt1 : 2 / ((n : ℝ) + 1) < z := hn1
  have hlt2 : z < 2 * ((n : ℝ) + 1) := by linarith
  have hε : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) / 2 := by
    have hmin : 0 < min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z) :=
      lt_min (by linarith) (by linarith)
    linarith
  filter_upwards [Metric.ball_mem_nhds z hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  refine cut_eq_one_of_mem n ?_ ?_
  · have hm : min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
        ≤ z - 2 / ((n : ℝ) + 1) := min_le_left _ _
    have h1 : z - y ≤ |y - z| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · have hm : min (z - 2 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1) - z)
        ≤ 2 * ((n : ℝ) + 1) - z := min_le_right _ _
    have h1 : y - z ≤ |y - z| := le_abs_self _
    linarith

private theorem cut_eventuallyEq_zero_of_neg {z : ℝ} (hz : z < 0) :
    ∀ᶠ n : ℕ in atTop, cut n =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
  filter_upwards with n
  have hε : 0 < -(z / 2) := by linarith
  filter_upwards [Metric.ball_mem_nhds z hε] with y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have h1 : y - z ≤ |y - z| := le_abs_self _
  have hy0 : y < 0 := by linarith
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact cut_apply_zero_of_le n (by linarith)

/-- For every fixed `z ≠ 0` the derivatives `(cut n)'(z)` vanish for all large `n`. -/
private theorem deriv_cut_eventually_eq_zero {z : ℝ} (hz : z ≠ 0) :
    ∀ᶠ n : ℕ in atTop, deriv (cut n) z = 0 := by
  rcases lt_or_gt_of_ne hz with h | h
  · filter_upwards [cut_eventuallyEq_zero_of_neg h] with n hn
    rw [hn.deriv_eq, deriv_const]
  · filter_upwards [cut_eventuallyEq_one_of_pos h] with n hn
    rw [hn.deriv_eq, deriv_const]

/-!
## The lemma
-/

/-- **Uniform bounds and limits for the radial cut-offs `cut n` of the truncation argument**
(`cut n z = smoothTransition ((n+1)z - 1) (1 - smoothTransition (z/(n+1) - 2))`, equal to `1`
on `[2/(n+1), 2(n+1)]` and vanishing outside `(1/(n+1), 3(n+1))`; all in
`Submission.Work.FTS.EllipticEst.interpol_trunc_defs`).

There is `K > 0` with, for every `n` and every `z`, `|z · deriv (cut n) z| ≤ K`; moreover for
every fixed `z` with `0 < z` the cut-offs converge to `1` and the scaled derivatives to `0`:
`cut n z → 1` and `z · deriv (cut n) z → 0` as `n → ∞`.

Route: the product rule on the two `smoothTransition` factors gives
`z (cut n)'(z) = [(n+1)z·ψ'((n+1)z-1)]·(1-ψ(s)) - ψ(t)·[z ψ'(s)/(n+1)]` with
`t = (n+1)z - 1`, `s = z/(n+1) - 2`; since `(n+1)z = t+1` and `z/(n+1) = s+2`, the
constant `K := sup |(t+1)ψ'(t)| + sup |(t+2)ψ'(t)|` works (`deriv ψ` is continuous with
compact support).  For fixed `z > 0` and large `n` one has `cut n ≡ 1` on a neighbourhood
of `z` (`cut_eq_one_of_mem`), hence `deriv (cut n) z = 0`. -/
theorem cut_deriv_uniform : ∃ K : ℝ, 0 < K ∧
    (∀ n : ℕ, ∀ z : ℝ, |z * deriv (Work.FTS.EllipticEst.cut n) z| ≤ K)
    ∧ (∀ z : ℝ, 0 < z → Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1))
    ∧ (∀ z : ℝ, Filter.Tendsto (fun n : ℕ => z * deriv (Work.FTS.EllipticEst.cut n) z) Filter.atTop (nhds 0)) := by
  obtain ⟨C1, hC1, h1⟩ := exists_bound_shift_mul_deriv_smoothTransition 1
  obtain ⟨C2, hC2, h2⟩ := exists_bound_shift_mul_deriv_smoothTransition 2
  refine ⟨max 1 (C1 + C2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_, ?_, ?_⟩
  · intro n z
    exact le_trans (abs_z_mul_deriv_cut_le n z hC1 h1 hC2 h2) (le_max_right _ _)
  · intro z hz
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [cut_eventuallyEq_one_of_pos hz] with n hn
    exact hn.eq_of_nhds.symm
  · intro z
    by_cases hz : z = 0
    · subst hz
      simpa using (tendsto_const_nhds (x := (0 : ℝ)))
    · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
      filter_upwards [deriv_cut_eventually_eq_zero hz] with n hn
      simp [hn]

end Work.FTS.EllipticEst.AngSecond
