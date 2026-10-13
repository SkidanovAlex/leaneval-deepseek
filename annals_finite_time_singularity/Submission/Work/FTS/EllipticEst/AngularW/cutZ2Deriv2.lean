import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngularW

open scoped Real Topology
open Filter Set

noncomputable section

/-!
## The second derivative of the radial cut-off `cut n`, uniformly bounded after `z ^ 2`

`Work.FTS.EllipticEst.cut n z = ψ ((n+1) z - 1) (1 - ψ (z/(n+1) - 2))` with
`ψ = Real.smoothTransition`, the smooth step which is `0` off `(0,1)` (as are all its
derivatives).  Writing, for `w > 0`,

`cutG w z = ψ (w z - 1) (1 - ψ (z/w - 2))`

(so that `cut n = cutG ((n : ℝ) + 1)`), differentiating `cutG w` by the chain and product
rules gives

`z ^ 2 (cutG w)''(z) = ((w z) ^ 2 ψ''(w z - 1)) (1 - ψ (z/w - 2))
    - 2 ((w z) ψ'(w z - 1)) ((z/w) ψ'(z/w - 2)) - ψ (w z - 1) ((z/w) ^ 2 ψ''(z/w - 2))`

(using `z ^ 2 = (w z) (z/w)` in the middle term).  Each of the three terms is bounded
uniformly in `w > 0` and `z`: the rescaled quantities `(x + 1) ^ k ψ^{(k)}(x)` and
`(x + 2) ^ k ψ^{(k)}(x)`, `k ≤ 2`, are continuous and vanish off `[0,1]`, hence bounded,
while `|ψ| ≤ 1` and `|1 - ψ| ≤ 1`.  This gives `cutZ2Deriv2`.
-/

/-! ### Rescaled derivatives of `Real.smoothTransition` -/

private theorem deriv_sT_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

private theorem deriv_sT_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

private theorem continuous_deriv_deriv_sT :
    Continuous (deriv (deriv Real.smoothTransition)) := by
  have h : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 3)).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h

private theorem deriv_deriv_sT_eq_zero_of_lt {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < -x)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    refine deriv_sT_eq_zero_of_lt ?_
    have := (abs_lt.mp hy).2
    linarith
  rw [h.deriv_eq, deriv_const]

private theorem deriv_deriv_sT_eq_zero_of_gt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < (x - 1) / 2)] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    refine deriv_sT_eq_zero_of_gt ?_
    have := (abs_lt.mp hy).1
    linarith
  rw [h.deriv_eq, deriv_const]

private theorem abs_sT_le_one (x : ℝ) : |Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
  exact Real.smoothTransition.le_one x

private theorem abs_one_sub_sT_le_one (x : ℝ) : |1 - Real.smoothTransition x| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [Real.smoothTransition.le_one x])]
  linarith [Real.smoothTransition.nonneg x]

/-- `x ↦ (x + c) ψ'(x)` is bounded: it is continuous and vanishes off `[0,1]`. -/
private theorem exists_bound_shift_mul_deriv (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c) * deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c) * deriv Real.smoothTransition x) :=
    (continuous_id.add continuous_const).mul
      ((Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num))
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
    · rw [deriv_sT_eq_zero_of_lt hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_sT_eq_zero_of_gt hx, mul_zero, abs_zero]; exact hC0

/-- `x ↦ (x + c) ^ 2 ψ''(x)` is bounded: it is continuous and vanishes off `[0,1]`. -/
private theorem exists_bound_shift_sq_mul_deriv2 (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(x + c)^2 * deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hcont : Continuous (fun x : ℝ => (x + c)^2 * deriv (deriv Real.smoothTransition) x) :=
    ((continuous_id.add continuous_const).pow 2).mul continuous_deriv_deriv_sT
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
    · rw [deriv_deriv_sT_eq_zero_of_lt hx, mul_zero, abs_zero]; exact hC0
    · rw [deriv_deriv_sT_eq_zero_of_gt hx, mul_zero, abs_zero]; exact hC0

/-! ### The cut-off in rescaled form and its first two derivatives -/

/-- The cut-off in rescaled form: `cutG w z = ψ (w z - 1) (1 - ψ (z / w - 2))`. -/
private def cutG (w z : ℝ) : ℝ :=
  Real.smoothTransition (w * z - 1) * (1 - Real.smoothTransition (z / w - 2))

/-- The first derivative of `cutG w`, as given by the chain and product rules. -/
private def dcutG (w y : ℝ) : ℝ :=
  (w * deriv Real.smoothTransition (w * y - 1)) * (1 - Real.smoothTransition (y / w - 2))
    + Real.smoothTransition (w * y - 1)
      * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))

/-- The second derivative of `cutG w` obtained from the product and chain rules. -/
private def rawDD (w y : ℝ) : ℝ :=
  (w * (w * deriv (deriv Real.smoothTransition) (w * y - 1)))
      * (1 - Real.smoothTransition (y / w - 2))
    + (w * deriv Real.smoothTransition (w * y - 1))
      * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))
    - ((w * deriv Real.smoothTransition (w * y - 1))
        * (deriv Real.smoothTransition (y / w - 2) * (1 / w))
      + Real.smoothTransition (w * y - 1)
        * ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w)))

/-- The second derivative of `cutG w`, in simplified form. -/
private def ddcutG (w z : ℝ) : ℝ :=
  w ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1)
      * (1 - Real.smoothTransition (z / w - 2))
    - 2 * (deriv Real.smoothTransition (w * z - 1)
        * deriv Real.smoothTransition (z / w - 2))
    - Real.smoothTransition (w * z - 1)
      * (deriv (deriv Real.smoothTransition) (z / w - 2) / w ^ 2)

private theorem cut_eq_cutG (n : ℕ) :
    Work.FTS.EllipticEst.cut n = cutG ((n : ℝ) + 1) := by
  funext z
  simp only [Work.FTS.EllipticEst.cut, cutG]

/-! ### Chain rules -/

private theorem hasDerivAt_sT_comp (w y : ℝ) :
    HasDerivAt (fun y : ℝ => Real.smoothTransition (w * y - 1))
      (w * deriv Real.smoothTransition (w * y - 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => w * y - 1) w y := by
    have hR : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using ((hasDerivAt_id' y).const_mul w)
    exact hR.sub_const 1
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (w * y - 1)) (w * y - 1) :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv (mul_comm _ _)

private theorem hasDerivAt_deriv_sT_comp (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (w * y - 1))
      (w * deriv (deriv Real.smoothTransition) (w * y - 1)) y := by
  have h1 : HasDerivAt (fun y : ℝ => w * y - 1) w y := by
    have hR : HasDerivAt (fun y : ℝ => w * y) w y := by
      simpa using ((hasDerivAt_id' y).const_mul w)
    exact hR.sub_const 1
  have h2 : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (w * y - 1)) (w * y - 1) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv (mul_comm _ _)

private theorem hasDerivAt_compl_sT (w y : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - Real.smoothTransition (y / w - 2))
      (-(deriv Real.smoothTransition (y / w - 2) * (1 / w))) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / w - 2) (1 / w) y := by
    have hR : HasDerivAt (fun y : ℝ => y / w) (1 / w) y := by
      simpa using (hasDerivAt_id' y).div_const w
    exact hR.sub_const 2
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (y / w - 2)) (y / w - 2) :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt).hasDerivAt
  exact ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub (h2.comp y h1)).congr_deriv (zero_sub _)

private theorem hasDerivAt_deriv_sT_div (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (y / w - 2))
      (deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) y := by
  have h1 : HasDerivAt (fun y : ℝ => y / w - 2) (1 / w) y := by
    have hR : HasDerivAt (fun y : ℝ => y / w) (1 / w) y := by
      simpa using (hasDerivAt_id' y).div_const w
    exact hR.sub_const 2
  have h2 : HasDerivAt (deriv Real.smoothTransition)
      (deriv (deriv Real.smoothTransition) (y / w - 2)) (y / w - 2) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.differentiableAt).hasDerivAt
  exact (h2.comp y h1).congr_deriv rfl

private theorem hasDerivAt_deriv_sT_div_mul (w y : ℝ) :
    HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (y / w - 2) * (1 / w))
      ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w)) y :=
  (hasDerivAt_deriv_sT_div w y).mul_const (1 / w)

/-! ### The two derivatives of `cutG` -/

private theorem hasDerivAt_cutG (w y : ℝ) :
    HasDerivAt (cutG w) (dcutG w y) y := by
  have h := (hasDerivAt_sT_comp w y).mul (hasDerivAt_compl_sT w y)
  have hfun : cutG w = (fun y : ℝ => Real.smoothTransition (w * y - 1))
      * (fun y : ℝ => 1 - Real.smoothTransition (y / w - 2)) := by
    funext y
    simp only [cutG, Pi.mul_apply]
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [dcutG]

private theorem rawDD_eq_ddcutG (w y : ℝ) (hw : w ≠ 0) : rawDD w y = ddcutG w y := by
  have key : ∀ a c d e f B : ℝ,
      (w * (w * a)) * B + (w * c) * (-(d * (1 / w)))
          - ((w * c) * (d * (1 / w)) + e * ((f * (1 / w)) * (1 / w)))
        = w ^ 2 * a * B - 2 * (c * d) - e * (f / w ^ 2) := by
    intro a c d e f B
    field_simp
    ring
  simp only [rawDD, ddcutG]
  exact key _ _ _ _ _ _

private theorem hasDerivAt_dcutG (w y : ℝ) (hw : w ≠ 0) :
    HasDerivAt (dcutG w) (ddcutG w y) y := by
  have hP : HasDerivAt
      (fun y : ℝ => (w * deriv Real.smoothTransition (w * y - 1))
        * (1 - Real.smoothTransition (y / w - 2)))
      ((w * (w * deriv (deriv Real.smoothTransition) (w * y - 1)))
          * (1 - Real.smoothTransition (y / w - 2))
        + (w * deriv Real.smoothTransition (w * y - 1))
          * (-(deriv Real.smoothTransition (y / w - 2) * (1 / w)))) y :=
    ((hasDerivAt_deriv_sT_comp w y).const_mul w).mul (hasDerivAt_compl_sT w y)
  have hQ : HasDerivAt
      (fun y : ℝ => Real.smoothTransition (w * y - 1)
        * (deriv Real.smoothTransition (y / w - 2) * (1 / w)))
      ((w * deriv Real.smoothTransition (w * y - 1))
          * (deriv Real.smoothTransition (y / w - 2) * (1 / w))
        + Real.smoothTransition (w * y - 1)
          * ((deriv (deriv Real.smoothTransition) (y / w - 2) * (1 / w)) * (1 / w))) y :=
    (hasDerivAt_sT_comp w y).mul (hasDerivAt_deriv_sT_div_mul w y)
  have h := hP.sub hQ
  have hfun : dcutG w
      = (fun y : ℝ => (w * deriv Real.smoothTransition (w * y - 1))
            * (1 - Real.smoothTransition (y / w - 2)))
        - (fun y : ℝ => Real.smoothTransition (w * y - 1)
            * (deriv Real.smoothTransition (y / w - 2) * (1 / w))) := by
    funext y
    simp only [dcutG, Pi.sub_apply]
    ring
  rw [hfun]
  refine h.congr_deriv ?_
  exact rawDD_eq_ddcutG w y hw

private theorem deriv_deriv_cutG (w z : ℝ) (hw : w ≠ 0) :
    deriv (deriv (cutG w)) z = ddcutG w z := by
  have h : deriv (cutG w) = dcutG w := funext (fun y => (hasDerivAt_cutG w y).deriv)
  rw [h]
  exact (hasDerivAt_dcutG w z hw).deriv

/-! ### The uniform bound -/

private theorem z2_algebra (w z P Q R A B S : ℝ) (hw : w ≠ 0) :
    z ^ 2 * (w ^ 2 * P * B - 2 * (Q * R) - A * (S / w ^ 2))
      = ((w * z - 1 + 1) ^ 2 * P) * B
        - 2 * ((w * z - 1 + 1) * Q) * ((z / w - 2 + 2) * R)
        - A * ((z / w - 2 + 2) ^ 2 * S) := by
  field_simp
  ring

private theorem z2_mul_ddcutG (w z : ℝ) (hw : w ≠ 0) :
    z ^ 2 * ddcutG w z
      = ((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
          * (1 - Real.smoothTransition (z / w - 2))
        - 2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
          * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))
        - Real.smoothTransition (w * z - 1)
          * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2)) := by
  simp only [ddcutG]
  exact z2_algebra w z _ _ _ _ _ _ hw

private theorem abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a - b - c| ≤ |a - b| + |c| := by
    simpa using abs_sub_le (a - b) 0 c
  have h2 : |a - b| ≤ |a| + |b| := by
    simpa using abs_sub_le a 0 b
  linarith

private theorem bound_ddcutG {C1 C2 CA CB : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ x : ℝ, |(x + 1) * deriv Real.smoothTransition x| ≤ C1)
    (h2 : ∀ x : ℝ, |(x + 2) * deriv Real.smoothTransition x| ≤ C2)
    (hA : ∀ x : ℝ, |(x + 1) ^ 2 * deriv (deriv Real.smoothTransition) x| ≤ CA)
    (hB : ∀ x : ℝ, |(x + 2) ^ 2 * deriv (deriv Real.smoothTransition) x| ≤ CB)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (w z : ℝ) (hw : w ≠ 0) :
    |z ^ 2 * ddcutG w z| ≤ CA + 2 * C1 * C2 + CB := by
  rw [z2_mul_ddcutG w z hw]
  have hX : |((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
      * (1 - Real.smoothTransition (z / w - 2))| ≤ CA := by
    calc |((w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1))
          * (1 - Real.smoothTransition (z / w - 2))|
        = |(w * z - 1 + 1) ^ 2 * deriv (deriv Real.smoothTransition) (w * z - 1)|
          * |1 - Real.smoothTransition (z / w - 2)| := abs_mul _ _
      _ ≤ CA * 1 :=
          mul_le_mul (hA (w * z - 1)) (abs_one_sub_sT_le_one (z / w - 2)) (abs_nonneg _) hCA
      _ = CA := mul_one CA
  have hY : |2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
      * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))| ≤ 2 * C1 * C2 := by
    have h1' : |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)| ≤ C1 :=
      h1 (w * z - 1)
    have h2' : |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)| ≤ C2 :=
      h2 (z / w - 2)
    have hstep : |2 * ((w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1))
        * ((z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2))|
        = (2 * |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)|)
          * |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)| := by
      rw [abs_mul]
      rw [abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [hstep]
    calc (2 * |(w * z - 1 + 1) * deriv Real.smoothTransition (w * z - 1)|)
          * |(z / w - 2 + 2) * deriv Real.smoothTransition (z / w - 2)|
        ≤ (2 * C1) * C2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1' (by norm_num)) h2'
            (abs_nonneg _) (by linarith)
      _ = 2 * C1 * C2 := by ring
  have hZ : |Real.smoothTransition (w * z - 1)
      * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2))| ≤ CB := by
    calc |Real.smoothTransition (w * z - 1)
          * ((z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2))|
        = |Real.smoothTransition (w * z - 1)|
          * |(z / w - 2 + 2) ^ 2 * deriv (deriv Real.smoothTransition) (z / w - 2)| := abs_mul _ _
      _ ≤ 1 * CB :=
          mul_le_mul (abs_sT_le_one _) (hB (z / w - 2)) (abs_nonneg _) zero_le_one
      _ = CB := one_mul CB
  exact le_trans (abs_sub_sub_le _ _ _) (by linarith)

theorem cutZ2Deriv2 : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ z : ℝ,
    |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.cut n)) z| ≤ C := by
  obtain ⟨C1, hC1, h1⟩ := exists_bound_shift_mul_deriv 1
  obtain ⟨C2, hC2, h2⟩ := exists_bound_shift_mul_deriv 2
  obtain ⟨CA, hCA, hA⟩ := exists_bound_shift_sq_mul_deriv2 1
  obtain ⟨CB, hCB, hB⟩ := exists_bound_shift_sq_mul_deriv2 2
  refine ⟨max 1 (CA + 2 * C1 * C2 + CB), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n z
  have hwn : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [cut_eq_cutG n, deriv_deriv_cutG ((n : ℝ) + 1) z hwn]
  exact le_trans (bound_ddcutG hC1 hC2 h1 h2 hA hB hCA hCB ((n : ℝ) + 1) z hwn)
    (le_max_right _ _)

end

end Work.FTS.EllipticEst.AngularW
