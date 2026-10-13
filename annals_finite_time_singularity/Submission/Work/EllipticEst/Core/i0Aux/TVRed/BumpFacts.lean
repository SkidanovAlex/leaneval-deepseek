/-
Copyright: work module for the Elgindi finite-time singularity project.

# The trace-matching surrogate and its elementary properties

This file constructs the bump `bumpFun x = smoothTransition (2 - 4x)` (with `IsBump` proved), and
proves the pointwise, support and trace properties of the surrogate
`surrFun ψ F₀ F₁ L θ = F₀ * ψ (θ/L) + F₁ * ψ ((π/2 - θ)/L)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. The explicit bump `ψ x = smoothTransition (2 - 4 x)` -/

/-- The explicit bump: `bumpFun x = smoothTransition (2 - 4x)`, which is `1` for `x ≤ 1/4` and
`0` for `x ≥ 1/2`. -/
noncomputable def bumpFun (x : ℝ) : ℝ := Real.smoothTransition (2 - 4 * x)

lemma bumpFun_contDiff : ContDiff ℝ 2 bumpFun := by
  have h1 : ContDiff ℝ 2 Real.smoothTransition := by
    simpa using Real.smoothTransition.contDiff (n := 2)
  have h2 : ContDiff ℝ 2 (fun x : ℝ => 2 - 4 * x) := by fun_prop
  have h3 := h1.comp h2
  first
  | (change ContDiff ℝ 2 fun x : ℝ => Real.smoothTransition (2 - 4 * x); exact h3)
  | simpa only [bumpFun, Function.comp_def] using h3

lemma bumpFun_eq_one {x : ℝ} (hx : x ≤ 1 / 4) : bumpFun x = 1 := by
  rw [bumpFun]
  exact Real.smoothTransition.one_of_one_le (by linarith)

lemma bumpFun_eq_zero {x : ℝ} (hx : 1 / 2 ≤ x) : bumpFun x = 0 := by
  rw [bumpFun]
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma bumpFun_nonneg (x : ℝ) : 0 ≤ bumpFun x := by
  rw [bumpFun]; exact Real.smoothTransition.nonneg _

lemma bumpFun_le_one (x : ℝ) : bumpFun x ≤ 1 := by
  rw [bumpFun]; exact Real.smoothTransition.le_one _

lemma bumpFun_deriv_eq_zero_left {x : ℝ} (hx : x < 1 / 4) : deriv bumpFun x = 0 := by
  have h : bumpFun =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact bumpFun_eq_one (le_of_lt hy)
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv_eq_zero_right {x : ℝ} (hx : 1 / 2 < x) : deriv bumpFun x = 0 := by
  have h : bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact bumpFun_eq_zero (le_of_lt hy)
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv2_eq_zero_left {x : ℝ} (hx : x < 1 / 4) : deriv (deriv bumpFun) x = 0 := by
  have h : deriv bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact bumpFun_deriv_eq_zero_left hy
  rw [h.deriv_eq]; simp

lemma bumpFun_deriv2_eq_zero_right {x : ℝ} (hx : 1 / 2 < x) : deriv (deriv bumpFun) x = 0 := by
  have h : deriv bumpFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact bumpFun_deriv_eq_zero_right hy
  rw [h.deriv_eq]; simp

lemma bumpFun_continuous_deriv : Continuous (deriv bumpFun) :=
  bumpFun_contDiff.continuous_deriv (by norm_num)

lemma bumpFun_contDiff_one_deriv : ContDiff ℝ 1 (deriv bumpFun) := by
  first
  | exact bumpFun_contDiff.deriv'
  | (have h : ContDiff ℝ 2 bumpFun := bumpFun_contDiff; fun_prop)
  | exact bumpFun_contDiff.deriv' (n := 1)

lemma bumpFun_continuous_deriv2 : Continuous (deriv (deriv bumpFun)) :=
  bumpFun_contDiff_one_deriv.continuous_deriv_one

lemma bumpFun_deriv_bound : ∃ C : ℝ, ∀ x : ℝ, |deriv bumpFun x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn bumpFun_continuous_deriv.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [bumpFun_deriv_eq_zero_left (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)
    · rw [bumpFun_deriv_eq_zero_right (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)

lemma bumpFun_deriv2_bound : ∃ C : ℝ, ∀ x : ℝ, |deriv (deriv bumpFun) x| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn bumpFun_continuous_deriv2.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)
  · have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [bumpFun_deriv2_eq_zero_left (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)
    · rw [bumpFun_deriv2_eq_zero_right (not_le.mp hx)]
      simpa using le_max_right C (0 : ℝ)

/-- **The existence of a bump.** -/
theorem bumpExists : ∃ (ψ : ℝ → ℝ) (C : ℝ), IsBump ψ C := by
  obtain ⟨C1, hC1⟩ := bumpFun_deriv_bound
  obtain ⟨C2, hC2⟩ := bumpFun_deriv2_bound
  refine ⟨bumpFun, max (max C1 C2) 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · exact bumpFun_contDiff
  · intro x
    exact (bumpFun_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  · intro x
    exact (bumpFun_contDiff.differentiable_deriv_two.differentiableAt).hasDerivAt
  · intro x hx; exact bumpFun_eq_one hx
  · intro x hx; exact bumpFun_eq_zero hx
  · exact bumpFun_nonneg
  · exact bumpFun_le_one
  · intro x
    exact le_trans (hC1 x) (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro x
    exact le_trans (hC2 x) (le_trans (le_max_right _ _) (le_max_left _ _))
  · intro x hx; exact bumpFun_deriv_eq_zero_left hx
  · intro x hx; exact bumpFun_deriv_eq_zero_right hx
  · intro x hx; exact bumpFun_deriv2_eq_zero_left hx
  · intro x hx; exact bumpFun_deriv2_eq_zero_right hx

/-! ## 2. The chain rule for the surrogate -/

variable {ψ : ℝ → ℝ} {C F₀ F₁ L : ℝ}

lemma hasDerivAt_div_const (θ : ℝ) (_hL : L ≠ 0) :
    HasDerivAt (fun θ : ℝ => θ / L) (1 / L) θ := by
  simpa using (hasDerivAt_id θ).div_const L

lemma hasDerivAt_pi_div_two_sub_div (θ : ℝ) (hL : L ≠ 0) :
    HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) / L) (-(1 / L)) θ := by
  have h : HasDerivAt (fun y : ℝ => (Real.pi / 2 - y) / L) ((-1) / L) θ := by
    have h' := ((hasDerivAt_const (x := θ) (c := Real.pi / 2)).sub (hasDerivAt_id θ)).div_const L
    convert h' using 1
    all_goals first | (funext y; simp) | ring
  have h2 : (-1 : ℝ) / L = -(1 / L) := by ring
  exact h.congr_deriv h2

lemma hasDerivAt_surr_left (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ψ (θ / L)) (deriv ψ (θ / L) * (1 / L)) θ := by
  have h := (hψ.hasDerivAt (θ / L)).comp θ (hasDerivAt_div_const θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_right (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L))
      (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L))) θ := by
  have h := (hψ.hasDerivAt ((Real.pi / 2 - θ) / L)).comp θ (hasDerivAt_pi_div_two_sub_div θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_deriv (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => deriv ψ (θ / L)) (deriv (deriv ψ) (θ / L) * (1 / L)) θ := by
  have h := (hψ.hasDerivAt_deriv (θ / L)).comp θ (hasDerivAt_div_const θ hL)
  simpa only [Function.comp_def] using h

lemma hasDerivAt_surr_deriv_right (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => deriv ψ ((Real.pi / 2 - θ) / L))
      (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) θ := by
  have h := (hψ.hasDerivAt_deriv ((Real.pi / 2 - θ) / L)).comp θ
    (hasDerivAt_pi_div_two_sub_div θ hL)
  simpa only [Function.comp_def] using h

/-- The first derivative of the surrogate, pointwise (raw form). -/
lemma deriv_surr_eq (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    deriv (surrFun ψ F₀ F₁ L) θ
      = F₀ * (deriv ψ (θ / L) * (1 / L))
        + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L))) := by
  have hfun : surrFun ψ F₀ F₁ L
      = (fun y : ℝ => F₀ * ψ (y / L)) + fun y : ℝ => F₁ * ψ ((Real.pi / 2 - y) / L) := by
    funext y; rfl
  rw [hfun]
  exact (((hasDerivAt_surr_left hψ hL θ).const_mul F₀).add
    ((hasDerivAt_surr_right hψ hL θ).const_mul F₁)).deriv

/-- The second derivative of the surrogate, pointwise (raw form). -/
lemma deriv2_surr_eq (hψ : IsBump ψ C) (hL : L ≠ 0) (θ : ℝ) :
    deriv (deriv (surrFun ψ F₀ F₁ L)) θ
      = F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L)) := by
  have hfun : deriv (surrFun ψ F₀ F₁ L)
      = (fun y : ℝ => F₀ * (deriv ψ (y / L) * (1 / L)))
        + fun y : ℝ => F₁ * (deriv ψ ((Real.pi / 2 - y) / L) * (-(1 / L))) := by
    funext y
    rw [deriv_surr_eq hψ hL y]
    rfl
  rw [hfun]
  have hA : HasDerivAt (fun y : ℝ => F₀ * (deriv ψ (y / L) * (1 / L)))
      (F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)) θ := by
    have h0 : HasDerivAt (fun y : ℝ => F₀ * deriv ψ (y / L))
        (F₀ * (deriv (deriv ψ) (θ / L) * (1 / L))) θ :=
      (hasDerivAt_surr_deriv hψ hL θ).const_mul F₀
    have h1 : HasDerivAt (fun y : ℝ => (F₀ * deriv ψ (y / L)) * (1 / L))
        ((F₀ * (deriv (deriv ψ) (θ / L) * (1 / L))) * (1 / L)) θ :=
      h0.mul_const (1 / L)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  have hB : HasDerivAt (fun y : ℝ => F₁ * (deriv ψ ((Real.pi / 2 - y) / L) * (-(1 / L))))
      (F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))) θ := by
    have h0 : HasDerivAt (fun y : ℝ => F₁ * deriv ψ ((Real.pi / 2 - y) / L))
        (F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L)))) θ :=
      (hasDerivAt_surr_deriv_right hψ hL θ).const_mul F₁
    have h1 : HasDerivAt (fun y : ℝ => (F₁ * deriv ψ ((Real.pi / 2 - y) / L)) * (-(1 / L)))
        ((F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L)))) * (-(1 / L))) θ :=
      h0.mul_const (-(1 / L))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  exact (hA.add hB).deriv

/-! ## 3. Pointwise bounds, support and traces -/

lemma surr_bound (hψ : IsBump ψ C) (θ : ℝ) :
    |surrFun ψ F₀ F₁ L θ| ≤ |F₀| + |F₁| := by
  have h1 : |ψ (θ / L)| ≤ 1 := by
    rw [abs_of_nonneg (hψ.nonneg _)]
    exact hψ.le_one _
  have h2 : |ψ ((Real.pi / 2 - θ) / L)| ≤ 1 := by
    rw [abs_of_nonneg (hψ.nonneg _)]
    exact hψ.le_one _
  calc |surrFun ψ F₀ F₁ L θ| = |F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)| := rfl
    _ ≤ |F₀ * ψ (θ / L)| + |F₁ * ψ ((Real.pi / 2 - θ) / L)| := abs_add_le _ _
    _ = |F₀| * |ψ (θ / L)| + |F₁| * |ψ ((Real.pi / 2 - θ) / L)| := by rw [abs_mul, abs_mul]
    _ ≤ |F₀| * 1 + |F₁| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = |F₀| + |F₁| := by ring

lemma deriv_surr_bound (hψ : IsBump ψ C) (hL : 0 < L) (θ : ℝ) :
    |deriv (surrFun ψ F₀ F₁ L) θ| ≤ C * (|F₀| + |F₁|) / L := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 := hψ.deriv_bound (θ / L)
  have h2 := hψ.deriv_bound ((Real.pi / 2 - θ) / L)
  have hpos : (0 : ℝ) < 1 / L := by positivity
  have hA : |F₀ * (deriv ψ (θ / L) * (1 / L))| ≤ |F₀| * C / L := by
    rw [abs_mul, abs_mul, abs_of_pos hpos]
    have h4 : |F₀| * |deriv ψ (θ / L)| ≤ |F₀| * C :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg F₀)
    calc |F₀| * (|deriv ψ (θ / L)| * (1 / L)) = (|F₀| * |deriv ψ (θ / L)|) * (1 / L) := by ring
      _ ≤ (|F₀| * C) * (1 / L) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos)
      _ = |F₀| * C / L := by ring
  have hB : |F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))| ≤ |F₁| * C / L := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hpos]
    have h4 : |F₁| * |deriv ψ ((Real.pi / 2 - θ) / L)| ≤ |F₁| * C :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg F₁)
    calc |F₁| * (|deriv ψ ((Real.pi / 2 - θ) / L)| * (1 / L))
        = (|F₁| * |deriv ψ ((Real.pi / 2 - θ) / L)|) * (1 / L) := by ring
      _ ≤ (|F₁| * C) * (1 / L) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos)
      _ = |F₁| * C / L := by ring
  calc |F₀ * (deriv ψ (θ / L) * (1 / L)) + F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))|
      ≤ |F₀ * (deriv ψ (θ / L) * (1 / L))| + |F₁ * (deriv ψ ((Real.pi / 2 - θ) / L) * (-(1 / L)))| :=
        abs_add_le _ _
    _ ≤ |F₀| * C / L + |F₁| * C / L := add_le_add hA hB
    _ = C * (|F₀| + |F₁|) / L := by ring

lemma deriv2_surr_bound (hψ : IsBump ψ C) (hL : 0 < L) (θ : ℝ) :
    |deriv (deriv (surrFun ψ F₀ F₁ L)) θ| ≤ C * (|F₀| + |F₁|) / L ^ 2 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 := hψ.deriv2_bound (θ / L)
  have h2 := hψ.deriv2_bound ((Real.pi / 2 - θ) / L)
  have hpos : (0 : ℝ) < 1 / L := by positivity
  have hpos2 : (0 : ℝ) < 1 / L * (1 / L) := mul_pos hpos hpos
  have hA : |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)| ≤ |F₀| * C / L ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hpos]
    have h4 : |F₀| * |deriv (deriv ψ) (θ / L)| ≤ |F₀| * C :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg F₀)
    calc |F₀| * (|deriv (deriv ψ) (θ / L)| * (1 / L)) * (1 / L)
        = (|F₀| * |deriv (deriv ψ) (θ / L)|) * ((1 / L) * (1 / L)) := by ring
      _ ≤ (|F₀| * C) * ((1 / L) * (1 / L)) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos2)
      _ = |F₀| * C / L ^ 2 := by field_simp [ne_of_gt hL] <;> ring
  have hB : |F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))| ≤ |F₁| * C / L ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hpos]
    have h4 : |F₁| * |deriv (deriv ψ) ((Real.pi / 2 - θ) / L)| ≤ |F₁| * C :=
      mul_le_mul_of_nonneg_left h2 (abs_nonneg F₁)
    calc |F₁| * (|deriv (deriv ψ) ((Real.pi / 2 - θ) / L)| * (1 / L)) * (1 / L)
        = (|F₁| * |deriv (deriv ψ) ((Real.pi / 2 - θ) / L)|) * ((1 / L) * (1 / L)) := by ring
      _ ≤ (|F₁| * C) * ((1 / L) * (1 / L)) := mul_le_mul_of_nonneg_right h4 (le_of_lt hpos2)
      _ = |F₁| * C / L ^ 2 := by field_simp [ne_of_gt hL] <;> ring
  calc |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)
        + F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))|
      ≤ |F₀ * (deriv (deriv ψ) (θ / L) * (1 / L)) * (1 / L)|
        + |F₁ * (deriv (deriv ψ) ((Real.pi / 2 - θ) / L) * (-(1 / L))) * (-(1 / L))| := abs_add_le _ _
    _ ≤ |F₀| * C / L ^ 2 + |F₁| * C / L ^ 2 := add_le_add hA hB
    _ = C * (|F₀| + |F₁|) / L ^ 2 := by ring

lemma pi_div_two_L_ge_two (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    (2 : ℝ) ≤ Real.pi / (2 * L) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L)]
  nlinarith [hLp, Real.pi_pos]

lemma sub_div_eq (hL : L ≠ 0) :
    (Real.pi / 2 - L / 4) / L = Real.pi / (2 * L) - 1 / 4 := by
  field_simp <;> ring

lemma deriv_surr_eq_zero_of_lt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [h1, h2]
  ring

lemma deriv_surr_eq_zero_of_gt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : deriv (surrFun ψ F₀ F₁ L) θ = 0 := by
  rw [deriv_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv ψ (θ / L) = 0 := by
    apply hψ.deriv_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : deriv ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  rw [h1, h2]
  ring

lemma deriv2_surr_eq_zero_of_lt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    apply hψ.deriv2_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv2_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [h1, h2]
  ring

lemma deriv2_surr_eq_zero_of_gt (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : deriv (deriv (surrFun ψ F₀ F₁ L)) θ = 0 := by
  rw [deriv2_surr_eq hψ (ne_of_gt hL) θ]
  have h1 : deriv (deriv ψ) (θ / L) = 0 := by
    apply hψ.deriv2_eq_zero_right
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : deriv (deriv ψ) ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.deriv2_eq_zero_left
    rw [div_lt_iff₀ hL]; linarith
  rw [h1, h2]
  ring

lemma surr_eq_on_small (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : θ < L / 4) : surrFun ψ F₀ F₁ L θ = F₀ := by
  have h1 : ψ (θ / L) = 1 := by
    apply hψ.eq_one
    rw [div_le_iff₀ hL]; linarith
  have h2 : ψ ((Real.pi / 2 - θ) / L) = 0 := by
    apply hψ.eq_zero
    have hlt : (Real.pi / 2 - L / 4) / L < (Real.pi / 2 - θ) / L :=
      div_lt_div_of_pos_right (by linarith) hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  rw [surrFun, h1, h2]
  ring

lemma surr_eq_on_large (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    {θ : ℝ} (hθ : Real.pi / 2 - L / 4 < θ) : surrFun ψ F₀ F₁ L θ = F₁ := by
  have h1 : ψ (θ / L) = 0 := by
    apply hψ.eq_zero
    have hlt : (Real.pi / 2 - L / 4) / L < θ / L := div_lt_div_of_pos_right hθ hL
    rw [sub_div_eq (ne_of_gt hL)] at hlt
    have := pi_div_two_L_ge_two hL hLp
    linarith
  have h2 : ψ ((Real.pi / 2 - θ) / L) = 1 := by
    apply hψ.eq_one
    rw [div_le_iff₀ hL]; linarith
  rw [surrFun, h1, h2]
  ring

lemma surr_smooth (hψ : IsBump ψ C) (hL : L ≠ 0) :
    ContDiff ℝ 2 (surrFun ψ F₀ F₁ L) := by
  have hdiv1 : ContDiff ℝ 2 (fun θ : ℝ => θ / L) := by
    have he : (fun θ : ℝ => θ / L) = fun θ : ℝ => θ * (1 / L) := by funext θ; ring
    rw [he]; fun_prop
  have hdiv2 : ContDiff ℝ 2 (fun θ : ℝ => (Real.pi / 2 - θ) / L) := by
    have he : (fun θ : ℝ => (Real.pi / 2 - θ) / L)
        = fun θ : ℝ => (Real.pi / 2 - θ) * (1 / L) := by funext θ; ring
    rw [he]; fun_prop
  have h1 : ContDiff ℝ 2 (fun θ : ℝ => ψ (θ / L)) := hψ.contDiff.comp hdiv1
  have h2 : ContDiff ℝ 2 (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L)) := hψ.contDiff.comp hdiv2
  have h3 : ContDiff ℝ 2 (fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)) :=
    (contDiff_const.mul h1).add (contDiff_const.mul h2)
  have hfun : surrFun ψ F₀ F₁ L
      = fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L) := rfl
  rw [hfun]
  exact h3

lemma surr_tendsto_left (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    Filter.Tendsto (surrFun ψ F₀ F₁ L) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  have hmem : Set.Ioo (0 : ℝ) (L / 4) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Set.Ioo (-1 : ℝ) (L / 4), ?_, ?_⟩
    · exact IsOpen.mem_nhds isOpen_Ioo ⟨by norm_num, by linarith⟩
    · intro x hx; exact ⟨hx.2, hx.1.2⟩
  filter_upwards [hmem] with θ hθ
  first
  | exact surr_eq_on_small hψ hL hLp hθ.2
  | exact (surr_eq_on_small hψ hL hLp hθ.2).symm

lemma surr_tendsto_right (hψ : IsBump ψ C) (hL : 0 < L) (hLp : L ≤ Real.pi / 4) :
    Filter.Tendsto (surrFun ψ F₀ F₁ L)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  have hmem : Set.Ioo (Real.pi / 2 - L / 4) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Ioo (Real.pi / 2 - L / 4) (Real.pi / 2 + 1), ?_, ?_⟩
    · exact IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hLp, Real.pi_pos], by linarith [Real.pi_pos]⟩
    · rintro x ⟨hx1, hx2⟩
      exact ⟨hx1.1, hx2⟩
  filter_upwards [hmem] with θ hθ
  first
  | exact surr_eq_on_large hψ hL hLp hθ.1
  | exact (surr_eq_on_large hψ hL hLp hθ.1).symm

end

end Work.EllipticEst.Core.i0Aux.TVRed
