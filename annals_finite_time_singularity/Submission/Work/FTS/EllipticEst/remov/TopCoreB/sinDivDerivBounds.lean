import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.TopCoreB

open Set Filter
open scoped BigOperators

/-- `Real.sinc` (the continuous extension of `sin x / x`) is smooth at every point
of the interval `(-1, 1)`.  This is proved through analyticity: `sinc = dslope sin 0`
is analytic at `0` (the `dslope` of an analytic function is analytic), and away from
`0` it is the quotient of two analytic functions with nonvanishing denominator. -/
lemma contDiffAt_sinc {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n Real.sinc x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have h : AnalyticAt ℝ (dslope Real.sin 0) (0 : ℝ) := by
      obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
      exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    rw [← Real.sinc_eq_dslope] at h
    exact h.contDiffAt
  · have h1 : ContDiffAt ℝ n (Real.sin / id) x :=
      (Real.analyticAt_sin (x := x)).contDiffAt.div (analyticAt_id (z := x)).contDiffAt hx0
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hx0] with y hy
    show Real.sinc y = Real.sin y / y
    exact Real.sinc_of_ne_zero hy

/-- `Real.sinc` does not vanish on `(-1, 1)`. -/
lemma sinc_ne_zero_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : Real.sinc x ≠ 0 := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_trichotomy x 0 with h | h | h
  · rw [← Real.sinc_neg, Real.sinc_of_ne_zero (show (-x : ℝ) ≠ 0 by linarith)]
    refine div_ne_zero (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_gt_three])).ne' (by linarith)
  · subst h; simp
  · rw [Real.sinc_of_ne_zero (show x ≠ 0 by linarith)]
    refine div_ne_zero (Real.sin_pos_of_pos_of_lt_pi h (by linarith [hx2, Real.pi_gt_three])).ne' (by linarith)

/-- On `(0, π/8]` the function `x / sin x` coincides with the reciprocal of `Real.sinc`. -/
lemma eventually_sincInv_eq {x : ℝ} (hx : 0 < x) :
    (fun y : ℝ => (Real.sinc y)⁻¹) =ᶠ[nhds x] fun y : ℝ => y / Real.sin y := by
  filter_upwards [eventually_ne_nhds hx.ne'] with y hy
  rw [Real.sinc_of_ne_zero hy, inv_div]

theorem sinDivDerivBounds (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ i ≤ N, ∀ x ∈ Set.Ioc (0 : ℝ) (Real.pi / 8),
      |iteratedDeriv i (fun x : ℝ => x / Real.sin x) x| ≤ K := by
  have hsub : Icc (0 : ℝ) (Real.pi / 8) ⊆ Ioo (-1 : ℝ) 1 :=
    Set.Icc_subset_Ioo (by norm_num) (by linarith [Real.pi_lt_four])
  -- The reciprocal of `sinc` is `C^N` on the open interval `(-1, 1)`.
  have hcd : ∀ m ≤ N, ContDiffOn ℝ (m : WithTop ℕ∞)
      (fun x : ℝ => (Real.sinc x)⁻¹) (Ioo (-1 : ℝ) 1) := by
    intro m _ x hx
    exact ((contDiffAt_sinc hx (m : WithTop ℕ∞)).inv (sinc_ne_zero_of_mem_Ioo hx)).contDiffWithinAt
  -- hence its `m`-th derivative is bounded on the compact set `[0, π/8]`.
  have hbound : ∀ m, ∃ C : ℝ, m ≤ N → ∀ x ∈ Icc (0 : ℝ) (Real.pi / 8),
      |iteratedDeriv m (fun x : ℝ => (Real.sinc x)⁻¹) x| ≤ C := by
    intro m
    by_cases hm : m ≤ N
    · have hunic : UniqueDiffOn ℝ (Ioo (-1 : ℝ) 1) := isOpen_Ioo.uniqueDiffOn
      have hcontW : ContinuousOn
          (iteratedDerivWithin m (fun x : ℝ => (Real.sinc x)⁻¹) (Ioo (-1 : ℝ) 1))
          (Ioo (-1 : ℝ) 1) :=
        (hcd m hm).continuousOn_iteratedDerivWithin le_rfl hunic
      have hcont : ContinuousOn (iteratedDeriv m (fun x : ℝ => (Real.sinc x)⁻¹))
          (Ioo (-1 : ℝ) 1) :=
        hcontW.congr fun x hx =>
          (iteratedDerivWithin_eq_iteratedDeriv hunic
            ((hcd m hm).contDiffAt (isOpen_Ioo.mem_nhds hx)) hx).symm
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.mono hsub)
      exact ⟨C, fun _ x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose C hC using hbound
  refine ⟨(∑ m ∈ Finset.range (N + 1), max (C m) 0) + 1, ?_, ?_⟩
  · have hnn : 0 ≤ ∑ m ∈ Finset.range (N + 1), max (C m) 0 :=
      Finset.sum_nonneg fun m _ => le_max_right _ _
    linarith
  · intro i hi x hx
    have hxIcc : x ∈ Icc (0 : ℝ) (Real.pi / 8) := ⟨le_of_lt hx.1, hx.2⟩
    have h1 : |iteratedDeriv i (fun x : ℝ => (Real.sinc x)⁻¹) x| ≤ max (C i) 0 :=
      le_trans (hC i hi x hxIcc) (le_max_left _ _)
    have h2 : max (C i) 0 ≤ ∑ m ∈ Finset.range (N + 1), max (C m) 0 :=
      Finset.single_le_sum (fun m _ => le_max_right _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hEq : iteratedDeriv i (fun y : ℝ => (Real.sinc y)⁻¹) x
        = iteratedDeriv i (fun y : ℝ => y / Real.sin y) x :=
      Filter.EventuallyEq.iteratedDeriv_eq i (eventually_sincInv_eq hx.1)
    rw [← hEq]
    linarith

end Work.FTS.EllipticEst.remov.TopCoreB
