/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/JepsHkMem/Jker_comp_zShift_lt_top.lean`

The `p₁`-half of the weighted `ℋ^k`-estimate for the log-coordinate mollifier `J_ε`: composing
the kernel with the `z`-shift of an `ℝ≥0∞`-valued weight cannot destroy finiteness, because the
kernel is supported in the ball of radius `ε`, so the shifted argument `p ↦ z * exp (-p.1)` runs
over a *compact* interval of the `u`-line, on which the substitution `du = -u dx` costs only the
bounded factor `(z exp (-ε))⁻¹ = exp ε / z`.

Concretely, for `G : ℝ → ℝ≥0∞` with `∫⁻_{u > 0} G u < ∞`, every admissible kernel `ρ` and all
`ε > 0`, `z > 0`,

  `∫⁻ p : ℝ × ℝ, ofReal (Jker ρ ε p) * G (z * exp (-(p.1))) < ∞`.

The proof is a chain: the kernel is bounded by `M` on its (compact) support, so the `p`-integral
is at most `M` times the integral of `G (z exp (-p.1))` over the ball; the ball is contained in
the square `Icc (-ε) ε ×ˢ Icc (-ε) ε`, on which Tonelli's inequality reduces the `p₂`-integration
to the length `2ε` of the interval; and finally the one-dimensional change of variables
`u = z exp (-x)` (`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) turns
`∫⁻ x in Icc (-ε) ε, G (z exp (-x))` into an integral of `G` over `(0, ∞)` divided by the
pointwise lower bound `z exp (-ε)` of `|d/dx (z exp (-x))|`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

open MeasureTheory Set

set_option maxHeartbeats 800000

/-- **The one-dimensional substitution `u = z * exp (-x)` on `[-ε, ε]`.**  For any
`G : ℝ → ℝ≥0∞` (no measurability needed) and `ε, z > 0`,

  `∫⁻ x in Icc (-ε) ε, G (z * exp (-x)) ≤ (exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The constant is the inverse of the pointwise lower bound `z * exp (-ε)` of the stretching factor
`|d/dx (z exp (-x))| = z exp (-x)`. -/
private lemma lintegral_Icc_expNeg_le {G : ℝ → ENNReal} {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) :
    (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
  have hzε : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  -- the derivative of the substitution
  have hderiv : ∀ x ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x)))
        (Set.Icc (-ε) ε) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa using h1
    have h2 : HasDerivAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x))) x := by
      have h3 := h'.const_mul z
      simpa using h3
    exact h2.hasDerivWithinAt
  -- the substitution is injective
  have hinj : Set.InjOn (fun x : ℝ => z * Real.exp (-x)) (Set.Icc (-ε) ε) := by
    intro x _ y _ hxy
    have hexp : Real.exp (-x) = Real.exp (-y) := mul_left_cancel₀ hz.ne' hxy
    have h2 : -x = -y := Real.exp_injective hexp
    linarith
  have hkey := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.Icc (-ε) ε) (f := fun x : ℝ => z * Real.exp (-x))
    (f' := fun x : ℝ => -(z * Real.exp (-x))) measurableSet_Icc hderiv hinj G
  have himage_sub : (fun x : ℝ => z * Real.exp (-x)) '' Set.Icc (-ε) ε ⊆ Set.Ioi 0 := by
    rintro u ⟨x, _, rfl⟩
    exact mul_pos hz (Real.exp_pos _)
  have hpt : ∀ x : ℝ, ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x))
      = ENNReal.ofReal (z * Real.exp (-x)) * G (z * Real.exp (-x)) := by
    intro x
    rw [abs_neg, abs_of_pos (mul_pos hz (Real.exp_pos _))]
  have h1 : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ x in Set.Icc (-ε) ε,
          ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (z * Real.exp (-ε)))
      (fun x => G (z * Real.exp (-x))) ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc ?_
    intro x hx
    rw [hpt x]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hz.le)
  have h2 : (∫⁻ x in Set.Icc (-ε) ε,
        ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := by
    rw [← hkey]
    exact lintegral_mono_set himage_sub
  have hfin' : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := le_trans h1 h2
  have hne0 : ENNReal.ofReal (z * Real.exp (-ε)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hzε
  have hneTop : ENNReal.ofReal (z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u := by
    calc (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
        = 1 * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := (one_mul _).symm
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ENNReal.ofReal (z * Real.exp (-ε))
            * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ *
            (ENNReal.ofReal (z * Real.exp (-ε))
              * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))) := by
          rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u :=
          mul_le_mul_of_nonneg_left hfin' zero_le
  have hreal : (z * Real.exp (-ε))⁻¹ = Real.exp ε / z := by
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hconst_eq : (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ = ENNReal.ofReal (Real.exp ε / z) := by
    rw [← ENNReal.ofReal_inv_of_pos hzε, hreal]
  rwa [hconst_eq] at hstep

theorem Jker_comp_zShift_lt_top {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {G : ℝ → ENNReal}
    (hmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume)
    (hfin : (∫⁻ z' in Set.Ioi 0, G z') < ⊤) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε p)
      * G (z * Real.exp (-(p.1)))) < ⊤ := by
  set s : Set ℝ := Set.Icc (-ε) ε with hs
  set Φ : ℝ × ℝ → ENNReal := fun p => G (z * Real.exp (-(p.1))) with hΦ
  have hΦa : ∀ p : ℝ × ℝ, Φ p = G (z * Real.exp (-(p.1))) := fun p => by simp only [hΦ]
  -- the kernel is bounded on its compact support
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) ε).exists_bound_of_continuousOn
    (Jker_continuous hρ ε).continuousOn
  have hJle : ∀ p : ℝ × ℝ, Jker ρ ε p ≤ max C 0 := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · have h := hC p hp
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
    · rw [Jker_eq_zero_of_not_mem hρ hε hp]
      exact le_max_right _ _
  -- (1) replace the kernel by its supremum on the ball
  have hstep1 : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
    have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p
        ≤ ENNReal.ofReal (max C 0) * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p := by
      intro p
      by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
      · rw [indicator_of_mem hp]
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hJle p)) zero_le
      · rw [indicator_of_notMem hp, Jker_eq_zero_of_not_mem hρ hε hp]
        simp
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max C 0)
            * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p := lintegral_mono hpt
      _ = ENNReal.ofReal (max C 0)
            * ∫⁻ p : ℝ × ℝ, (Metric.closedBall (0 : ℝ × ℝ) ε).indicator Φ p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := by
          rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet) Φ]
  -- (2) the ball sits inside the square `s ×ˢ s`
  have hball_sub : Metric.closedBall (0 : ℝ × ℝ) ε ⊆ s ×ˢ s := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hp' : max |p.1| |p.2| ≤ ε := by simpa only [Real.norm_eq_abs] using hp
    have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) hp'
    have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) hp'
    rw [hs]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hstep2 : (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) ≤ ∫⁻ p in s ×ˢ s, Φ p :=
    lintegral_mono_set hball_sub
  -- (3) pass to the product of the two restricted lines
  have hstep3 : (∫⁻ p in s ×ˢ s, Φ p)
      = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  -- (4) Tonelli's inequality
  have hstep4 : (∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)))
      ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := lintegral_prod_le Φ
  -- (5) the `p₂`-integration contributes only the length `2ε`
  have hinner : ∀ x : ℝ, (∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) := by
    intro x
    have hpt : ∀ y : ℝ, Φ (x, y) = G (z * Real.exp (-x)) := by
      intro y
      rw [hΦa]
    rw [show (∫⁻ y in s, Φ (x, y)) = ∫⁻ y in s, G (z * Real.exp (-x)) from
      lintegral_congr (fun y => hpt y)]
    rw [setLIntegral_const, hs, Real.volume_Icc]
    have : (ε : ℝ) - -ε = 2 * ε := by ring
    rw [this]
    exact mul_comm _ _
  have hstep5 : (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := by
    rw [show (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
        = ∫⁻ x in s, ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) from
      lintegral_congr (fun x => hinner x)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (6) the one-dimensional substitution
  have hstep6 : (∫⁻ x in s, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
    simpa only [hs] using lintegral_Icc_expNeg_le (G := G) hε hz
  -- the goal, rewritten in terms of `Φ`
  have hstart : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      = (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * G (z * Real.exp (-(p.1)))) :=
    lintegral_congr (fun p => by rw [hΦa p])
  have hK : ENNReal.ofReal (max C 0) * (ENNReal.ofReal (2 * ε)
      * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) < ⊤ := by
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) ?_
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) hfin
  rw [← hstart]
  refine lt_of_le_of_lt ?_ hK
  calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p) * Φ p)
      ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p := hstep1
    _ ≤ ENNReal.ofReal (max C 0) * ∫⁻ p in s ×ˢ s, Φ p :=
        mul_le_mul_of_nonneg_left hstep2 zero_le
    _ = ENNReal.ofReal (max C 0)
          * ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by rw [hstep3]
    _ ≤ ENNReal.ofReal (max C 0) * ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) :=
        mul_le_mul_of_nonneg_left hstep4 zero_le
    _ = ENNReal.ofReal (max C 0)
          * (ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x))) := by rw [hstep5]
    _ ≤ ENNReal.ofReal (max C 0) * (ENNReal.ofReal (2 * ε)
          * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep6 zero_le) zero_le

end Work.FTS.StrongEps.JepsHkMem
