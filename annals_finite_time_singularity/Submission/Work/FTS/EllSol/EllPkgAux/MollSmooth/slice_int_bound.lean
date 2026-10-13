/-
# The slice integral bound of the mollification transfer

For a continuous slice datum `D` on an interval `[l, u] ⊆ (0, π/2)` of length at most `π/4`,
a centre `c` within distance `π/4` of every point of `[l, u]`, and an integrable `θ`-slice
`D(θ)² sin(2θ)^{-η}`, the weighted first moment of `D` is bounded by the `L²`-norm of `D`
against the angular weight `sin(2θ)^{-η}` of `Work.Spaces`:

  `|∫_l^u (c - t) D(t) dt| ≤ (π/4) √(π/4) √(∫_{Iθ} D(θ)² sin(2θ)^{-η} dθ)`.

The proof is Cauchy–Schwarz (`Work.Spaces.hardyZ_interval_integral_mul_le_sqrt`), applied to
the pair `((c - ·) D, 1)` on `[l, u]`, combined with the two elementary bounds

* `(c - t)² ≤ (π/4)²` on `[l, u]` (from `|c - t| ≤ π/4`), and
* `∫_l^u D² ≤ ∫_{Iθ} D² sin(2θ)^{-η}`, which follows from `sin(2θ)^{-η} ≥ 1` on
  `[l, u] ⊆ (0, π/2)` and from the monotonicity of the set integral.

The constant `(π/4) √(π/4)` is exactly what the two bounds give: the factor `π/4` from the
length `u - l ≤ π/4` and the factor `π/4` from the weight `|c - t| ≤ π/4`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open scoped Real Topology Interval
open MeasureTheory Set Filter

theorem slice_int_bound {D : ℝ → ℝ} {c l u : ℝ} (hlu : l ≤ u) (hl : 0 < l)
    (hu : u < Real.pi / 2) (hul : u - l ≤ Real.pi / 4) (hcont : ContinuousOn D (Set.uIcc l u))
    (hc : ∀ t ∈ Set.Icc l u, |c - t| ≤ Real.pi / 4)
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => D θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    |∫ t in l..u, (c - t) * D t| ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  -- abbreviate the constant `π/4` so that the arithmetic at the end is painless
  set P : ℝ := Real.pi / 4 with hP
  have hPnn : 0 ≤ P := by rw [hP]; positivity
  -- `D` is continuous on the closed interval `[l, u]`
  have hcontIcc : ContinuousOn D (Set.Icc l u) := by
    rwa [Set.uIcc_of_le hlu] at hcont
  -- the interval `[l, u]` lies inside `Iθ = [0, π/2]`
  have hsub : Set.Icc l u ⊆ Work.Spaces.Iθ := by
    intro t ht
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_trans (le_of_lt hl) ht.1, le_of_lt (lt_of_le_of_lt ht.2 hu)⟩
  -- on `[l, u]` the weight `sin(2θ)^{-η}` dominates `1`
  have hthEta : ∀ t ∈ Set.Icc l u, (1 : ℝ) ≤ Work.FTS.EllipticEst.thEta t := by
    intro t ht
    have ht0 : 0 < Real.sin (2 * t) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [ht.1, hl]
      · linarith [ht.2, hu]
    have hle : Real.sin (2 * t) ≤ 1 := Real.sin_le_one _
    have hneg : -(Work.Spaces.eta) ≤ 0 := by linarith [Work.Spaces.eta_nonneg]
    have h := Real.rpow_le_rpow_of_nonpos ht0 hle hneg
    rw [Real.one_rpow] at h
    simpa [Work.FTS.EllipticEst.thEta] using h
  have hIntD2 : IntegrableOn (fun t : ℝ => D t ^ 2) (Set.Icc l u) :=
    (hcontIcc.pow 2).integrableOn_compact isCompact_Icc
  have hIntD2w : IntegrableOn (fun t : ℝ => D t ^ 2 * Work.FTS.EllipticEst.thEta t)
      (Set.Icc l u) := hint.mono_set hsub
  -- the `L²`-norm over `[l, u]` is dominated by the weighted one over `Iθ`
  have hX : ∫ t in l..u, D t ^ 2 ≤
      ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    have hconv : ∫ t in l..u, D t ^ 2 = ∫ t in Set.Icc l u, D t ^ 2 := by
      rw [intervalIntegral.integral_of_le hlu, integral_Icc_eq_integral_Ioc]
    rw [hconv]
    have h1 : ∫ t in Set.Icc l u, D t ^ 2 ≤
        ∫ t in Set.Icc l u, D t ^ 2 * Work.FTS.EllipticEst.thEta t :=
      setIntegral_mono_on hIntD2 hIntD2w measurableSet_Icc
        (fun t ht => le_mul_of_one_le_right (sq_nonneg _) (hthEta t ht))
    have h2 : ∫ t in Set.Icc l u, D t ^ 2 * Work.FTS.EllipticEst.thEta t ≤
        ∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine setIntegral_mono_set hint ?_ ?_
      · filter_upwards [ae_restrict_mem (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
          with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · exact Filter.Eventually.of_forall (fun x hx => hsub hx)
    exact le_trans h1 h2
  -- Cauchy–Schwarz for the interval integral, applied to `((c - ·) D, 1)`
  have hf_cont : ContinuousOn (fun t : ℝ => (c - t) * D t) (Set.uIcc l u) :=
    ((continuous_const.sub continuous_id).continuousOn).mul hcont
  have hg_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.uIcc l u) :=
    continuous_const.continuousOn
  have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt l u hlu
    (f := fun t : ℝ => (c - t) * D t) (g := fun _ : ℝ => (1 : ℝ)) hf_cont hg_cont
  have h_one : ∫ t in l..u, (1 : ℝ) ^ 2 = u - l := by
    rw [show (1 : ℝ) ^ 2 = 1 by norm_num, intervalIntegral.integral_const]
    simp
  -- the pointwise bound on the integrand, from `|c - t| ≤ P`
  have hpt : ∀ t ∈ Set.Icc l u, ((c - t) * D t) ^ 2 ≤ P ^ 2 * D t ^ 2 := by
    intro t ht
    have h1 : |c - t| ≤ P := hc t ht
    have h2 : (c - t) ^ 2 ≤ P ^ 2 := by
      have h3 := abs_le.mp h1
      nlinarith [h3.1, h3.2]
    calc ((c - t) * D t) ^ 2 = (c - t) ^ 2 * D t ^ 2 := by ring
      _ ≤ P ^ 2 * D t ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hmono : ∫ t in l..u, ((c - t) * D t) ^ 2 ≤ P ^ 2 * ∫ t in l..u, D t ^ 2 := by
    have hg2 : ContinuousOn (fun t : ℝ => P ^ 2 * D t ^ 2) (Set.uIcc l u) :=
      continuousOn_const.mul (hcont.pow 2)
    have hb := intervalIntegral.integral_mono_on hlu
      ((hf_cont.pow 2).intervalIntegrable (μ := volume))
      (hg2.intervalIntegrable (μ := volume)) hpt
    rwa [intervalIntegral.integral_const_mul] at hb
  have hsqrt : Real.sqrt (P ^ 2 * ∫ t in l..u, D t ^ 2) =
      P * Real.sqrt (∫ t in l..u, D t ^ 2) := by
    rw [show P ^ 2 * ∫ t in l..u, D t ^ 2 = (P * P) * ∫ t in l..u, D t ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hPnn hPnn), Real.sqrt_mul_self (x := P) hPnn]
  have hXS : Real.sqrt (∫ t in l..u, D t ^ 2) ≤
      Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_le_sqrt hX
  calc |∫ t in l..u, (c - t) * D t|
      = |∫ t in l..u, (c - t) * D t * 1| := by
        congr 1
        exact intervalIntegral.integral_congr (fun t _ => (mul_one _).symm)
    _ ≤ Real.sqrt (∫ t in l..u, ((c - t) * D t) ^ 2) * Real.sqrt (∫ t in l..u, (1 : ℝ) ^ 2) :=
        hcs
    _ = Real.sqrt (∫ t in l..u, ((c - t) * D t) ^ 2) * Real.sqrt (u - l) := by rw [h_one]
    _ ≤ Real.sqrt (P ^ 2 * ∫ t in l..u, D t ^ 2) * Real.sqrt P :=
        mul_le_mul (Real.sqrt_le_sqrt hmono) (Real.sqrt_le_sqrt hul)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = P * Real.sqrt (∫ t in l..u, D t ^ 2) * Real.sqrt P := by rw [hsqrt]
    _ ≤ P * Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) *
          Real.sqrt P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXS hPnn) (Real.sqrt_nonneg P)
    _ = P * Real.sqrt P *
          Real.sqrt (∫ θ in Work.Spaces.Iθ, D θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
