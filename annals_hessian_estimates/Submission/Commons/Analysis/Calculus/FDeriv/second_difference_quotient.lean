import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Calculus.Taylor.taylor_two_isLittleO

namespace Commons.Analysis.Calculus.FDeriv

open Filter Asymptotics
open scoped Topology

/-- A continuous bilinear form given by the second derivative, evaluated on the diagonal of `t • v`. -/
lemma clm_smul_smul_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] (E →L[ℝ] ℝ)) (t : ℝ) (v : E) :
    L (t • v) (t • v) = t ^ 2 * (L v v) := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- If `R` is `o(‖·‖²)` at the origin then `t ↦ R (t • v) / t²` tends to `0`. -/
lemma tendsto_div_sq_of_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : E → ℝ} (hR : R =o[nhds (0 : E)] (fun y => ‖y‖ ^ 2)) (v : E) :
    Tendsto (fun t : ℝ => R (t • v) / t ^ 2) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
  have hcont : Tendsto (fun t : ℝ => t • v) (nhds (0 : ℝ)) (nhds (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • v) := continuous_id.smul continuous_const
    simpa using hc.tendsto (0 : ℝ)
  have hcont' : Tendsto (fun t : ℝ => t • v) (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (0 : E)) :=
    hcont.mono_left nhdsWithin_le_nhds
  rw [Metric.tendsto_nhds]
  intro ε hε
  set c : ℝ := ε / (1 + ‖v‖ ^ 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  filter_upwards [hcont'.eventually (hR.bound hcpos), self_mem_nhdsWithin] with t ht hmem
  have ht0 : t ≠ 0 := by simpa using hmem
  have hgn : ‖‖t • v‖ ^ 2‖ = ‖t • v‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  rw [hgn] at ht
  simp only [dist_zero_right]
  have hnorm : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc ‖R (t • v) / t ^ 2‖
      = ‖R (t • v)‖ / t ^ 2 := by
        have h2 : ‖(t : ℝ) ^ 2‖ = t ^ 2 := Real.norm_of_nonneg (sq_nonneg t)
        rw [norm_div, h2]
    _ ≤ (c * ‖t • v‖ ^ 2) / t ^ 2 := div_le_div_of_nonneg_right ht (sq_nonneg t)
    _ = (c * (t ^ 2 * ‖v‖ ^ 2)) / t ^ 2 := by rw [hnorm]
    _ = c * ‖v‖ ^ 2 := by
        rw [mul_div_assoc, mul_comm (t ^ 2) (‖v‖ ^ 2),
          mul_div_cancel_right₀ _ (pow_ne_zero 2 ht0)]
    _ < ε := by
        rw [hcdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖v‖]

theorem second_difference_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {v : E} (h : ContDiffAt ℝ 2 u 0) :
    Filter.Tendsto (fun t : ℝ => (u (t • v) + u (-(t • v)) - 2 * u 0) / t ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds ((fderiv ℝ (fderiv ℝ u) 0) v v)) := by
  set L : E →L[ℝ] ℝ := fderiv ℝ u 0 with hL
  set Q : E →L[ℝ] (E →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ u) 0 with hQ
  set R : E → ℝ := fun y => u y - u 0 - L y - (1 / 2) * Q y y with hR
  -- `R` is the Peano remainder of the second order Taylor expansion.
  have hRlittle : R =o[nhds (0 : E)] (fun y => ‖y‖ ^ 2) := by
    have h0 := Commons.Analysis.Calculus.Taylor.taylor_two_isLittleO (f := u) (x := (0 : E)) h
    simpa only [hR, hQ, hL, sub_zero] using h0
  -- linear part cancels
  have hLzero : ∀ t : ℝ, L (t • v) + L (-(t • v)) = 0 := by
    intro t
    rw [← map_add, add_neg_cancel, map_zero]
  -- quadratic part doubles
  have hQdiag : ∀ t : ℝ, Q (t • v) (t • v) = t ^ 2 * (Q v v) :=
    fun t => clm_smul_smul_apply' Q t v
  have hQdiag' : ∀ t : ℝ, Q (-(t • v)) (-(t • v)) = t ^ 2 * (Q v v) := by
    intro t
    rw [show (-(t • v) : E) = (-t) • v by rw [neg_smul], clm_smul_smul_apply']
    ring
  -- exact second order expansion
  have hkey : ∀ t : ℝ,
      u (t • v) + u (-(t • v)) - 2 * u 0
        = t ^ 2 * (Q v v) + R (t • v) + R (-(t • v)) := by
    intro t
    have h1 : R (t • v) = u (t • v) - u 0 - L (t • v) - (1 / 2) * Q (t • v) (t • v) := by
      simp [hR]
    have h2 : R (-(t • v))
        = u (-(t • v)) - u 0 - L (-(t • v)) - (1 / 2) * Q (-(t • v)) (-(t • v)) := by
      simp [hR]
    have hL' := hLzero t
    have hQ1 := hQdiag t
    have hQ2 := hQdiag' t
    linarith
  -- the remainder contributes nothing
  have hRlim : Tendsto (fun t : ℝ => (R (t • v) + R (-(t • v))) / t ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have h1 := tendsto_div_sq_of_isLittleO hRlittle v
    have h2 := tendsto_div_sq_of_isLittleO hRlittle (-v)
    have h2' : Tendsto (fun t : ℝ => R (-(t • v)) / t ^ 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
      refine h2.congr' (Eventually.of_forall (fun t => ?_))
      simp only [smul_neg]
    have hsum := h1.add h2'
    have heq : (fun t : ℝ => R (t • v) / t ^ 2 + R (-(t • v)) / t ^ 2)
        =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
        (fun t : ℝ => (R (t • v) + R (-(t • v))) / t ^ 2) :=
      Eventually.of_forall (fun t => by dsimp only; rw [add_div])
    exact Tendsto.congr' heq (by simpa using hsum)
  -- assemble
  have hfinal : Tendsto (fun t : ℝ => Q v v + (R (t • v) + R (-(t • v))) / t ^ 2)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (Q v v)) := by
    simpa using hRlim.const_add (Q v v)
  have heq : (fun t : ℝ => Q v v + (R (t • v) + R (-(t • v))) / t ^ 2)
      =ᶠ[nhdsWithin (0 : ℝ) ({0}ᶜ)]
      (fun t : ℝ => (u (t • v) + u (-(t • v)) - 2 * u 0) / t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t hmem
    have ht0 : t ≠ 0 := by simpa using hmem
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    rw [hkey t]
    field_simp
    ring
  simpa only [hQ] using Tendsto.congr' heq hfinal

end Commons.Analysis.Calculus.FDeriv