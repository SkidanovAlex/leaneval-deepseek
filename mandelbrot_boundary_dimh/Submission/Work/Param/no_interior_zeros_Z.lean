import Mathlib
import Submission.Work.Param.Setup

/-!
# The hitting sets `Z n` have empty interior

`Z n = {t : ℂ | (P n).eval t = 0}` is the zero set of the polynomial `P n = G n - X/2`, i.e. the
set of parameters `t` for which the `n`-th point of the critical orbit of `Tc (cOfLam t)` has
already reached the fixed point `t/2`.  Since `(P n).eval 2 = -1 ≠ 0`, the polynomial `P n` is
nonzero; a nonzero polynomial over `ℂ` has only finitely many roots, so `Z n` is finite, and in
particular has empty interior.

We prove this directly and elementarily: if `interior (Z n)` were nonempty it would contain a ball
`Metric.ball x ε` with `ε > 0`, and the injective map `r ↦ x + (ε/2) * r` from the infinite interval
`(0,1)` into that ball would exhibit infinitely many roots of `P n`.  By
`Polynomial.eq_zero_of_infinite_isRoot` this forces `P n = 0`, contradicting `(P n).eval 2 = -1`.
-/

namespace Work.Param

open Polynomial

/-- **The `n`-th hitting set has empty interior.**  `Z n` is the zero set of the nonzero polynomial
`P n`, hence finite, hence has no interior point. -/
theorem no_interior_zeros_Z (n : ℕ) : ¬ (interior (Work.Param.Z n)).Nonempty := by
  rintro ⟨x, hx⟩
  rw [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hx
  set c : ℂ := ((ε / 2 : ℝ) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < ε / 2))
  -- `r ↦ x + c * r` is injective on the infinite interval `(0,1)` ...
  have hinj : Function.Injective (fun r : ↥(Set.Ioo (0:ℝ) 1) => x + c * ((r:ℝ) : ℂ)) := by
    intro a b hab
    have h1 : c * ((a:ℝ) : ℂ) = c * ((b:ℝ) : ℂ) := add_left_cancel hab
    have h2 : ((a:ℝ) : ℂ) = ((b:ℝ) : ℂ) := mul_left_cancel₀ hcne h1
    exact Subtype.ext (Complex.ofReal_injective h2)
  -- ... and it takes its values in `Z n`, because they all lie in `Metric.ball x ε`.
  have hmem : ∀ r : ↥(Set.Ioo (0:ℝ) 1), x + c * ((r:ℝ) : ℂ) ∈ Work.Param.Z n := by
    intro r
    apply hεsub
    rw [Metric.mem_ball]
    have hr1 : (r:ℝ) < 1 := r.2.2
    have habs : ‖((r:ℝ) : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨by linarith [r.2.1], hr1⟩
    have hcn : ‖c‖ = ε / 2 := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hcn]
    nlinarith [habs, hε]
  have hInst : Infinite ↥(Set.Ioo (0:ℝ) 1) := (Set.Ioo_infinite (by norm_num : (0:ℝ) < 1)).to_subtype
  have hinf : (Work.Param.Z n).Infinite :=
    @Set.infinite_of_injective_forall_mem (↥(Set.Ioo (0:ℝ) 1)) ℂ hInst (Work.Param.Z n) _ hinj hmem
  -- so `P n` has infinitely many roots, hence is the zero polynomial.
  have hroot : Set.Infinite {y : ℂ | (P n).IsRoot y} := by
    simpa only [Polynomial.IsRoot, Work.Param.Z] using hinf
  have hzero : P n = 0 := Polynomial.eq_zero_of_infinite_isRoot (P n) hroot
  -- but `(P n).eval 2 = -1`.
  have h2 : (P n).eval 2 = 0 := by rw [hzero]; simp
  rw [P_eval_two n] at h2
  norm_num at h2

end Work.Param
