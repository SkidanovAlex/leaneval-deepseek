import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs
import Submission.Work.FTS.EllipticEst.Blocks.AgmonIBP
import Submission.Work.FTS.EllipticEst.Blocks.logChiFamily
import Submission.Work.FTS.EllipticEst.TT.logCutDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.EllipticEst

/-! ## Piece 1 of `NOTES_AgmonCutoff.md`: the second logarithmic derivative of `logChi n`

`logChi n z = chi (log z / L)` with `L = log ((n : ℝ) + 2)` and
`chi = Work.ChiExplicit.chi = fun t => Real.smoothTransition (2 - |t|)`, the explicit smooth
bump.  The chain rule gives, for `z > 0` and `t = log z / L`,

  `(logChi n)'(z)  = chi'(t) / (z L)`,
  `(logChi n)''(z) = chi''(t) / (z L)² - chi'(t) / (z² L)`,

so that `z² (logChi n)''(z) = chi''(t)/L² - chi'(t)/L`.  Both `chi'` and `chi''` are globally
bounded (they are continuous and vanish outside `[-2,2]`), hence `|z² (logChi n)''(z)|` is
bounded by `K / L` uniformly in `n` and `z`.  This is exactly the statement
`logChi_second_deriv_le` below, the input `δ = δ_n → 0` of the Agmon estimate. -/

/-- **A global bound for the second derivative of the explicit cut-off.**  `deriv (deriv chi)`
is continuous (`chi` is `C^∞`) and vanishes strictly outside `[-2,2]` (where `chi` is locally
`0`, so both its first and its second derivative vanish there); on the compact interval `[-2,2]`
the continuous function `|deriv (deriv chi)|` therefore attains its maximum. -/
theorem exists_bound_deriv_deriv_chi :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv (deriv Work.ChiExplicit.chi) t| ≤ K := by
  have hcont : Continuous (fun t : ℝ => |deriv (deriv Work.ChiExplicit.chi) t|) := by
    have h1 : Continuous (iteratedDeriv 2 Work.ChiExplicit.chi) :=
      (Work.ChiExplicit.chi_contDiff ⊤).continuous_iteratedDeriv 2 (by simp)
    have h2 : iteratedDeriv 2 Work.ChiExplicit.chi
        = deriv (deriv Work.ChiExplicit.chi) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact (h1.congr (fun t => by rw [h2])).abs
  -- `chi` is locally `0` outside `[-2,2]`, hence so are `chi'` and `chi''`.
  have hzero : ∀ t : ℝ, 2 < |t| → deriv (deriv Work.ChiExplicit.chi) t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | (2 : ℝ) < |s|} := isOpen_lt continuous_const continuous_abs
    have hev : deriv Work.ChiExplicit.chi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      have h0 : Work.ChiExplicit.chi =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hs] with u hu
        exact Work.ChiExplicit.chi_eq_zero hu.le
      rw [h0.deriv_eq, deriv_const]
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨x₀, -, hmax⟩ :=
    (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
      (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
      (f := fun t : ℝ => |deriv (deriv Work.ChiExplicit.chi) t|) hcont.continuousOn
  refine ⟨|deriv (deriv Work.ChiExplicit.chi) x₀|, abs_nonneg _, ?_⟩
  intro t
  by_cases ht : |t| ≤ 2
  · exact (isMaxOn_iff.mp hmax) t (Set.mem_Icc.mpr (abs_le.mp ht))
  · rw [hzero t (lt_of_not_ge ht)]
    simp

/-- **The second derivative of `logChi n`** for `z > 0`, by the chain rule:
with `L = log ((n : ℝ) + 2)`, `t = log z / L`,

  `(logChi n)''(z) = (chi''(t) - chi'(t)·L) / (z·L)²`. -/
theorem deriv_deriv_logChi_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z =
      (deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2))
        - deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))
          * Real.log ((n : ℝ) + 2)) / (z * Real.log ((n : ℝ) + 2)) ^ 2 := by
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hL0 : L ≠ 0 := ne_of_gt hLpos
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hdiffchi : Differentiable ℝ (deriv Work.ChiExplicit.chi) := by
    have h2 : ContDiff ℝ 2 Work.ChiExplicit.chi := Work.ChiExplicit.chi_contDiff 2
    exact h2.differentiable_deriv_two
  have hgz : DifferentiableAt ℝ (fun w : ℝ => Real.log w / L) z :=
    (Real.differentiableAt_log hz0).div_const L
  have hchid : DifferentiableAt ℝ (deriv Work.ChiExplicit.chi) (Real.log z / L) :=
    hdiffchi.differentiableAt
  have hAz : DifferentiableAt ℝ
      (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L)) z := by
    simpa only [Function.comp_def] using hchid.comp z hgz
  have hBz : DifferentiableAt ℝ (fun w : ℝ => w * L) z :=
    differentiableAt_id.mul_const L
  -- On `(0,∞)`, `deriv (logChi n)` is the function used in the chain rule above.
  have hev : deriv (Work.FTS.EllipticEst.TT.logChi n)
      =ᶠ[𝓝 z] (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L) / (w * L)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    rw [Work.FTS.EllipticEst.Blocks.deriv_logChi_eq n hw, ← hL, mul_one_div]
  rw [hev.deriv_eq]
  have hderivA : deriv (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L)) z
      = deriv (deriv Work.ChiExplicit.chi) (Real.log z / L) * (1 / (z * L)) := by
    rw [show (fun w : ℝ => deriv Work.ChiExplicit.chi (Real.log w / L))
        = (deriv Work.ChiExplicit.chi) ∘ (fun w : ℝ => Real.log w / L) from rfl,
      deriv_comp z hchid hgz, deriv_div_const, Real.deriv_log]
    rw [inv_eq_one_div, div_div]
  have hderivB : deriv (fun w : ℝ => w * L) z = L := by
    rw [show (fun w : ℝ => w * L) = fun y : ℝ => id y * L from rfl,
      deriv_mul_const differentiableAt_id L, deriv_id]
    ring
  have hBne : (fun w : ℝ => w * L) z ≠ 0 := by
    show z * L ≠ 0
    exact mul_ne_zero hz0 hL0
  rw [deriv_fun_div hAz hBz hBne, hderivA, hderivB]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / L) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / L) with hB
  field_simp

/-- **The identity behind the estimate**, in the form in which it is bounded:
for `z > 0`, `L = log ((n : ℝ) + 2)` and `t = log z / L`,

  `z² · (logChi n)''(z) = chi''(t)/L² - chi'(t)/L`. -/
theorem logChi_second_deriv_eq (n : ℕ) {z : ℝ} (hz : 0 < z) :
    z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z =
      deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2))
        / Real.log ((n : ℝ) + 2) ^ 2
      - deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2))
        / Real.log ((n : ℝ) + 2) := by
  have hLpos : 0 < Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hz0 : z ≠ 0 := ne_of_gt hz
  rw [deriv_deriv_logChi_eq n hz]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2)) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) with hB
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos' : 0 < L := by rw [hL]; exact hLpos
  have hL0' : L ≠ 0 := ne_of_gt hLpos'
  field_simp

/-- Second logarithmic derivative of the cut-off family `logChi n`: on `(0,∞)` the quantity
`z²·(logChi n)''(z) = chi''(t)/L² - chi'(t)/L` (with `t = log z / log ((n:ℝ)+2)`) is bounded by
`K / log ((n:ℝ)+2)`, uniformly in `z`.  See `Submission/Work/EllipticEst/NOTES_AgmonCutoff.md`
(Piece 1). -/
theorem logChi_second_deriv_le : ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (z : ℝ), 0 < z →
    |z ^ 2 * deriv (deriv (Work.FTS.EllipticEst.TT.logChi n)) z|
      ≤ K / Real.log ((n : ℝ) + 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := Work.FTS.EllipticEst.Blocks.exists_bound_deriv_chi
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_deriv_deriv_chi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K₁ + K₂ / Real.log 2 + 1, by positivity, ?_⟩
  intro n z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hLpos : 0 < Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_add_natCast_pos n
  have hLge : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
    Work.FTS.EllipticEst.TT.log_two_le_log n
  rw [logChi_second_deriv_eq n hz]
  set A := deriv (deriv Work.ChiExplicit.chi) (Real.log z / Real.log ((n : ℝ) + 2)) with hA
  set B := deriv Work.ChiExplicit.chi (Real.log z / Real.log ((n : ℝ) + 2)) with hB
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLpos' : 0 < L := by rw [hL]; exact hLpos
  have hLge' : Real.log 2 ≤ L := by rw [hL]; exact hLge
  have hAabs : |A| ≤ K₂ := by rw [hA]; exact hK₂ _
  have hBabs : |B| ≤ K₁ := by rw [hB]; exact hK₁ _
  have htri : |A / L ^ 2 - B / L| ≤ |A| / L ^ 2 + |B| / L := by
    calc |A / L ^ 2 - B / L| = |A / L ^ 2 + -(B / L)| := by rw [sub_eq_add_neg]
      _ ≤ |A / L ^ 2| + |-(B / L)| := abs_add_le _ _
      _ = |A| / L ^ 2 + |B| / L := by
          rw [abs_div, abs_neg, abs_div, abs_of_pos (pow_pos hLpos' 2), abs_of_pos hLpos']
  have hstep : |A| / L ^ 2 + |B| / L ≤ K₂ / L ^ 2 + K₁ / L :=
    add_le_add (div_le_div_of_nonneg_right hAabs (pow_pos hLpos' 2).le)
      (div_le_div_of_nonneg_right hBabs hLpos'.le)
  have hstep2 : K₂ / L ^ 2 ≤ K₂ / (Real.log 2 * L) := by
    refine div_le_div_of_nonneg_left hK₂0 (mul_pos hlog2 hLpos') ?_
    nlinarith
  have hstep3 : K₂ / (Real.log 2 * L) = K₂ / Real.log 2 / L :=
    (div_div K₂ (Real.log 2) L).symm
  have hstep4 : K₂ / L ^ 2 + K₁ / L ≤ (K₁ + K₂ / Real.log 2 + 1) / L := by
    have h : K₂ / L ^ 2 + K₁ / L ≤ K₂ / Real.log 2 / L + K₁ / L :=
      add_le_add (hstep2.trans hstep3.le) le_rfl
    refine h.trans ?_
    have h2 : K₂ / Real.log 2 / L + K₁ / L = (K₁ + K₂ / Real.log 2) / L := by
      rw [add_div]
      ring
    rw [h2]
    exact div_le_div_of_nonneg_right (by linarith) hLpos'.le
  calc |A / L ^ 2 - B / L| ≤ |A| / L ^ 2 + |B| / L := htri
    _ ≤ K₂ / L ^ 2 + K₁ / L := hstep
    _ ≤ (K₁ + K₂ / Real.log 2 + 1) / L := hstep4

end Work.EllipticEst
