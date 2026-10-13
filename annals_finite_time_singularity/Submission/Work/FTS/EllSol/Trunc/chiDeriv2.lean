import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllSol.Trunc.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open Filter Set
open scoped Topology

/-- `deriv (deriv tk)` is bounded: it is continuous and vanishes off `[-2,2]`. -/
theorem exists_bound_deriv2_tk : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv (deriv tk) t| ≤ K := by
  have hcont : Continuous (deriv (deriv tk)) :=
    ((tk_contDiff 2).deriv').continuous_deriv_one
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
  · exact le_trans (hK t ht) (le_max_left _ _)
  · have h0 : deriv (deriv tk) t = 0 := by
      have htk : tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
        have hmem : t ∈ {s : ℝ | 2 < |s|} := by
          change 2 < |t|
          exact lt_of_not_ge fun hle => ht (Set.mem_Icc.mpr (abs_le.mp hle))
        filter_upwards [hopen.mem_nhds hmem] with s hs
        exact tk_eq_zero (le_of_lt hs)
      have hd : deriv tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        simpa using htk.deriv
      rw [hd.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The second derivative of the cutoff at scale `N`. -/
theorem deriv2_chi_eq (N t : ℝ) :
    deriv (deriv (chi N)) t = deriv (deriv tk) (t / N) / N ^ 2 := by
  have hchi : deriv (chi N) = fun s : ℝ => deriv tk (s / N) / N := by
    funext s; exact deriv_chi_eq N s
  rw [hchi, deriv_div_const]
  have hcomp : deriv (fun s : ℝ => deriv tk (s / N)) t
      = deriv (deriv tk) (t / N) * deriv (fun s : ℝ => s / N) t := by
    rw [show (fun s : ℝ => deriv tk (s / N))
        = (deriv tk) ∘ (fun s : ℝ => s / N) from rfl]
    exact deriv_comp t
      ((ContDiff.differentiable_deriv_two (tk_contDiff 2)).differentiableAt)
      (differentiableAt_id.div_const N)
  rw [hcomp, deriv_div_const, deriv_id'']
  ring

theorem chiDeriv2 :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ t : ℝ, |deriv (deriv tk) t| ≤ K) ∧
      (∀ N t : ℝ, deriv (deriv (chi N)) t = deriv (deriv tk) (t / N) / N ^ 2) ∧
      (∀ N : ℝ, 0 < N → ∀ t : ℝ, |deriv (deriv (chi N)) t| ≤ K / N ^ 2) ∧
      (∀ N : ℝ, 0 < N → ∀ t : ℝ, |t| < N → deriv (chi N) t = 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_deriv2_tk
  refine ⟨K, hK0, hK, fun N t => deriv2_chi_eq N t, fun N hN t => ?_, fun N hN t ht => ?_⟩
  · rw [deriv2_chi_eq, abs_div, abs_of_nonneg (sq_nonneg N)]
    exact div_le_div_of_nonneg_right (hK (t / N)) (sq_nonneg N)
  · have hev : (chi N) =ᶠ[𝓝 t] (fun _ : ℝ => (1:ℝ)) := by
      have hopen : IsOpen {s : ℝ | |s| < N} := isOpen_lt continuous_abs continuous_const
      have hmem : t ∈ {s : ℝ | |s| < N} := ht
      filter_upwards [hopen.mem_nhds hmem] with s hs
      exact chi_eq_one hN (le_of_lt hs)
    rw [hev.deriv_eq, deriv_const]

end Work.FTS.EllSol.Trunc
