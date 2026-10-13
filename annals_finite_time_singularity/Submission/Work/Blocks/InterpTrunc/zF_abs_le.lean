/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second commutator bound `|D_z² ζ_k| ≤ K₂ / log² k`

`ζ_k = zc φ k = φ(log z / log k)` for `z > 0` (and `0` for `z ≤ 0`), where `φ` is the `C^∞`
bump of `IsZCut`.  Since `D_z² ζ_k = φ''(log z / log k) / log² k` for `z > 0` and `D_z² ζ_k = 0`
for `z ≤ 0`, the bound follows from the boundedness of `φ''` (continuous, compactly supported).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.Blocks.InterpTrunc.sliceL2_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

theorem zF_bound_uniform {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ (k : ℕ), 2 ≤ k → ∀ z : ℝ,
      |zF φ k z| ≤ K₂ / (Real.log k) ^ 2 := by
  -- smoothness of `φ'` and `φ''`
  have hφ1 : ContDiff ℝ Work.FTS.EllipticEst.smoothOrder (deriv φ) :=
    ContDiff.deriv' (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) hφ.1
  have hφ2 : ContDiff ℝ Work.FTS.EllipticEst.smoothOrder (deriv (deriv φ)) :=
    ContDiff.deriv' (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) hφ1
  have hcont : Continuous (fun t : ℝ => |deriv (deriv φ) t|) := hφ2.continuous.abs
  have hzero : ∀ t : ℝ, 2 < |t| → deriv (deriv φ) t = 0 := by
    intro t ht
    have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
    have hloc : ∀ s : ℝ, 2 < |s| → deriv φ s = 0 := by
      intro s hs
      have hev : φ =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [hopen.mem_nhds hs] with r hr
        exact hφ.2.2.1 r hr.le
      rw [hev.deriv_eq]
      exact deriv_const s 0
    have hev1 : deriv φ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds ht] with s hs
      exact hloc s hs
    have h2 := hev1.deriv_eq
    simpa using h2
  obtain ⟨x₀, -, hmax⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_isMaxOn
    (⟨(-2 : ℝ), by norm_num⟩ : (Set.Icc (-2 : ℝ) 2).Nonempty)
    (f := fun t : ℝ => |deriv (deriv φ) t|) hcont.continuousOn
  refine ⟨|deriv (deriv φ) x₀|, abs_nonneg _, ?_⟩
  have hK2 : ∀ t : ℝ, |deriv (deriv φ) t| ≤ |deriv (deriv φ) x₀| := by
    intro t
    by_cases ht : |t| ≤ 2
    · exact isMaxOn_iff.mp hmax t (Set.mem_Icc.mpr (abs_le.mp ht))
    · rw [hzero t (lt_of_not_ge ht)]
      simpa using abs_nonneg (deriv (deriv φ) x₀)
  intro k hk z
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hLpos : 0 < Real.log k := Real.log_pos hk1
  have hL0 : Real.log k ≠ 0 := ne_of_gt hLpos
  rcases le_or_gt z 0 with hz | hz
  · have h0 : zF φ k z = 0 :=
      zF_eq_zero_of_notMem hφ hk (fun hc => absurd hc.1 (not_le_of_gt (by
        have : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
        linarith)))
    rw [h0, abs_zero]
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  · have hz0 : z ≠ 0 := ne_of_gt hz
    -- the first derivative of `psiFun` (chain rule)
    have hpsi : ∀ y : ℝ, 0 < y →
        deriv (Work.FTS.EllipticEst.psiFun φ k) y
          = deriv φ (Real.log y / Real.log k) * (y⁻¹ / Real.log k) := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt hy
      have h1 : HasDerivAt φ (deriv φ (Real.log y / Real.log k)) (Real.log y / Real.log k) :=
        ((hφ.1.contDiffAt).differentiableAt smoothOrder_ne_zero).hasDerivAt
      have h2 : HasDerivAt (fun y : ℝ => Real.log y / Real.log k)
          (y⁻¹ / Real.log k) y := (Real.hasDerivAt_log hy0).div_const _
      exact (h1.comp y h2).deriv
    -- `zE` agrees near `z` with `fun y => φ'(log y / log k)/log k`
    have hzE : zE φ k =ᶠ[𝓝 z]
        (fun y => deriv φ (Real.log y / Real.log k) / Real.log k) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      show y * deriv (zeta φ k) y = deriv φ (Real.log y / Real.log k) / Real.log k
      rw [Work.FTS.EllipticEst.Alpha4.zc_deriv_eq hy, hpsi y hy]
      field_simp [ne_of_gt (show (0 : ℝ) < y from hy)]
    have hderiv : deriv (zE φ k) z
        = deriv (deriv φ) (Real.log z / Real.log k) / (z * (Real.log k) ^ 2) := by
      rw [hzE.deriv_eq]
      have hφd : HasDerivAt (deriv φ) (deriv (deriv φ) (Real.log z / Real.log k))
          (Real.log z / Real.log k) :=
        ((hφ1.contDiffAt).differentiableAt smoothOrder_ne_zero).hasDerivAt
      have hg : HasDerivAt (fun y : ℝ => Real.log y / Real.log k)
          (z⁻¹ / Real.log k) z := (Real.hasDerivAt_log hz0).div_const _
      have h1 : HasDerivAt (fun y : ℝ => deriv φ (Real.log y / Real.log k))
          (deriv (deriv φ) (Real.log z / Real.log k) * (z⁻¹ / Real.log k)) z := by
        simpa [Function.comp_def] using hφd.comp z hg
      have h2 : HasDerivAt
          (fun y : ℝ => deriv φ (Real.log y / Real.log k) / Real.log k)
          ((deriv (deriv φ) (Real.log z / Real.log k) * (z⁻¹ / Real.log k))
            / Real.log k) z := h1.div_const _
      rw [h2.deriv]
      field_simp
    show |z * deriv (zE φ k) z| ≤ |deriv (deriv φ) x₀| / (Real.log k) ^ 2
    rw [hderiv]
    have key : |z * (deriv (deriv φ) (Real.log z / Real.log k)
          / (z * (Real.log k) ^ 2))|
        = |deriv (deriv φ) (Real.log z / Real.log k)| / (Real.log k) ^ 2 := by
      rw [abs_mul, abs_div, abs_mul, abs_of_pos hz, abs_of_pos (pow_pos hLpos 2)]
      field_simp [hz0, hL0]
    rw [key]
    exact div_le_div_of_nonneg_right (hK2 _) (sq_nonneg _)

/-- The per-`k` form of the second commutator bound. -/
theorem zF_abs_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K) {k : ℕ}
    (hk : 2 ≤ k) : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ z : ℝ, |zF φ k z| ≤ K₂ / (Real.log k) ^ 2 := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := zF_bound_uniform hφ
  exact ⟨K₂, hK₂0, fun z => hK₂ k hk z⟩

end Work.Blocks.InterpTrunc
