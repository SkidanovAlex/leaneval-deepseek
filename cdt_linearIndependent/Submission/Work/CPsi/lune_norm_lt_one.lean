import Mathlib
import Submission.Work.CPsi.psiC_deps

/-!
# `‖lune (23/10) z‖ < 1` on the open unit disc

The lune map `h(z,c)` of arXiv:2408.15403 is the (right) inverse of the degree-two rational map
`f w = w (B + C w)/(C + B w)` with `B = 1 + c²`, `C = c² - 1`.  At `c = 23/10` the algebraic
facts `f (lune c z) = z` for every `z` and `‖w‖ = 1 → ‖f w‖ = 1` are available in `psiC_base`,
and `lune c` is holomorphic on the open unit disc because the radicand avoids the branch cut
`(-∞,0]` there.

Consequently, for fixed `z` with `‖z‖ < 1`, the modulus `t ↦ ‖lune (tz)‖` is continuous on
`[0,1]`, equals `0` at `t = 0`, and never takes the value `1` (it would force `‖tz‖ = 1`).
By the intermediate value theorem it stays `< 1`, so `lune (23/10)` maps the open unit disc into
the open unit disc.
-/

namespace Work.CPsi

open Metric
open scoped Topology

theorem lune_norm_lt_one : ∀ z : ℂ, ‖z‖ < 1 → ‖Submission.CDTPlan.lune (23 / 10) z‖ < 1 := by
  -- The lune map is continuous on the open unit disc (the radicand avoids the branch cut).
  have hgobL : ContinuousOn gobL (ball 0 1) := by
    have hR : ContinuousOn gobR (ball 0 1) := by
      unfold gobR; fun_prop
    have hsqrt : ContinuousOn (fun z => (gobR z) ^ (1 / 2 : ℂ)) (ball 0 1) :=
      hR.cpow_const (fun z hz =>
        gobR_slitPlane_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz))
    have hnum : ContinuousOn (fun z => gB * z - gB + (gobR z) ^ (1 / 2 : ℂ)) (ball 0 1) :=
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).add hsqrt
    have h := hnum.div_const (2 * gC)
    unfold gobL
    exact h
  intro z hz
  rw [lune_eq z]
  -- The modulus profile along the segment `t ↦ t z`.
  let F : ℝ → ℝ := fun t => ‖gobL ((t : ℂ) * z)‖
  have hlt_of : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖((t : ℂ) * z)‖ < 1 := by
    intro t ht
    have hn : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
    rw [norm_mul, hn, abs_of_nonneg ht.1]
    calc t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
      _ = ‖z‖ := one_mul _
      _ < 1 := hz
  have hmaps : Set.MapsTo (fun t : ℝ => ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) (ball 0 1) := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hlt_of t ht
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have h1 : ContinuousOn (fun t : ℝ => ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) :=
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
    have h2 : ContinuousOn (fun t : ℝ => gobL ((t : ℂ) * z)) (Set.Icc (0 : ℝ) 1) :=
      hgobL.comp h1 hmaps
    simpa only [F] using h2.norm
  have hF0 : F 0 = 0 := by
    simp only [F, Complex.ofReal_zero, zero_mul, gobL_zero, norm_zero]
  -- The profile never reaches the value `1`: that would force `‖t z‖ = 1`.
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t ≠ 1 := by
    intro t ht hFt
    have hw : ‖gobL ((t : ℂ) * z)‖ = 1 := by simpa only [F] using hFt
    have h1 : ‖gobF (gobL ((t : ℂ) * z))‖ = 1 := norm_gobF_eq_one hw
    rw [gobF_gobL] at h1
    exact (ne_of_lt (hlt_of t ht)) h1
  rcases lt_or_gt_of_ne (hne 1 (by norm_num)) with h | h
  · simpa only [F, Complex.ofReal_one, one_mul] using h
  · exfalso
    have hmem0 : (1 : ℝ) ∈ Set.Icc (F 0) (F 1) := by
      rw [hF0]; exact ⟨zero_le_one, le_of_lt h⟩
    rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont) hmem0 with
      ⟨t, ht, hFt⟩
    exact hne t ht hFt

end Work.CPsi
