import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.wirt_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst

/-- Elementary bound: if `|A| ≤ C * |s|`, `C ≥ 0` and `|B| ≤ 1`, then
`|r * A ^ 2 * (B / s)| ≤ r * C ^ 2 * |s|` for `r > 0`.  (With Lean's totalised division the
case `s = 0` is immediate since then `B / 0 = 0`.) -/
private theorem abs_mul_sq_div_le_aux {r C A B s : ℝ} (hr : 0 < r) (_hC : 0 ≤ C)
    (hA : |A| ≤ C * |s|) (hB : |B| ≤ 1) : |r * A ^ 2 * (B / s)| ≤ r * C ^ 2 * |s| := by
  rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos hr]
  have hs : 0 ≤ |s| := abs_nonneg s
  have hsq : |A| ^ 2 ≤ C ^ 2 * |s| ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg A) hA 2
    rwa [mul_pow] at h
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]
    simp
  · have hmul : C ^ 2 * |s| ^ 2 * (1 / |s|) = C ^ 2 * |s| := by field_simp
    have h1 : |B| / |s| ≤ 1 / |s| := div_le_div_of_nonneg_right hB hs
    have h2 : |A| ^ 2 * (|B| / |s|) ≤ C ^ 2 * |s| := by
      calc |A| ^ 2 * (|B| / |s|) ≤ |A| ^ 2 * (1 / |s|) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ ≤ C ^ 2 * |s| ^ 2 * (1 / |s|) :=
            mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = C ^ 2 * |s| := hmul
    have h3 := mul_le_mul_of_nonneg_left h2 hr.le
    linarith [h3]

theorem wirt_phi_tendsto {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    Filter.Tendsto (fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))))
        (nhdsWithin a (Set.Ioi a)) (nhds 0) ∧
      Filter.Tendsto (fun x => r * (u x) ^ 2 * (Real.cos (r * (x - a)) / Real.sin (r * (x - a))))
        (nhdsWithin b (Set.Iio b)) (nhds 0) := by
  -- `u` vanishes to first order at both endpoints: it is dominated by `|sin (r · - a)|`.
  obtain ⟨C, hC0, hC⟩ := wirt_sin_bound hab hr hrb hu ha hb
  -- each of the two filters eventually stays inside `[a, b]`, where the bound applies.
  have hmem_a : Set.Icc a b ∈ nhdsWithin a (Set.Ioi a) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, hab, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hmem_b : Set.Icc a b ∈ nhdsWithin b (Set.Iio b) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Ioi a, isOpen_Ioi, hab, fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩
  -- the sine majorant tends to `0` at both endpoints (`sin 0 = 0`, `sin π = 0`).
  have hg_a : Filter.Tendsto (fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|)
      (nhdsWithin a (Set.Ioi a)) (nhds 0) := by
    have hc : Continuous fun x : ℝ => Real.sin (r * (x - a)) := by fun_prop
    have h : Filter.Tendsto (fun x : ℝ => Real.sin (r * (x - a)))
        (nhdsWithin a (Set.Ioi a)) (nhds 0) := by
      simpa [Real.sin_zero] using (hc.tendsto a).mono_left nhdsWithin_le_nhds
    simpa using h.abs.const_mul (r * C ^ 2)
  have hg_b : Filter.Tendsto (fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|)
      (nhdsWithin b (Set.Iio b)) (nhds 0) := by
    have hc : Continuous fun x : ℝ => Real.sin (r * (x - a)) := by fun_prop
    have h : Filter.Tendsto (fun x : ℝ => Real.sin (r * (x - a)))
        (nhdsWithin b (Set.Iio b)) (nhds 0) := by
      simpa [hrb, Real.sin_pi] using (hc.tendsto b).mono_left nhdsWithin_le_nhds
    simpa using h.abs.const_mul (r * C ^ 2)
  refine ⟨?_, ?_⟩
  · refine squeeze_zero_norm' (a := fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|) ?_ hg_a
    filter_upwards [hmem_a] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_sq_div_le_aux hr hC0 (hC x hx) (Real.abs_cos_le_one _)
  · refine squeeze_zero_norm' (a := fun x : ℝ => r * C ^ 2 * |Real.sin (r * (x - a))|) ?_ hg_b
    filter_upwards [hmem_b] with x hx
    rw [Real.norm_eq_abs]
    exact abs_mul_sq_div_le_aux hr hC0 (hC x hx) (Real.abs_cos_le_one _)

end Work.FTS.EllipticEst
