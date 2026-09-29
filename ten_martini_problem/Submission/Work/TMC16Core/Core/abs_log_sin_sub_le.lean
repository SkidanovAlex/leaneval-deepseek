import Mathlib

namespace Work.TMC16Core.Core

/-- For `0 ≤ y ≤ π / 2` we have `y * cos y ≤ sin y`. -/
private lemma mul_cos_le_sin {y : ℝ} (hy0 : 0 ≤ y) (hy2 : y ≤ Real.pi / 2) :
    y * Real.cos y ≤ Real.sin y := by
  rcases lt_or_eq_of_le hy2 with h | h
  · have hcos : 0 < Real.cos y :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
    have htan : y ≤ Real.tan y := Real.le_tan hy0 h
    rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hcos] at htan
    exact htan
  · rw [h, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two]
    norm_num

/-- On `[a, b]` with `0 < a ≤ b ≤ 1 / 2`, the function
`t ↦ log (sin (π t)) - log t` is antitone. -/
private lemma log_sin_sub_log_antitone {a b : ℝ} (ha : 0 < a) (hb2 : b ≤ 1 / 2)
    (hle : a ≤ b) :
    AntitoneOn (fun t : ℝ => Real.log (Real.sin (Real.pi * t)) - Real.log t)
      (Set.Icc a b) := by
  have hsin_pos : ∀ t ∈ Set.Icc a b, 0 < Real.sin (Real.pi * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have ht2 : t ≤ 1 / 2 := le_trans ht.2 hb2
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, ht2])
  have hcont : ContinuousOn
      (fun t : ℝ => Real.log (Real.sin (Real.pi * t)) - Real.log t) (Set.Icc a b) := by
    have h1 : ContinuousOn (fun t : ℝ => Real.log (Real.sin (Real.pi * t)))
        (Set.Icc a b) :=
      ContinuousOn.log
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
        (fun t ht => (hsin_pos t ht).ne')
    have h2 : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc a b) :=
      ContinuousOn.log continuousOn_id
        (fun t ht => ne_of_gt (lt_of_lt_of_le ha ht.1))
    exact h1.sub h2
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s : ℝ => Real.log (Real.sin (Real.pi * s)) - Real.log s)
        (Real.cos (Real.pi * t) * Real.pi / Real.sin (Real.pi * t) - t⁻¹) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have ht2 : t ≤ 1 / 2 := le_trans ht.2.le hb2
    have hsin_ne : Real.sin (Real.pi * t) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, ht2])).ne'
    have hlin : HasDerivAt (fun s : ℝ => Real.pi * s) Real.pi t :=
      hasDerivAt_const_mul (x := t) Real.pi
    have hsin_d : HasDerivAt (fun s : ℝ => Real.sin (Real.pi * s))
        (Real.cos (Real.pi * t) * Real.pi) t :=
      hlin.sin
    have hlogsin : HasDerivAt (fun s : ℝ => Real.log (Real.sin (Real.pi * s)))
        (Real.cos (Real.pi * t) * Real.pi / Real.sin (Real.pi * t)) t :=
      hsin_d.log hsin_ne
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0.ne'
    exact hlogsin.sub hlog
  have hneg : ∀ t ∈ Set.Ioo a b,
      Real.cos (Real.pi * t) * Real.pi / Real.sin (Real.pi * t) - t⁻¹ ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have ht2 : t ≤ 1 / 2 := le_trans ht.2.le hb2
    have hsp : 0 < Real.sin (Real.pi * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, ht2])
    have hbase : (Real.pi * t) * Real.cos (Real.pi * t) ≤ Real.sin (Real.pi * t) :=
      mul_cos_le_sin (by positivity) (by nlinarith [Real.pi_pos, ht2])
    rw [sub_nonpos, div_le_iff₀ hsp, inv_mul_eq_div, le_div_iff₀ ht0]
    nlinarith [hbase]
  exact antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Icc a b)
    (f := fun t : ℝ => Real.log (Real.sin (Real.pi * t)) - Real.log t)
    (f' := fun t : ℝ => Real.cos (Real.pi * t) * Real.pi / Real.sin (Real.pi * t) - t⁻¹)
    (convex_Icc a b) hcont
    (fun t ht => (hderiv t (by rwa [interior_Icc] at ht)).hasDerivWithinAt)
    (fun t ht => hneg t (by rwa [interior_Icc] at ht))

/-- The case `a ≤ b` of the main estimate. -/
private lemma abs_log_sin_sub_le_of_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ≤ 1 / 2) (hb2 : b ≤ 1 / 2) (hle : a ≤ b) :
    |Real.log (Real.sin (Real.pi * a)) - Real.log (Real.sin (Real.pi * b))|
      ≤ |a - b| / min a b := by
  have habsab : |a - b| = b - a := by
    rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
    ring
  rw [min_eq_left hle, habsab]
  have hsinapos : 0 < Real.sin (Real.pi * a) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, ha2])
  have hsin_le : Real.sin (Real.pi * a) ≤ Real.sin (Real.pi * b) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos, ha]) (by nlinarith [Real.pi_pos, hb2])
      (by nlinarith [Real.pi_pos, hle])
  have hlogle : Real.log (Real.sin (Real.pi * a)) ≤ Real.log (Real.sin (Real.pi * b)) :=
    Real.log_le_log hsinapos hsin_le
  have habs : |Real.log (Real.sin (Real.pi * a)) - Real.log (Real.sin (Real.pi * b))|
      = Real.log (Real.sin (Real.pi * b)) - Real.log (Real.sin (Real.pi * a)) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlogle)]
    ring
  rw [habs]
  have hanti := log_sin_sub_log_antitone ha hb2 hle
  have hkey : Real.log (Real.sin (Real.pi * b)) - Real.log (Real.sin (Real.pi * a))
      ≤ Real.log b - Real.log a := by
    have h := hanti (Set.left_mem_Icc.mpr hle) (Set.right_mem_Icc.mpr hle) hle
    linarith
  calc Real.log (Real.sin (Real.pi * b)) - Real.log (Real.sin (Real.pi * a))
      ≤ Real.log b - Real.log a := hkey
    _ = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
    _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    _ = (b - a) / a := by rw [sub_div, div_self ha.ne']

theorem abs_log_sin_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha2 : a ≤ 1 / 2)
    (hb2 : b ≤ 1 / 2) :
    |Real.log (Real.sin (Real.pi * a)) - Real.log (Real.sin (Real.pi * b))|
      ≤ |a - b| / min a b := by
  rcases le_total a b with hle | hle
  · exact abs_log_sin_sub_le_of_le ha hb ha2 hb2 hle
  · have h := abs_log_sin_sub_le_of_le hb ha hb2 ha2 hle
    have e1 : |Real.log (Real.sin (Real.pi * b)) - Real.log (Real.sin (Real.pi * a))|
        = |Real.log (Real.sin (Real.pi * a)) - Real.log (Real.sin (Real.pi * b))| :=
      abs_sub_comm _ _
    have e2 : |b - a| = |a - b| := abs_sub_comm b a
    have e3 : min b a = min a b := min_comm b a
    rw [e1, e2, e3] at h
    exact h

end Work.TMC16Core.Core
