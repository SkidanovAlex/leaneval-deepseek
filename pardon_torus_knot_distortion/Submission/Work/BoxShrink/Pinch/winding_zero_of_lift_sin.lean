import Mathlib
import Submission.Work.CoreTopology.Winding
import Submission.Work.SurgeryInvariance.Defs

/-!
# Vanishing of the winding vector from sign conditions on a lift

Let `P` be a parametrised torus, `γ` a closed curve of `P` and `L : LiftOf P γ` a lift of `γ`
to the parameter plane `ℝ²`, with coordinates `(L.Θ, L.Φ)`.

* If `sin (L.Θ t) > 0` for every `t`, then the longitude parameter `Θ` stays inside one of the
  intervals `(2kπ, (2k+1)π)`, hence advances by strictly less than `π` over a period; since that
  advance is an integer multiple of `2π`, the first winding number vanishes.

* If `|sin (L.Φ t)| < 1` for every `t`, then `Φ` never meets the lattice `π/2 + πℤ`; but over a
  period `Φ` advances by an integer multiple of `2π`, and if that integer were nonzero the
  intermediate value theorem would produce a time at which `Φ` meets that lattice.  Hence the
  second winding number vanishes.

The two statements are proved here in the slightly more general form "a continuous function `f`
with `f (2π) - f 0 = m · 2π` and such a sign condition has `m = 0`", and then applied to the two
coordinate functions of the lift.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- Any closed interval of `ℝ` of length at least `π` contains an integer multiple of `π`. -/
lemma exists_int_mul_pi_mem_Icc {a b : ℝ} (h : Real.pi ≤ b - a) :
    ∃ k : ℤ, (k : ℝ) * Real.pi ∈ Set.Icc a b := by
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨⌈a / Real.pi⌉, ?_, ?_⟩
  · have hle : a / Real.pi ≤ (⌈a / Real.pi⌉ : ℝ) := Int.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right hle (le_of_lt hπ)
    rwa [div_mul_cancel₀ a (ne_of_gt hπ)] at h2
  · have hlt : (⌈a / Real.pi⌉ : ℝ) < a / Real.pi + 1 := Int.ceil_lt_add_one _
    have h2 := mul_lt_mul_of_pos_right hlt hπ
    have h3 : (a / Real.pi + 1) * Real.pi = a + Real.pi := by
      rw [add_mul, one_mul, div_mul_cancel₀ a (ne_of_gt hπ)]
    rw [h3] at h2
    linarith

/-- Any closed interval of `ℝ` of length at least `π` contains a point of the lattice
`π/2 + πℤ`, i.e. a point at which `|sin| = 1`. -/
lemma exists_pi_half_add_int_mul_pi_mem_Icc {a b : ℝ} (h : Real.pi ≤ b - a) :
    ∃ k : ℤ, Real.pi / 2 + (k : ℝ) * Real.pi ∈ Set.Icc a b := by
  obtain ⟨k, hk⟩ :=
    exists_int_mul_pi_mem_Icc (a := a - Real.pi/2) (b := b - Real.pi/2) (by linarith)
  exact ⟨k, by constructor <;> linarith [hk.1, hk.2]⟩

/-- A continuous function attains every value between `f a` and `f b`, i.e. every value in the
interval spanned by the two endpoint values. -/
lemma exists_mem_Icc_eq_of_between {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    {y : ℝ} (hy : y ∈ Set.Icc (min (f a) (f b)) (max (f a) (f b))) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  rcases le_total (f a) (f b) with h | h
  · have hy' : y ∈ Set.Icc (f a) (f b) := by simpa [min_eq_left h, max_eq_right h] using hy
    obtain ⟨c, hc, hfc⟩ := (intermediate_value_Icc hab hf.continuousOn) hy'
    exact ⟨c, hc, hfc⟩
  · have hy' : y ∈ Set.Icc (f b) (f a) := by simpa [min_eq_right h, max_eq_left h] using hy
    obtain ⟨c, hc, hfc⟩ := (intermediate_value_Icc' hab hf.continuousOn) hy'
    exact ⟨c, hc, hfc⟩

/-- The length of the interval spanned by `x` and `y` is `|y - x|`. -/
lemma abs_minmax_sub (x y : ℝ) : max x y - min x y = |y - x| := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonneg (by linarith)]
  · rw [max_eq_left h, min_eq_right h, abs_of_nonpos (by linarith)]; ring

/-- A nonzero integer has absolute value at least `1`, also as a real number. -/
lemma abs_int_cast_ge_one (m : ℤ) (hm : m ≠ 0) : (1 : ℝ) ≤ |(m : ℝ)| := by
  have h1 := Int.one_le_abs hm
  calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
    _ ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast h1
    _ = |(m : ℝ)| := Int.cast_abs

/-- If `sin (f t) > 0` for all `t` and `f (2π) - f 0 = m · 2π`, then `m = 0`: the parameter
advances by strictly less than `π` over a period. -/
lemma eq_zero_of_cont_sin_pos {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, 0 < Real.sin (f t)) {m : ℤ}
    (hdiff : f (2 * Real.pi) - f 0 = (m : ℝ) * (2 * Real.pi)) : m = 0 := by
  by_contra hm
  have hbig : Real.pi ≤ |f (2 * Real.pi) - f 0| := by
    have hprod : (1 : ℝ) * (2 * Real.pi) ≤ |(m : ℝ)| * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right (abs_int_cast_ge_one m hm) (by positivity)
    rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    linarith [Real.pi_pos]
  have hlen : Real.pi ≤ max (f 0) (f (2 * Real.pi)) - min (f 0) (f (2 * Real.pi)) := by
    rw [abs_minmax_sub]; linarith
  obtain ⟨k, hk⟩ := exists_int_mul_pi_mem_Icc hlen
  obtain ⟨c, hc, hfc⟩ := exists_mem_Icc_eq_of_between hf (by positivity) hk
  have hc' := h c
  rw [hfc, Real.sin_int_mul_pi] at hc'
  exact lt_irrefl 0 hc'

/-- If `|sin (f t)| < 1` for all `t` and `f (2π) - f 0 = m · 2π`, then `m = 0`: otherwise the
intermediate value theorem produces a time at which `f` meets the lattice `π/2 + πℤ`. -/
lemma eq_zero_of_cont_abs_sin_lt_one {f : ℝ → ℝ} (hf : Continuous f)
    (h : ∀ t : ℝ, |Real.sin (f t)| < 1) {m : ℤ}
    (hdiff : f (2 * Real.pi) - f 0 = (m : ℝ) * (2 * Real.pi)) : m = 0 := by
  by_contra hm
  have hbig : Real.pi ≤ |f (2 * Real.pi) - f 0| := by
    have hprod : (1 : ℝ) * (2 * Real.pi) ≤ |(m : ℝ)| * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_right (abs_int_cast_ge_one m hm) (by positivity)
    rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    linarith [Real.pi_pos]
  have hlen : Real.pi ≤ max (f 0) (f (2 * Real.pi)) - min (f 0) (f (2 * Real.pi)) := by
    rw [abs_minmax_sub]; linarith
  obtain ⟨k, hk⟩ := exists_pi_half_add_int_mul_pi_mem_Icc hlen
  obtain ⟨c, hc, hfc⟩ := exists_mem_Icc_eq_of_between hf (by positivity) hk
  have hc' := h c
  rw [hfc] at hc'
  have h1 : |Real.sin (Real.pi/2 + (k:ℝ)*Real.pi)| = 1 := Real.abs_sin_eq_one_iff.mpr ⟨k, rfl⟩
  linarith

theorem winding_zero_of_lift_sin {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ)
    (hΘ : ∀ t : ℝ, 0 < Real.sin (L.Θ t))
    (hΦ : ∀ t : ℝ, |Real.sin (L.Φ t)| < 1) :
    Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
  rw [Work.SurgeryInvariance.windingOf_eq P γ L]
  have hspec := L.winding_spec
  refine Prod.ext ?_ ?_
  · exact eq_zero_of_cont_sin_pos L.contΘ hΘ (by rw [hspec.1]; ring)
  · exact eq_zero_of_cont_abs_sin_lt_one L.contΦ hΦ (by rw [hspec.2]; ring)

end

end Work.BoxShrink.Pinch
