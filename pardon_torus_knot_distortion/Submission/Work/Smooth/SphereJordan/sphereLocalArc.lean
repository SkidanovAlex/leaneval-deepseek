import Mathlib

/-!
# A small arc of a circle is the part of the circle inside a small ball

This file proves `Work.Smooth.SphereJordan.sphereLocalArc`: for a point `x` of the circle
`Metric.sphere w r` (`0 < r`) and a radius `ε` with `0 < ε < 2 r`, the points of the circle at
distance `< ε` from `x` form an *open arc* around `x`, and are exactly the image of an open
interval `(-δ, δ)` under the circular parametrisation based at `x`.

## The mathematics

Write `x = w + r e^{iθ}` (`θ = arg (x - w)`).  For a point `y = w + r e^{i(θ+t)}` of the circle the
distance to `x` is the chord length

  `‖y - x‖ = r ‖e^{i t} - 1‖ = 2 r |sin (t/2)|`,

so `dist y x < ε` iff `|sin (t/2)| < ε/(2r)`.  Since `arcsin` parametrises `sin` on `[-π/2, π/2]`,
and `ε/(2r) < 1`, this is exactly `|t| < δ` for `δ = 2 arcsin (ε/(2r)) < π`.  This gives both
inclusions:

* `t ∈ (-δ, δ)` gives a point of the sphere at distance `< ε` from `x`
  (`sphereLocalArc_arc_image_subset`);
* conversely any `y` of the sphere with `dist y x < ε` satisfies
  `|sin (t/2)| < ε/(2r)` for `t = arg ((y - w)/(x - w))` (taken in `(-π, π]`), hence `|t| < δ`
  (`sphereLocalArc_ball_subset_arc_image`).
-/

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The chord length between `1` and `e^{i t}`, in real terms: `‖e^{it} - 1‖ = 2 |sin (t/2)|`. -/
private lemma norm_exp_mul_I_sub_one (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (t / 2)| := by
  rw [mul_comm (t : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The exponent on the circle based at `θ` is additive. -/
private lemma exp_arg_add (θ t : ℝ) :
    Complex.exp ((((θ + t : ℝ)) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The forward inclusion**: every point of the arc `(-δ, δ)` lies on the sphere `sphere w r` and
inside the ball `ball x ε`, where `δ = 2 arcsin (ε/(2r))`. -/
private lemma arc_image_subset {w x : ℂ} {r ε : ℝ} (hr : 0 < r) (hx : dist x w = r)
    (hε0 : 0 < ε) (hε : ε < 2 * r) :
    (fun t : ℝ => w + (x - w) * Complex.exp ((t : ℂ) * Complex.I)) ''
        Set.Ioo (-(2 * Real.arcsin (ε / (2 * r)))) (2 * Real.arcsin (ε / (2 * r)))
      ⊆ Metric.sphere w r ∩ Metric.ball x ε := by
  have hc : ‖x - w‖ = r := by rw [dist_eq_norm] at hx; exact hx
  rintro y ⟨t, ht, rfl⟩
  rw [Set.mem_inter_iff, Metric.mem_sphere, Metric.mem_ball, dist_eq_norm, dist_eq_norm]
  constructor
  · rw [add_sub_cancel_left, norm_mul, hc, Complex.norm_exp_ofReal_mul_I, mul_one]
  · have h1 : (w + (x - w) * Complex.exp ((t : ℂ) * Complex.I)) - x
        = (x - w) * (Complex.exp ((t : ℂ) * Complex.I) - 1) := by ring
    rw [h1, norm_mul, hc, norm_exp_mul_I_sub_one]
    have hlt : |t| < 2 * Real.arcsin (ε / (2 * r)) := by
      rw [Set.mem_Ioo] at ht; exact abs_lt.mpr ht
    have hk0 : 0 < ε / (2 * r) := div_pos hε0 (by linarith)
    have hk1 : ε / (2 * r) < 1 := (div_lt_one (by linarith : (0 : ℝ) < 2 * r)).mpr hε
    have harc1 : Real.arcsin (ε / (2 * r)) < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
    have hkey1 : |t / 2| < Real.arcsin (ε / (2 * r)) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hxmem : |t / 2| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [abs_nonneg (t / 2)], le_of_lt (lt_trans hkey1 harc1)⟩
    have hymem : ε / (2 * r) ∈ Set.Icc (-1) 1 := by
      rw [Set.mem_Icc]; exact ⟨by linarith [hk0], le_of_lt hk1⟩
    have hsinlt : Real.sin |t / 2| < ε / (2 * r) :=
      (Real.lt_arcsin_iff_sin_lt hxmem hymem).mp hkey1
    have habsle : |t / 2| ≤ Real.pi := by
      linarith [hkey1, harc1, Real.pi_pos]
    have hsin : |Real.sin (t / 2)| = Real.sin |t / 2| :=
      Real.abs_sin_eq_sin_abs_of_abs_le_pi habsle
    rw [hsin]
    have hmul := mul_lt_mul_of_pos_right hsinlt (by linarith : (0 : ℝ) < 2 * r)
    rw [div_mul_cancel₀ _ (by linarith : (2 * r) ≠ 0)] at hmul
    nlinarith [hmul]

/-- **The backward inclusion**: every point `y` of the sphere `sphere w r` at distance `< ε` from
`x` lies on the arc `(-δ, δ)` based at `x`, where `δ = 2 arcsin (ε/(2r))`. -/
private lemma arc_point_of_mem {w x : ℂ} {r ε : ℝ} (hr : 0 < r) (hx : dist x w = r)
    (hε0 : 0 < ε) (hε : ε < 2 * r) {y : ℂ}
    (hyw : dist y w = r) (hyx : dist y x < ε) :
    ∃ t ∈ Set.Ioo (-(2 * Real.arcsin (ε / (2 * r)))) (2 * Real.arcsin (ε / (2 * r))),
      w + (x - w) * Complex.exp ((t : ℂ) * Complex.I) = y := by
  have hcne : x - w ≠ 0 := by
    intro h
    have : ‖x - w‖ = r := by rw [dist_eq_norm] at hx; exact hx
    rw [h, norm_zero] at this; linarith
  have hxw : ‖x - w‖ = r := by rw [dist_eq_norm] at hx; exact hx
  have hyw' : ‖y - w‖ = r := by rw [dist_eq_norm] at hyw; exact hyw
  have hyx' : ‖y - x‖ < ε := by rw [dist_eq_norm] at hyx; exact hyx
  set z : ℂ := (y - w) / (x - w) with hzdef
  have hznorm : ‖z‖ = 1 := by
    rw [hzdef, norm_div, hyw', hxw, div_self (ne_of_gt hr)]
  have hexp : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hznorm] at h
    simpa using h
  have hkey : w + (x - w) * Complex.exp ((z.arg : ℂ) * Complex.I) = y := by
    rw [hexp, hzdef]
    field_simp
    ring
  refine ⟨z.arg, ?_, hkey⟩
  rw [Set.mem_Ioo]
  have hlt : -Real.pi < z.arg := Complex.neg_pi_lt_arg z
  have hle : z.arg ≤ Real.pi := Complex.arg_le_pi z
  have hzn1 : ‖z - 1‖ < ε / r := by
    have he : y - x = (x - w) * (z - 1) := by rw [hzdef]; field_simp; ring
    have h : ‖y - x‖ = r * ‖z - 1‖ := by rw [he, norm_mul, hxw]
    rw [h] at hyx'
    rw [lt_div_iff₀ hr]
    linarith
  have h2sin : 2 * |Real.sin (z.arg / 2)| < ε / r := by
    have h := norm_exp_mul_I_sub_one z.arg
    rw [← h, hexp]
    exact hzn1
  have hsinb : |Real.sin (z.arg / 2)| < ε / (2 * r) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * r)]
    rw [lt_div_iff₀ hr] at h2sin
    nlinarith [h2sin]
  have hk0 : 0 < ε / (2 * r) := div_pos hε0 (by linarith)
  have hk1 : ε / (2 * r) < 1 := (div_lt_one (by linarith : (0 : ℝ) < 2 * r)).mpr hε
  have ha_le_pi : |z.arg / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : |z.arg| ≤ Real.pi := abs_le.mpr ⟨le_of_lt hlt, hle⟩
    linarith
  have hsin_eq : Real.sin |z.arg / 2| = |Real.sin (z.arg / 2)| :=
    (Real.abs_sin_eq_sin_abs_of_abs_le_pi ha_le_pi).symm
  have hsinlt : Real.sin |z.arg / 2| < ε / (2 * r) := by rw [hsin_eq]; exact hsinb
  have ha_mem : |z.arg / 2| ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    refine ⟨by linarith [abs_nonneg (z.arg / 2)], ?_⟩
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : |z.arg| ≤ Real.pi := abs_le.mpr ⟨le_of_lt hlt, hle⟩
    linarith
  have hk_mem : ε / (2 * r) ∈ Set.Icc (-1) 1 := by
    rw [Set.mem_Icc]; exact ⟨by linarith [hk0], le_of_lt hk1⟩
  have hkey2 : |z.arg / 2| < Real.arcsin (ε / (2 * r)) :=
    (Real.lt_arcsin_iff_sin_lt ha_mem hk_mem).mpr hsinlt
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hkey2
  have habs : |z.arg| < 2 * Real.arcsin (ε / (2 * r)) := by linarith
  exact abs_lt.mp habs

/-- The ball part of the sphere is an open arc. -/
private lemma ball_subset_arc_image {w x : ℂ} {r ε : ℝ} (hr : 0 < r) (hx : dist x w = r)
    (hε0 : 0 < ε) (hε : ε < 2 * r) :
    Metric.sphere w r ∩ Metric.ball x ε
      ⊆ (fun t : ℝ => w + (x - w) * Complex.exp ((t : ℂ) * Complex.I)) ''
        Set.Ioo (-(2 * Real.arcsin (ε / (2 * r)))) (2 * Real.arcsin (ε / (2 * r))) := by
  rintro y ⟨hyw, hyx⟩
  rw [Metric.mem_sphere] at hyw
  rw [Metric.mem_ball] at hyx
  exact arc_point_of_mem hr hx hε0 hε hyw hyx

/-- **The arc of the circle cut out by a ball.**  For `x` on `sphere w r` and `0 < ε < 2 r`, the
part of the circle within distance `ε` of `x` is the image of the open interval
`(-δ, δ)`, `δ = 2 arcsin (ε/(2r))`, under the parametrisation `t ↦ w + (x - w) e^{i t}`. -/
private lemma arc_image_eq {w x : ℂ} {r ε : ℝ} (hr : 0 < r) (hx : dist x w = r)
    (hε0 : 0 < ε) (hε : ε < 2 * r) :
    (fun t : ℝ => w + (x - w) * Complex.exp ((t : ℂ) * Complex.I)) ''
        Set.Ioo (-(2 * Real.arcsin (ε / (2 * r)))) (2 * Real.arcsin (ε / (2 * r)))
      = Metric.sphere w r ∩ Metric.ball x ε :=
  Subset.antisymm (arc_image_subset hr hx hε0 hε) (ball_subset_arc_image hr hx hε0 hε)

theorem sphereLocalArc {w x : ℂ} {r ε : ℝ} (hr : 0 < r) (hx : dist x w = r)
    (hε0 : 0 < ε) (hε : ε < 2 * r) :
    ∃ θ : ℝ, x = w + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∧
      ∃ δ > 0, (fun t : ℝ => w + (r : ℂ) * Complex.exp (((θ + t : ℝ) : ℂ) * Complex.I)) ''
        Set.Ioo (-δ) δ = Metric.sphere w r ∩ Metric.ball x ε := by
  have hnorm : ‖x - w‖ = r := by rw [dist_eq_norm] at hx; exact hx
  have hc_eq : x - w = (r : ℂ) * Complex.exp ((Complex.arg (x - w) : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (x - w)
    rw [hnorm] at h
    exact h.symm
  have hfun : (fun t : ℝ =>
        w + (r : ℂ) * Complex.exp (((Complex.arg (x - w) + t : ℝ) : ℂ) * Complex.I))
      = (fun t : ℝ => w + (x - w) * Complex.exp ((t : ℂ) * Complex.I)) := by
    funext t
    rw [exp_arg_add (Complex.arg (x - w)) t]
    conv_rhs => rw [hc_eq]
    ring
  refine ⟨Complex.arg (x - w), ?_, 2 * Real.arcsin (ε / (2 * r)), ?_, ?_⟩
  · rw [← hc_eq]; ring
  · have hk0 : 0 < ε / (2 * r) := div_pos hε0 (by linarith)
    have := Real.arcsin_pos.mpr hk0
    linarith
  · rw [hfun]
    exact arc_image_eq hr hx hε0 hε

end

end Work.Smooth.SphereJordan
