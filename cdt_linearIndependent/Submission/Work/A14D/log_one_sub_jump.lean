import Mathlib
import Submission.Work.A14.defs

/-!
# `Work.A14D.log_one_sub_jump`

The boundary (branch-cut) values of `Complex.log` at the negative real axis: for `1 < x` and
`ε → 0⁺`, the points `1 - (x + ε i)` (lower half-plane) and `1 - (x - ε i)` (upper half-plane)
tend to the cut point `1 - x < 0` from below resp. above, whence

`log (1 - (x + ε i)) → log (x - 1) - π i`,  `log (1 - (x - ε i)) → log (x - 1) + π i`.

The jump of `2πi` across the cut.  Proof: `Complex.log z = log ‖z‖ + (arg z) i`, with
`arg` given on the open half-planes `re < 0` by `arcsin ((-z).im / ‖z‖) ∓ π`.
-/

namespace Work.A14D

open Complex Metric Filter Topology
open scoped Topology

/-- A `Tendsto` for `ℂ`-valued functions is determined by its real and imaginary parts. -/
private lemma tendsto_of_tendsto_re_im {α : Type*} {l : Filter α} {f : α → ℂ} {z : ℂ}
    (hre : Tendsto (fun a => (f a).re) l (𝓝 z.re))
    (him : Tendsto (fun a => (f a).im) l (𝓝 z.im)) : Tendsto f l (𝓝 z) := by
  have h : Tendsto (fun a => ((f a).re : ℂ) + ((f a).im : ℂ) * I) l
      (𝓝 ((z.re : ℂ) + (z.im : ℂ) * I)) :=
    ((Complex.continuous_ofReal.tendsto z.re).comp hre).add
      (Tendsto.mul_const Complex.I ((Complex.continuous_ofReal.tendsto z.im).comp him))
  simpa [Complex.re_add_im] using h

private lemma tendsto_id_nhdsWithin : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private lemma tendsto_ofReal_id_nhdsWithin :
    Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  simpa using tendsto_id_nhdsWithin.ofReal

private lemma re_sub_mul_I (a ε : ℝ) : ((a : ℂ) - ε * I).re = a := by simp
private lemma re_add_mul_I (a ε : ℝ) : ((a : ℂ) + ε * I).re = a := by simp
private lemma im_neg_sub_mul_I (a ε : ℝ) : (-((a : ℂ) - ε * I)).im = ε := by simp
private lemma im_neg_add_mul_I (a ε : ℝ) : (-((a : ℂ) + ε * I)).im = -ε := by simp
private lemma im_sub_mul_I (a ε : ℝ) : ((a : ℂ) - ε * I).im = -ε := by simp
private lemma im_add_mul_I (a ε : ℝ) : ((a : ℂ) + ε * I).im = ε := by simp

private lemma tendsto_norm_sub {a : ℝ} (ha : a < 0) :
    Tendsto (fun ε : ℝ => ‖(a : ℂ) - ε * I‖) (𝓝[>] (0:ℝ)) (𝓝 (-a)) := by
  have h1 : Tendsto (fun ε : ℝ => (a : ℂ) - ε * I) (𝓝[>] (0:ℝ)) (𝓝 (a : ℂ)) := by
    simpa using tendsto_const_nhds.sub (Tendsto.mul_const Complex.I tendsto_ofReal_id_nhdsWithin)
  have h2 : Tendsto (fun ε : ℝ => ‖(a : ℂ) - ε * I‖) (𝓝[>] (0:ℝ)) (𝓝 ‖(a : ℂ)‖) :=
    (continuous_norm.tendsto (a : ℂ)).comp h1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha] using h2

private lemma tendsto_norm_add {a : ℝ} (ha : a < 0) :
    Tendsto (fun ε : ℝ => ‖(a : ℂ) + ε * I‖) (𝓝[>] (0:ℝ)) (𝓝 (-a)) := by
  have h1 : Tendsto (fun ε : ℝ => (a : ℂ) + ε * I) (𝓝[>] (0:ℝ)) (𝓝 (a : ℂ)) := by
    simpa using tendsto_const_nhds.add (Tendsto.mul_const Complex.I tendsto_ofReal_id_nhdsWithin)
  have h2 : Tendsto (fun ε : ℝ => ‖(a : ℂ) + ε * I‖) (𝓝[>] (0:ℝ)) (𝓝 ‖(a : ℂ)‖) :=
    (continuous_norm.tendsto (a : ℂ)).comp h1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ha] using h2

/-- `arg (a - ε i) → -π` for `a < 0`: the cut is approached from below. -/
private lemma tendsto_arg_sub_mul_I {a : ℝ} (ha : a < 0) :
    Tendsto (fun ε : ℝ => Complex.arg ((a : ℂ) - ε * I)) (𝓝[>] (0:ℝ)) (𝓝 (-Real.pi)) := by
  have hden := tendsto_norm_sub ha
  have hnum : Tendsto (fun ε : ℝ => (-((a : ℂ) - ε * I)).im) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [im_neg_sub_mul_I] using tendsto_id_nhdsWithin
  have hq : Tendsto (fun ε : ℝ => (-((a : ℂ) - ε * I)).im / ‖(a : ℂ) - ε * I‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hnum.div hden (by linarith : (-a : ℝ) ≠ 0)
    rw [zero_div] at h
    exact h
  have harc : Tendsto (fun ε : ℝ => Real.arcsin ((-((a : ℂ) - ε * I)).im / ‖(a : ℂ) - ε * I‖))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.arcsin_zero] using hq.arcsin
  have harc' : Tendsto
      (fun ε : ℝ => Real.arcsin ((-((a : ℂ) - ε * I)).im / ‖(a : ℂ) - ε * I‖) - Real.pi)
      (𝓝[>] (0:ℝ)) (𝓝 (-Real.pi)) := by
    simpa only [zero_sub] using harc.sub_const Real.pi
  refine Tendsto.congr' ?_ harc'
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  have hεpos' : 0 < ε := hεpos
  have hre : ((a : ℂ) - ε * I).re < 0 := by simpa only [re_sub_mul_I] using ha
  have him : ((a : ℂ) - ε * I).im < 0 := by
    rw [im_sub_mul_I]; linarith
  exact (Complex.arg_of_re_neg_of_im_neg hre him).symm

/-- `arg (a + ε i) → π` for `a < 0`: the cut is approached from above. -/
private lemma tendsto_arg_add_mul_I {a : ℝ} (ha : a < 0) :
    Tendsto (fun ε : ℝ => Complex.arg ((a : ℂ) + ε * I)) (𝓝[>] (0:ℝ)) (𝓝 Real.pi) := by
  have hden := tendsto_norm_add ha
  have hnum : Tendsto (fun ε : ℝ => (-((a : ℂ) + ε * I)).im) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [im_neg_add_mul_I, neg_zero] using tendsto_id_nhdsWithin.neg
  have hq : Tendsto (fun ε : ℝ => (-((a : ℂ) + ε * I)).im / ‖(a : ℂ) + ε * I‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := hnum.div hden (by linarith : (-a : ℝ) ≠ 0)
    rw [zero_div] at h
    exact h
  have harc : Tendsto (fun ε : ℝ => Real.arcsin ((-((a : ℂ) + ε * I)).im / ‖(a : ℂ) + ε * I‖))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.arcsin_zero] using hq.arcsin
  have harc' : Tendsto
      (fun ε : ℝ => Real.arcsin ((-((a : ℂ) + ε * I)).im / ‖(a : ℂ) + ε * I‖) + Real.pi)
      (𝓝[>] (0:ℝ)) (𝓝 Real.pi) := by
    simpa only [zero_add] using harc.add_const Real.pi
  refine Tendsto.congr' ?_ harc'
  filter_upwards [self_mem_nhdsWithin] with ε hεpos
  have hεpos' : 0 < ε := hεpos
  have hre : ((a : ℂ) + ε * I).re < 0 := by simpa only [re_add_mul_I] using ha
  have him : 0 ≤ ((a : ℂ) + ε * I).im := by rw [im_add_mul_I]; linarith
  exact (Complex.arg_of_re_neg_of_im_nonneg hre him).symm

theorem log_one_sub_jump (x : ℝ) (hx : 1 < x) :
    Tendsto (fun ε : ℝ => Complex.log (1 - (x + ε * Complex.I))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.log (x - 1) - Real.pi * Complex.I)) ∧
      Tendsto (fun ε : ℝ => Complex.log (1 - (x - ε * Complex.I))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.log (x - 1) + Real.pi * Complex.I)) := by
  have hx1 : (0 : ℝ) < x - 1 := sub_pos.mpr hx
  have hxn : (1 : ℝ) - x < 0 := by linarith
  have hcast1 : ∀ ε : ℝ, (1 : ℂ) - (x + ε * Complex.I) = ((1 - x : ℝ) : ℂ) - ε * Complex.I := by
    intro ε; push_cast; ring
  have hcast2 : ∀ ε : ℝ, (1 : ℂ) - (x - ε * Complex.I) = ((1 - x : ℝ) : ℂ) + ε * Complex.I := by
    intro ε; push_cast; ring
  have hnorm1 : Tendsto (fun ε : ℝ => ‖(1 : ℂ) - (x + ε * Complex.I)‖) (𝓝[>] (0:ℝ))
      (𝓝 (x - 1)) := by
    have h := tendsto_norm_sub hxn
    rw [neg_sub] at h
    simpa only [hcast1] using h
  have hnorm2 : Tendsto (fun ε : ℝ => ‖(1 : ℂ) - (x - ε * Complex.I)‖) (𝓝[>] (0:ℝ))
      (𝓝 (x - 1)) := by
    have h := tendsto_norm_add hxn
    rw [neg_sub] at h
    simpa only [hcast2] using h
  have hre1 : Tendsto (fun ε : ℝ => (Complex.log (1 - (x + ε * Complex.I))).re)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.log (x - 1))) := by
    refine Tendsto.congr (f₁ := fun ε : ℝ => Real.log ‖(1 : ℂ) - (x + ε * Complex.I)‖)
      (fun ε => ?_) ?_
    · rw [Complex.log_re]
    · exact (Real.continuousAt_log (ne_of_gt hx1)).tendsto.comp hnorm1
  have him1 : Tendsto (fun ε : ℝ => (Complex.log (1 - (x + ε * Complex.I))).im)
      (𝓝[>] (0:ℝ)) (𝓝 (-Real.pi)) := by
    refine Tendsto.congr
      (f₁ := fun ε : ℝ => Complex.arg (((1 - x : ℝ) : ℂ) - ε * Complex.I)) (fun ε => ?_) ?_
    · rw [Complex.log_im, hcast1]
    · exact tendsto_arg_sub_mul_I hxn
  have hre2 : Tendsto (fun ε : ℝ => (Complex.log (1 - (x - ε * Complex.I))).re)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.log (x - 1))) := by
    refine Tendsto.congr (f₁ := fun ε : ℝ => Real.log ‖(1 : ℂ) - (x - ε * Complex.I)‖)
      (fun ε => ?_) ?_
    · rw [Complex.log_re]
    · exact (Real.continuousAt_log (ne_of_gt hx1)).tendsto.comp hnorm2
  have him2 : Tendsto (fun ε : ℝ => (Complex.log (1 - (x - ε * Complex.I))).im)
      (𝓝[>] (0:ℝ)) (𝓝 Real.pi) := by
    refine Tendsto.congr
      (f₁ := fun ε : ℝ => Complex.arg (((1 - x : ℝ) : ℂ) + ε * Complex.I)) (fun ε => ?_) ?_
    · rw [Complex.log_im, hcast2]
    · exact tendsto_arg_add_mul_I hxn
  exact ⟨tendsto_of_tendsto_re_im (by simpa using hre1) (by simpa using him1),
         tendsto_of_tendsto_re_im (by simpa using hre2) (by simpa using him2)⟩

end Work.A14D
