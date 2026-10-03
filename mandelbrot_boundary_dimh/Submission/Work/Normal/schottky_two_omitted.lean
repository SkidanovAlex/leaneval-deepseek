import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.bloch_unit
import Submission.Work.Normal.exists_cos_eq_int_of_ball
import Submission.Work.Normal.exists_differentiableOn_cos_eq
import Submission.Work.Escape.exists_differentiableOn_ball_clog

/-!
# Schottky's theorem for two omitted values

A holomorphic function on the unit disk that omits `0` and `1` is bounded on every compact
subset of the disk by a constant depending only on the value at `0`.  This is Schottky's
theorem.

The proof is the classical one based on Bloch's theorem together with the explicit structure
of the omitted set of the "second" lift: if `f` omits `0` and `1`, then `L = log f` omits
`2πiℤ`, hence `g = L / (2πi)` omits `ℤ`, hence (taking a lift through `cos`) `cos h = g` with
`h` omitting `cos⁻¹(ℤ)`.  The set `cos⁻¹(ℤ)` contains `2πk ± i·arcosh m` and therefore meets
every disk of radius `> 4`; Bloch's theorem forces the image of `h` to contain a disk of radius
proportional to `|h'|`, which bounds `h'` on compact subsets.  A mean value estimate then
bounds `h`, and `|f| = exp(-2π Im (cos h)) ≤ exp(2π exp |h|)`.
-/

namespace Work.Normal

open Complex Metric Set Filter
open scoped Topology

noncomputable section

/-! ### Elementary facts about `Complex.cos` -/

lemma cnorm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by rw [h]
    _ = |r| := Real.sqrt_sq_eq_abs r

lemma mem_ball_zero_iff' {z : ℂ} {r : ℝ} : z ∈ Metric.ball 0 r ↔ ‖z‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]

lemma cos_eq_ofReal_sub (w : ℂ) :
    Complex.cos w
      = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ)
        - ((Real.sin w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  ring

lemma cos_sq_norm (w : ℂ) :
    ‖Complex.cos w‖ ^ 2
      = (Real.cos w.re * Real.cosh w.im) ^ 2 + (Real.sin w.re * Real.sinh w.im) ^ 2 := by
  rw [cos_eq_ofReal_sub w, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    sub_zero, zero_sub, zero_mul, add_zero]
  ring

lemma norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp ‖w‖ := by
  have hsq := cos_sq_norm w
  have hcosh0 : 0 < Real.cosh w.im := Real.cosh_pos _
  have hsinh : (Real.sinh w.im) ^ 2 ≤ (Real.cosh w.im) ^ 2 := by
    rw [Real.cosh_sq]; linarith [sq_nonneg (Real.sinh w.im)]
  have hsqle : ‖Complex.cos w‖ ^ 2 ≤ (Real.cosh w.im) ^ 2 := by
    have hstep : (Real.sin w.re) ^ 2 * (Real.sinh w.im) ^ 2
        ≤ (Real.sin w.re) ^ 2 * (Real.cosh w.im) ^ 2 :=
      mul_le_mul_of_nonneg_left hsinh (sq_nonneg (Real.sin w.re))
    have hsum : (Real.sin w.re) ^ 2 + (Real.cos w.re) ^ 2 = 1 := Real.sin_sq_add_cos_sq w.re
    nlinarith [hsq, hstep, hsum, sq_nonneg (Real.cosh w.im)]
  have hle2 : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
    nlinarith [norm_nonneg (Complex.cos w), hcosh0, hsqle]
  have hle3 : Real.cosh w.im ≤ Real.exp ‖w‖ := by
    have h1 : Real.cosh w.im ≤ Real.exp |w.im| := by
      rw [Real.cosh_eq]
      have ha : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (le_abs_self w.im)
      have hb : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr (neg_le_abs w.im)
      linarith
    have h2 : Real.exp |w.im| ≤ Real.exp ‖w‖ := Real.exp_le_exp.mpr (Complex.abs_im_le_norm w)
    linarith
  exact le_trans hle2 hle3

lemma abs_sinh_im_le_norm_cos (w : ℂ) : |Real.sinh w.im| ≤ ‖Complex.cos w‖ := by
  have hsq := cos_sq_norm w
  have hcosh : (Real.cosh w.im) ^ 2 = (Real.sinh w.im) ^ 2 + 1 := Real.cosh_sq _
  have key : (Real.sinh w.im) ^ 2 ≤ ‖Complex.cos w‖ ^ 2 := by
    rw [hsq]
    nlinarith [Real.sin_sq_add_cos_sq w.re, hcosh, sq_nonneg (Real.sinh w.im),
      sq_nonneg (Real.cos w.re)]
  have h := sq_le_sq.mp key
  rwa [abs_of_nonneg (norm_nonneg _)] at h

lemma exp_abs_le_of_abs_sinh_le {t A : ℝ} (h : |Real.sinh t| ≤ A) :
    Real.exp |t| ≤ 2 * A + 1 := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) h
  have hs : (Real.sinh t) ^ 2 ≤ A ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (Real.sinh t)) h 2
    rwa [sq_abs] at hh
  have h1 : Real.cosh t ≤ Real.sqrt (A ^ 2 + 1) := by
    rw [Real.le_sqrt (Real.cosh_pos t).le (by positivity), Real.cosh_sq]
    linarith
  have h2 : Real.sqrt (A ^ 2 + 1) ≤ A + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (A + 1)]
  have h3 : Real.exp |t| = Real.cosh t + |Real.sinh t| := by
    have hh := Real.cosh_add_sinh |t|
    rw [Real.cosh_abs, ← Real.abs_sinh] at hh
    exact hh.symm
  linarith [h1, h2, h3, h]

lemma exists_int_add_two_pi_mem_Ioc (t : ℝ) :
    ∃ k : ℤ, t + (k : ℝ) * (2 * Real.pi) ∈ Set.Ioc (-Real.pi) Real.pi := by
  refine ⟨⌊(Real.pi - t) / (2 * Real.pi)⌋, ?_⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : ((⌊(Real.pi - t) / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ (Real.pi - t) / (2 * Real.pi) :=
    Int.floor_le _
  have h2 : (Real.pi - t) / (2 * Real.pi)
      < ((⌊(Real.pi - t) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hk1 : (⌊(Real.pi - t) / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) ≤ Real.pi - t := by
    have := mul_le_mul_of_nonneg_right h1 (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  have hk2 : Real.pi - t < ((⌊(Real.pi - t) / (2 * Real.pi)⌋ : ℝ) + 1) * (2 * Real.pi) := by
    have := mul_lt_mul_of_pos_right h2 hpi
    rwa [div_mul_cancel₀ _ (ne_of_gt hpi)] at this
  constructor
  · nlinarith [hk2]
  · nlinarith [hk1]

lemma re_int_mul_two_pi_I (k : ℤ) :
    ((k : ℂ) * (2 * ↑Real.pi * Complex.I)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im]

lemma im_int_mul_two_pi_I (k : ℤ) :
    ((k : ℂ) * (2 * ↑Real.pi * Complex.I)).im = (k : ℝ) * (2 * Real.pi) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.intCast_re, Complex.intCast_im]

lemma re_int_mul_two_pi (k : ℤ) : ((k : ℂ) * (2 * ↑Real.pi)).re = (k : ℝ) * (2 * Real.pi) := by
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im]

lemma re_two_pi_mul_I (w : ℂ) :
    ((2 * Real.pi * Complex.I) * w).re = -(2 * Real.pi * w.im) := by
  rw [Complex.mul_re]
  have h1 : ((2 * Real.pi * Complex.I : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h2 : ((2 * Real.pi * Complex.I : ℂ)).im = 2 * Real.pi := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  rw [h1, h2]; ring

/-! ### Bloch's theorem on a disk -/

theorem bloch_disk {z₀ : ℂ} {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball z₀ s)) (hd : deriv f z₀ ≠ 0) :
    ∃ c : ℂ, Metric.ball c ((1 / 128 : ℝ) * s * ‖deriv f z₀‖) ⊆ f '' Metric.ball z₀ s := by
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  set d : ℂ := deriv f z₀ with hddef
  have hdne : d ≠ 0 := hd
  have hsd : s * d ≠ 0 := mul_ne_zero hsne hdne
  set F : ℂ → ℂ := fun u => (f (z₀ + s * u) - f z₀) / (s * d) with hFdef
  have hmap : MapsTo (fun u : ℂ => z₀ + s * u) (Metric.ball 0 1) (Metric.ball z₀ s) := by
    intro u hu
    rw [mem_ball_zero_iff'] at hu
    rw [Metric.mem_ball]
    have hz : z₀ + s * u - z₀ = s * u := by ring
    rw [dist_eq_norm, hz, norm_mul, cnorm_ofReal, abs_of_pos hs]
    nlinarith [norm_nonneg u]
  have hFdiff : DifferentiableOn ℂ F (Metric.ball 0 1) := by
    rw [hFdef]
    exact (((hf.comp (by fun_prop) hmap)).sub_const (f z₀)).div_const (s * d)
  have hF0 : F 0 = 0 := by rw [hFdef]; simp
  have hcomp : HasDerivAt (fun u : ℂ => f (z₀ + s * u)) (deriv f z₀ * s) 0 := by
    have h1 : HasDerivAt (fun u : ℂ => z₀ + s * u) (s : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (s : ℂ)).const_add z₀
    have hmem0 : z₀ + s * 0 ∈ Metric.ball z₀ s := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hz : z₀ + s * 0 - z₀ = s * 0 := by ring
      rw [hz, norm_mul, cnorm_ofReal, abs_of_pos hs, norm_zero, mul_zero]
      exact hs
    have h2 : HasDerivAt f (deriv f z₀) (z₀ + s * 0) := by
      have := (hf.differentiableAt (Metric.isOpen_ball.mem_nhds hmem0)).hasDerivAt
      simpa using this
    have h3 := h2.comp 0 h1
    simpa [Function.comp_def] using h3
  have hFderiv : deriv F 0 = 1 := by
    have hsub : HasDerivAt (fun u : ℂ => f (z₀ + s * u) - f z₀) (deriv f z₀ * s) 0 :=
      hcomp.sub_const (f z₀)
    have hdiv : HasDerivAt F ((deriv f z₀ * s) / (s * d)) 0 := by
      rw [hFdef]
      exact hsub.div_const (s * d)
    have hval : (deriv f z₀ * (s : ℂ)) / ((s : ℂ) * d) = 1 := by
      rw [hddef, mul_comm (s : ℂ) (deriv f z₀)]
      exact div_self (mul_ne_zero hd hsne)
    rw [hdiv.deriv]
    exact hval
  obtain ⟨c, hc⟩ := bloch_unit hFdiff hF0 hFderiv
  refine ⟨f z₀ + (s * d) * c, ?_⟩
  intro v hv
  rw [Metric.mem_ball, dist_eq_norm] at hv
  set v' : ℂ := c + (v - (f z₀ + (s * d) * c)) / (s * d) with hv'def
  have hv' : v' ∈ Metric.ball c (1 / 128 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hvc : v' - c = (v - (f z₀ + (s * d) * c)) / (s * d) := by rw [hv'def]; ring
    rw [hvc, norm_div, norm_mul, cnorm_ofReal, abs_of_pos hs]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hv, norm_nonneg (v - (f z₀ + (s * d) * c))]
  obtain ⟨u, hu, huF⟩ := hc hv'
  refine ⟨z₀ + s * u, hmap hu, ?_⟩
  have key : (f (z₀ + s * u) - f z₀) / (s * d) = v' := by
    simpa only [hFdef] using huF
  rw [div_eq_iff hsd] at key
  have hvval : v = f z₀ + v' * (s * d) := by
    rw [hv'def]
    field_simp
    ring
  rw [hvval]
  linear_combination key

/-! ### The main boundedness statement -/

theorem schottky_bound {a b r : ℝ} (ha : 0 < a) (hr : r < 1) :
    ∃ B : ℝ, ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
      (∀ z ∈ Metric.ball 0 1, f z ≠ 0 ∧ f z ≠ 1) →
      a ≤ ‖f 0‖ → ‖f 0‖ ≤ b →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ B := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · refine ⟨0, fun f hf hne haf hbf z hz => ?_⟩
    have : (0 : ℝ) ≤ r := le_trans (norm_nonneg z) hz
    linarith
  set Mx : ℝ := max (|Real.log a|) (|Real.log b|) with hMxdef
  set A : ℝ := (Mx + Real.pi) / (2 * Real.pi) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set Ah : ℝ := Real.pi + Real.log (2 * A + 1) with hAhdef
  set R : ℝ := (1 + r) / 2 with hRdef
  have hR1 : R < 1 := by rw [hRdef]; linarith
  have hRr : r < R := by rw [hRdef]; linarith
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have h1R : 0 < 1 - R := by rw [hRdef]; linarith
  set C : ℝ := 1024 / (1 - R) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨Real.exp (2 * Real.pi * Real.exp (Ah + C * r)), ?_⟩
  intro f hf hne haf hbf z hz
  have hzR : ‖z‖ < R := lt_of_le_of_lt hz hRr
  have hz1 : z ∈ Metric.ball 0 1 := by
    rw [mem_ball_zero_iff']; linarith [hzR, hR1]
  -- the holomorphic logarithm
  obtain ⟨L, hLdiff, hLexp, hLre⟩ :=
    Work.Escape.exists_differentiableOn_ball_clog (c := 0) (r := 1) hf
      (fun w hw => (hne w hw).1)
  -- shift so that the imaginary part at `0` lies in `(-π, π]`
  obtain ⟨k, hk⟩ := exists_int_add_two_pi_mem_Ioc (L 0).im
  set L' : ℂ → ℂ := fun w => L w + (k : ℂ) * (2 * Real.pi * Complex.I) with hL'def
  have hL'diff : DifferentiableOn ℂ L' (Metric.ball 0 1) := hLdiff.add_const _
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexpk : Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    have hcast : (k : ℂ) * (2 * Real.pi * Complex.I) = (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast; ring
    rw [hcast]; exact Complex.exp_int_mul_two_pi_mul_I k
  have hL'exp : ∀ w ∈ Metric.ball 0 1, Complex.exp (L' w) = f w := by
    intro w hw
    rw [hL'def, Complex.exp_add, hLexp w hw, hexpk, mul_one]
  have hL're : ∀ w ∈ Metric.ball 0 1, (L' w).re = Real.log ‖f w‖ := by
    intro w hw
    rw [hL'def, Complex.add_re, re_int_mul_two_pi_I, add_zero]
    exact hLre w hw
  have hL'0im : (L' 0).im ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hL'def, Complex.add_im, im_int_mul_two_pi_I]
    exact hk
  -- the function `g = L' / (2πi)`, which omits `ℤ`
  set g : ℂ → ℂ := fun w => L' w / (2 * Real.pi * Complex.I) with hgdef
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 1) := hL'diff.div_const _
  have hf_exp_g : ∀ w ∈ Metric.ball 0 1, Complex.exp (2 * Real.pi * Complex.I * g w) = f w := by
    intro w hw
    have hmul : (2 * Real.pi * Complex.I) * g w = L' w := by
      rw [hgdef]; field_simp
    rw [hmul, hL'exp w hw]
  have hg_ne_int : ∀ w ∈ Metric.ball 0 1, ∀ n : ℤ, g w ≠ (n : ℂ) := by
    intro w hw n hn
    have h1 : Complex.exp (2 * Real.pi * Complex.I * g w) = 1 := by
      rw [hn]
      have hcast : (2 * Real.pi * Complex.I) * (n : ℂ) = (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        push_cast; ring
      rw [hcast]; exact Complex.exp_int_mul_two_pi_mul_I n
    rw [hf_exp_g w hw] at h1
    exact (hne w hw).2 h1
  -- lift through `cos`
  obtain ⟨h, hhdiff, hhcos⟩ := exists_differentiableOn_cos_eq hgdiff
    (fun w hw => ⟨fun hh => hg_ne_int w hw 1 (by simpa using hh),
      fun hh => hg_ne_int w hw (-1) (by simpa using hh)⟩)
  obtain ⟨k', hk'⟩ := exists_int_add_two_pi_mem_Ioc (h 0).re
  set h' : ℂ → ℂ := fun w => h w + (k' : ℂ) * (2 * ↑Real.pi) with hh'def
  have hh'diff : DifferentiableOn ℂ h' (Metric.ball 0 1) := hhdiff.add_const _
  have hh'cos : ∀ w ∈ Metric.ball 0 1, Complex.cos (h' w) = g w := by
    intro w hw
    have hcast : h' w = h w + (k' : ℂ) * (2 * ↑Real.pi) := by simp only [hh'def]
    rw [hcast, Complex.cos_add_int_mul_two_pi]
    exact hhcos w hw
  have hh'0re : |(h' 0).re| ≤ Real.pi := by
    have hre : (h' 0).re = (h 0).re + (k' : ℝ) * (2 * Real.pi) := by
      rw [show h' 0 = h 0 + (k' : ℂ) * (2 * ↑Real.pi) from by simp only [hh'def],
        Complex.add_re, re_int_mul_two_pi]
    rw [hre]
    rw [Set.mem_Ioc] at hk'
    rw [abs_le]; constructor <;> linarith [hk'.1, hk'.2]
  -- bounds on `h' 0`
  have hL'0norm : ‖L' 0‖ ≤ Mx + Real.pi := by
    have hre : (L' 0).re = Real.log ‖f 0‖ := hL're 0 (Metric.mem_ball_self one_pos)
    have him : |(L' 0).im| ≤ Real.pi := by
      rw [Set.mem_Ioc] at hL'0im
      rw [abs_le]; constructor <;> linarith [hL'0im.1, hL'0im.2]
    have hlog : |Real.log ‖f 0‖| ≤ Mx := by
      have h0pos : 0 < ‖f 0‖ := lt_of_lt_of_le ha haf
      have h1 : Real.log a ≤ Real.log ‖f 0‖ := Real.log_le_log ha haf
      have hbpos : 0 < b := lt_of_lt_of_le h0pos hbf
      have h2 : Real.log ‖f 0‖ ≤ Real.log b := Real.log_le_log h0pos hbf
      have hMx1 : -Mx ≤ Real.log a := by
        rw [hMxdef]
        linarith [neg_abs_le (Real.log a), le_max_left (|Real.log a|) (|Real.log b|)]
      have hMx2 : Real.log b ≤ Mx := by
        rw [hMxdef]
        linarith [le_abs_self (Real.log b), le_max_right (|Real.log a|) (|Real.log b|)]
      rw [abs_le]; constructor <;> linarith
    calc ‖L' 0‖ ≤ |(L' 0).re| + |(L' 0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖f 0‖| + |(L' 0).im| := by rw [hre]
      _ ≤ Mx + Real.pi := add_le_add hlog him
  have hg0 : ‖g 0‖ ≤ A := by
    rw [hgdef, norm_div, hAdef]
    have hden : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      have hcast : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hcast, norm_mul, Complex.norm_I, mul_one, cnorm_ofReal, abs_of_pos (by positivity)]
    rw [hden]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hL'0norm, Real.pi_pos]
  have hImh0 : |(h' 0).im| ≤ Real.log (2 * A + 1) := by
    have hsinh : |Real.sinh (h' 0).im| ≤ A := by
      refine le_trans (abs_sinh_im_le_norm_cos (h' 0)) ?_
      rw [show Complex.cos (h' 0) = g 0 from hh'cos 0 (Metric.mem_ball_self one_pos)]
      exact hg0
    have hexp := exp_abs_le_of_abs_sinh_le hsinh
    have := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  have hh'0norm : ‖h' 0‖ ≤ Ah := by
    calc ‖h' 0‖ ≤ |(h' 0).re| + |(h' 0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Real.pi + Real.log (2 * A + 1) := add_le_add hh'0re hImh0
      _ = Ah := by rw [hAhdef]
  -- derivative bound on `ball 0 R`
  have hbound : ∀ w ∈ Metric.ball 0 R, ‖deriv h' w‖ ≤ C := by
    intro w hw
    rw [mem_ball_zero_iff'] at hw
    by_cases hdw : deriv h' w = 0
    · rw [hdw, norm_zero]; exact hC0
    · set s : ℝ := (1 - ‖w‖) / 2 with hsdef
      have hs : 0 < s := by rw [hsdef]; linarith [norm_nonneg w]
      have hs1 : s ≤ 1 := by rw [hsdef]; linarith [norm_nonneg w]
      have hsub : Metric.ball w s ⊆ Metric.ball (0 : ℂ) 1 := by
        intro u hu
        rw [Metric.mem_ball, dist_eq_norm] at hu
        rw [mem_ball_zero_iff']
        calc ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by
              have : u = w + (u - w) := by ring
              calc ‖u‖ = ‖w + (u - w)‖ := by rw [← this]
                _ ≤ ‖w‖ + ‖u - w‖ := norm_add_le _ _
                _ = ‖u - w‖ + ‖w‖ := by ring
          _ < s + ‖w‖ := by linarith
          _ = (1 + ‖w‖) / 2 := by rw [hsdef]; ring
          _ < 1 := by linarith
      obtain ⟨c, hc⟩ := bloch_disk (f := h') hs hs1 (hh'diff.mono hsub) hdw
      by_contra hcon
      rw [not_le] at hcon
      have hbig : 4 < (1 / 128 : ℝ) * s * ‖deriv h' w‖ := by
        have hsR : (1 - R) / 2 < s := by rw [hsdef]; linarith
        have hCeq : (1 / 128 : ℝ) * ((1 - R) / 2) * (1024 / (1 - R)) = 4 := by
          field_simp; ring
        have hstep : (1 / 128 : ℝ) * ((1 - R) / 2) * (1024 / (1 - R))
            < (1 / 128 : ℝ) * s * ‖deriv h' w‖ := by
          have ha' : (1 / 128 : ℝ) * ((1 - R) / 2) < (1 / 128 : ℝ) * s :=
            mul_lt_mul_of_pos_left hsR (by norm_num)
          rw [hCdef] at hcon
          have hb' : (1024 / (1 - R)) < ‖deriv h' w‖ := hcon
          calc (1 / 128 : ℝ) * ((1 - R) / 2) * (1024 / (1 - R))
              < ((1 / 128 : ℝ) * s) * (1024 / (1 - R)) :=
                mul_lt_mul_of_pos_right ha' (by positivity)
            _ < ((1 / 128 : ℝ) * s) * ‖deriv h' w‖ :=
                mul_lt_mul_of_pos_left hb' (by positivity)
            _ = (1 / 128 : ℝ) * s * ‖deriv h' w‖ := by ring
        linarith [hCeq, hstep]
      obtain ⟨u, hu, n, hn⟩ := exists_cos_eq_int_of_ball c hbig
      obtain ⟨v, hv, hvu⟩ := hc hu
      have hcv : Complex.cos (h' v) = (n : ℂ) := by rw [hvu]; exact hn
      rw [hh'cos v (hsub hv)] at hcv
      exact hg_ne_int v (hsub hv) n hcv
  -- mean value estimate
  have hmean : ∀ w ∈ Metric.ball 0 R, ‖h' w - h' 0‖ ≤ C * ‖w‖ := by
    intro w hw
    have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
      intro u hu
      rw [mem_ball_zero_iff'] at hu ⊢
      linarith
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u hu => ((hh'diff.mono hsub) u hu).differentiableAt
        (Metric.isOpen_ball.mem_nhds hu))
      (fun u hu => hbound u hu) (convex_ball (0 : ℂ) R)
      (Metric.mem_ball_self (x := (0 : ℂ)) hRpos) hw
    simpa using hmain
  have hhz : ‖h' z‖ ≤ Ah + C * r := by
    have h1 := hmean z (by rw [mem_ball_zero_iff']; exact hzR)
    have h2 : ‖h' z‖ ≤ ‖h' 0‖ + ‖h' z - h' 0‖ := by
      have hz' : h' z = h' 0 + (h' z - h' 0) := by ring
      calc ‖h' z‖ = ‖h' 0 + (h' z - h' 0)‖ := congrArg (fun a : ℂ => ‖a‖) hz'
        _ ≤ ‖h' 0‖ + ‖h' z - h' 0‖ := norm_add_le _ _
    have h3 : ‖h' z - h' 0‖ ≤ C * r := le_trans h1 (mul_le_mul_of_nonneg_left hz hC0)
    linarith [hh'0norm]
  calc ‖f z‖ = ‖Complex.exp (2 * Real.pi * Complex.I * g z)‖ := by rw [hf_exp_g z hz1]
    _ = Real.exp ((2 * Real.pi * Complex.I * g z).re) := Complex.norm_exp _
    _ = Real.exp (-2 * Real.pi * (Complex.cos (h' z)).im) := by
        rw [← hh'cos z hz1, re_two_pi_mul_I]
        congr 1
        ring
    _ ≤ Real.exp (2 * Real.pi * ‖Complex.cos (h' z)‖) := by
        apply Real.exp_le_exp.mpr
        have := Complex.abs_im_le_norm (Complex.cos (h' z))
        have hneg : -(Complex.cos (h' z)).im ≤ ‖Complex.cos (h' z)‖ := by
          linarith [neg_abs_le (Complex.cos (h' z)).im]
        nlinarith [Real.pi_pos, hneg]
    _ ≤ Real.exp (2 * Real.pi * Real.exp ‖h' z‖) := by
        apply Real.exp_le_exp.mpr
        have := norm_cos_le_exp (h' z)
        nlinarith [Real.pi_pos, norm_nonneg (Complex.cos (h' z))]
    _ ≤ Real.exp (2 * Real.pi * Real.exp (Ah + C * r)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr hhz

theorem schottky_two_omitted {r M : ℝ} (hr : r < 1) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
      (∀ z ∈ Metric.ball 0 1, f z ≠ 0 ∧ f z ≠ 1) → ‖f 0‖ ≤ M →
      ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ B := by
  set r' : ℝ := (1 + r) / 2 with hr'def
  have hr'1 : r' < 1 := by rw [hr'def]; linarith
  have hrr' : r < r' := by rw [hr'def]; linarith
  obtain ⟨B₁, hB₁⟩ := schottky_bound (a := 1 / 2) (b := max M 1) (r := r') (by norm_num) hr'1
  obtain ⟨B₂, hB₂⟩ := schottky_bound (a := 1 / 2) (b := 1 + max M 1) (r := r') (by norm_num) hr'1
  refine ⟨max 0 (max B₁ (1 + B₂)), le_max_left _ _, ?_⟩
  intro f hf hne hf0 z hz
  have hz' : ‖z‖ ≤ r' := le_trans hz hrr'.le
  rcases lt_or_ge ‖f 0‖ (1 / 2 : ℝ) with hc | hc
  · have hFne : ∀ w ∈ Metric.ball 0 1, (1 - f w) ≠ 0 ∧ (1 - f w) ≠ 1 := by
      intro w hw
      exact ⟨sub_ne_zero.mpr (Ne.symm (hne w hw).2), fun h => (hne w hw).1 (by linear_combination -h)⟩
    have hFdiff : DifferentiableOn ℂ (fun w => 1 - f w) (Metric.ball 0 1) :=
      (differentiableOn_const (1 : ℂ)).sub hf
    have hF0a : 1 / 2 ≤ ‖1 - f 0‖ := by
      have h1 : |(1 : ℝ) - ‖f 0‖| ≤ ‖(1 : ℂ) - f 0‖ := by
        simpa using abs_norm_sub_norm_le (1 : ℂ) (f 0)
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    have hF0b : ‖1 - f 0‖ ≤ 1 + max M 1 := by
      have h1 : ‖(1 : ℂ) - f 0‖ ≤ 1 + ‖f 0‖ := by
        simpa [norm_one] using norm_sub_le (1 : ℂ) (f 0)
      have h2 : ‖f 0‖ ≤ max M 1 := le_trans hf0 (le_max_left M 1)
      linarith
    have h2 := hB₂ (fun w => 1 - f w) hFdiff hFne hF0a hF0b z hz'
    have h3 : ‖f z‖ ≤ 1 + ‖1 - f z‖ := by
      have h1 : ‖(1 : ℂ) - (1 - f z)‖ ≤ 1 + ‖1 - f z‖ := by
        simpa [norm_one] using norm_sub_le (1 : ℂ) (1 - f z)
      simpa using h1
    have h4 : 1 + B₂ ≤ max 0 (max B₁ (1 + B₂)) :=
      le_trans (le_max_right B₁ (1 + B₂)) (le_max_right (0 : ℝ) (max B₁ (1 + B₂)))
    linarith [h2, h3, h4]
  · have h1 := hB₁ f hf hne hc (le_trans hf0 (le_max_left M 1)) z hz'
    exact le_trans h1 (le_trans (le_max_left B₁ (1 + B₂))
      (le_max_right (0 : ℝ) (max B₁ (1 + B₂))))

end
end Work.Normal
