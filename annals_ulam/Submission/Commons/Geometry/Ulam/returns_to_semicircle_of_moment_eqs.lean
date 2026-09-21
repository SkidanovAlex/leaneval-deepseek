import Mathlib
import Submission.Commons.Geometry.Ulam.even_profile_moment_solution
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric

namespace Commons.Geometry.Ulam

open MeasureTheory Filter
open scoped Interval ContDiff Topology

set_option autoImplicit false

noncomputable section



abbrev momE (n : ℕ) (f h x y : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun s => ∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - k) * t ^ (2 * k)

abbrev momO (n : ℕ) (f h x y : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  fun s => ∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1 - k) * t ^ (2 * k + 1)

abbrev refE (n : ℕ) (k : ℕ) : ℝ → ℝ :=
  fun s => ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
    ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - k) * t ^ (2 * k)

lemma hasDerivAt_momentIntegrand {f h : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (m j : ℕ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
        (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j) u := by
  have h1 : HasDerivAt (fun v : ℝ => v * t) (t) u := by
    simpa using (hasDerivAt_id u).mul_const t
  have h2 : HasDerivAt h (deriv h u) u := (hh.differentiable (by simp) u).hasDerivAt
  have hlin : HasDerivAt (fun v : ℝ => v * t + h v) (t + deriv h u) u := h1.add h2
  have hsq : HasDerivAt (fun v : ℝ => (v * t + h v) ^ 2)
      (2 * (u * t + h u) * (t + deriv h u)) u := by
    have h3 := hlin.pow 2
    rw [show (↑(2:ℕ):ℝ) * (u * t + h u) ^ (2 - 1) * (t + deriv h u)
          = 2 * (u * t + h u) * (t + deriv h u) by norm_num] at h3
    exact h3
  have hg : HasDerivAt (fun v : ℝ => f t ^ 2 - (v * t + h v) ^ 2)
      (-(2 * (u * t + h u) * (t + deriv h u))) u := by
    have hc : HasDerivAt (fun _ : ℝ => f t ^ 2) 0 u := hasDerivAt_const u (f t ^ 2)
    have h3 := hc.sub hsq
    rw [show 0 - 2 * (u * t + h u) * (t + deriv h u)
          = -(2 * (u * t + h u) * (t + deriv h u)) by ring] at h3
    exact h3
  have hgp : HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m)
      ((m : ℝ) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) *
        (-(2 * (u * t + h u) * (t + deriv h u)))) u := hg.pow m
  have h4 := hgp.mul_const (t ^ j)
  rw [show (m : ℝ) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) *
        (-(2 * (u * t + h u) * (t + deriv h u))) * t ^ j
        = -(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
          (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j by ring] at h4
  exact h4

lemma momE_hasDerivAt {f h x y : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (m j : ℕ) (hm : 1 ≤ m) (s : ℝ)
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot_y : f (y s) ^ 2 = (s * y s + h s) ^ 2)
    (hroot_x : f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (fun u : ℝ => ∫ t in (-x u)..(y u), (f t ^ 2 - (u * t + h u) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * s * ∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (m - 1) * t ^ (j + 2)) s := by
  have hx_at : HasDerivAt x (deriv x s) s := (hx.differentiable (by simp) s).hasDerivAt
  have hy_at : HasDerivAt y (deriv y s) s := (hy.differentiable (by simp) s).hasDerivAt
  have hx_cont : ContinuousAt x s := hx.continuous.continuousAt
  have hy_cont : ContinuousAt y s := hy.continuous.continuousAt
  have hF_cont : Continuous (fun p : ℝ × ℝ => (f p.2 ^ 2 - (p.1 * p.2 + h p.1) ^ 2) ^ m * p.2 ^ j) := by
    fun_prop
  have hF'_cont : Continuous (fun p : ℝ × ℝ => -(2 * (m : ℝ)) * (p.1 * p.2 + h p.1) * (p.2 + deriv h p.1) *
        (f p.2 ^ 2 - (p.1 * p.2 + h p.1) ^ 2) ^ (m - 1) * p.2 ^ j) := by
    have hdh : Continuous (deriv h) := hh.continuous_deriv (by norm_num)
    fun_prop
  have hisDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => (f t ^ 2 - (v * t + h v) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) * (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j) u :=
    fun u t => hasDerivAt_momentIntegrand hf hh m j u t
  have key := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := fun u t => (f t ^ 2 - (u * t + h u) ^ 2) ^ m * t ^ j)
    (F' := fun u t => -(2 * (m : ℝ)) * (u * t + h u) * (t + deriv h u) *
        (f t ^ 2 - (u * t + h u) ^ 2) ^ (m - 1) * t ^ j)
    (x := x) (y := y) hF_cont hF'_cont hisDeriv hx_at hy_at hx_cont hy_cont
  have hby : (f (y s) ^ 2 - (s * y s + h s) ^ 2) ^ m * (y s) ^ j = 0 := by
    rw [hroot_y, sub_self, zero_pow (by omega), zero_mul]
  have hbx : (f (-x s) ^ 2 - (s * (-x s) + h s) ^ 2) ^ m * (-x s) ^ j = 0 := by
    rw [hroot_x, sub_self, zero_pow (by omega), zero_mul]
  refine key.congr_deriv ?_
  rw [hby, hbx]
  simp only [zero_mul, sub_zero, zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  rw [hhs, hdhs]
  rw [pow_add]
  ring

lemma ray_boundary (s : ℝ) :
    1 - (1 / Real.sqrt (1 + s^2))^2 - (s * (1 / Real.sqrt (1 + s^2)))^2 = 0 := by
  have hpos : (0:ℝ) < 1 + s^2 := by positivity
  have hsq : (Real.sqrt (1 + s^2))^2 = 1 + s^2 := Real.sq_sqrt (le_of_lt hpos)
  have hne : Real.sqrt (1 + s^2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp
  nlinarith [hsq]

lemma contDiff_ray : ContDiff ℝ ∞ (fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2)) := by
  apply ContDiff.div
  · fun_prop
  · apply ContDiff.sqrt
    · fun_prop
    · intro x; positivity
  · intro x; positivity

lemma hasDerivAt_rayIntegrand (m j : ℕ) (u t : ℝ) :
    HasDerivAt (fun v : ℝ => ((1 - t^2) - (v*t)^2)^m * t^j)
      (-(2*(m:ℝ)) * u * ((1 - t^2) - (u*t)^2)^(m-1) * t^(j+2)) u := by
  have hlin : HasDerivAt (fun v : ℝ => v*t) (t) u := by simpa using (hasDerivAt_id u).mul_const t
  have hsq : HasDerivAt (fun v : ℝ => (v*t)^2) (2*(u*t)*t) u := by
    have h3 := hlin.pow 2
    rw [show (↑(2:ℕ):ℝ) * (u*t)^(2-1) * t = 2 * (u*t) * t by norm_num] at h3
    exact h3
  have hg : HasDerivAt (fun v : ℝ => (1 - t^2) - (v*t)^2) (-(2*(u*t)*t)) u := by
    have hc : HasDerivAt (fun _ : ℝ => 1 - t^2) 0 u := hasDerivAt_const u _
    have h3 := hc.sub hsq
    rw [show 0 - 2*(u*t)*t = -(2*(u*t)*t) by ring] at h3
    exact h3
  have hgp := hg.pow m
  have h4 := hgp.mul_const (t^j)
  rw [show (m:ℝ) * ((1 - t^2) - (u*t)^2)^(m-1) * (-(2*(u*t)*t)) * t^j
        = -(2*(m:ℝ)) * u * ((1-t^2)-(u*t)^2)^(m-1) * t^(j+2) by
      rw [pow_add]; ring] at h4
  exact h4

lemma refE_hasDerivAt (m j : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ t in (-(1 / Real.sqrt (1 + u ^ 2)))..(1 / Real.sqrt (1 + u ^ 2)),
        ((1 - t ^ 2) - (u * t) ^ 2) ^ m * t ^ j)
      (-(2 * (m : ℝ)) * s * ∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        ((1 - t ^ 2) - (s * t) ^ 2) ^ (m - 1) * t ^ (j + 2)) s := by
  have ha_smooth : ContDiff ℝ ∞ (fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2)) := contDiff_ray
  have ha_at : HasDerivAt (fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2))
      (deriv (fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2)) s) s :=
    (ha_smooth.differentiable (by simp) s).hasDerivAt
  have ha_cont : ContinuousAt (fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2)) s :=
    ha_smooth.continuous.continuousAt
  have hF_cont : Continuous (fun p : ℝ×ℝ => ((1 - p.2^2) - (p.1*p.2)^2)^m * p.2^j) := by fun_prop
  have hF'_cont : Continuous (fun p : ℝ×ℝ =>
      -(2*(m:ℝ)) * p.1 * ((1 - p.2^2) - (p.1*p.2)^2)^(m-1) * p.2^(j+2)) := by fun_prop
  have hisDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => ((1 - t^2) - (v*t)^2)^m * t^j)
      (-(2*(m:ℝ)) * u * ((1 - t^2) - (u*t)^2)^(m-1) * t^(j+2)) u :=
    fun u t => hasDerivAt_rayIntegrand m j u t
  have key := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuous_parametric
    (F := fun u t => ((1 - t^2) - (u*t)^2)^m * t^j)
    (F' := fun u t => -(2*(m:ℝ)) * u * ((1 - t^2) - (u*t)^2)^(m-1) * t^(j+2))
    (x := fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2))
    (y := fun u : ℝ => 1 / Real.sqrt (1 + u ^ 2))
    hF_cont hF'_cont hisDeriv ha_at ha_at ha_cont ha_cont
  have hby : ((1 - (1 / Real.sqrt (1 + s ^ 2))^2) - (s * (1 / Real.sqrt (1 + s ^ 2)))^2)^m
      * (1 / Real.sqrt (1 + s ^ 2))^j = 0 := by
    rw [ray_boundary s, zero_pow (by omega), zero_mul]
  have hbx : (1 - (-(1 / Real.sqrt (1 + s ^ 2)))^2 - (s * (-(1 / Real.sqrt (1 + s ^ 2))))^2)^m
      * (-(1 / Real.sqrt (1 + s ^ 2)))^j = 0 := by
    have h1 : (-(1 / Real.sqrt (1 + s ^ 2)))^2 = (1 / Real.sqrt (1 + s ^ 2))^2 := by ring
    have h2 : (s * -(1 / Real.sqrt (1 + s ^ 2)))^2 = (s * (1 / Real.sqrt (1 + s ^ 2)))^2 := by ring
    have hbase : 1 - (-(1 / Real.sqrt (1 + s ^ 2)))^2 - (s * (-(1 / Real.sqrt (1 + s ^ 2))))^2 = 0 := by
      rw [h1, h2, ray_boundary s]
    rw [hbase, zero_pow (by omega), zero_mul]
  refine key.congr_deriv ?_
  rw [hby, hbx]
  simp only [zero_mul, sub_zero, zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only []
  ring

lemma momE_deriv_step {f h x y : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) {n k : ℕ} (hk : k + 1 ≤ n) {s : ℝ}
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot : f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (momE n f h x y k) (-(2 * ((n - k : ℕ) : ℝ)) * s * momE n f h x y (k + 1) s) s := by
  have hm : 1 ≤ n - k := by omega
  have hstep := momE_hasDerivAt hf hh hx hy (n - k) (2 * k) hm s hhs hdhs hroot.1 hroot.2
  have hInt : (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (n - k - 1) * t ^ (2 * k + 2))
      = momE n f h x y (k + 1) s := by
    simp only [momE]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hhs]
    simp only [add_zero]
    have h1 : n - (k + 1) = n - k - 1 := by omega
    rw [h1]
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2]
  rw [hInt] at hstep
  exact hstep

lemma momO_deriv_step {f h x y : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) {n k : ℕ} (hk : k + 2 ≤ n) {s : ℝ}
    (hhs : h s = 0) (hdhs : deriv h s = 0)
    (hroot : f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2) :
    HasDerivAt (momO n f h x y k) (-(2 * ((n - 1 - k : ℕ) : ℝ)) * s * momO n f h x y (k + 1) s) s := by
  have hm : 1 ≤ n - 1 - k := by omega
  have hstep := momE_hasDerivAt hf hh hx hy (n - 1 - k) (2 * k + 1) hm s hhs hdhs hroot.1 hroot.2
  have hInt : (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t) ^ 2) ^ (n - 1 - k - 1) * t ^ (2 * k + 1 + 2))
      = momO n f h x y (k + 1) s := by
    simp only [momO]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    rw [hhs]
    simp only [add_zero]
    have h1 : n - 1 - (k + 1) = n - 1 - k - 1 := by omega
    rw [h1]
    have h2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [h2]
  rw [hInt] at hstep
  exact hstep

lemma refE_deriv_step {n k : ℕ} (hk : k + 1 ≤ n) (s : ℝ) :
    HasDerivAt (refE n k) (-(2 * ((n - k : ℕ) : ℝ)) * s * refE n (k + 1) s) s := by
  have hm : 1 ≤ n - k := by omega
  have hstep := refE_hasDerivAt (n - k) (2 * k) hm s
  have hInt : (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
        ((1 - t ^ 2) - (s * t) ^ 2) ^ (n - k - 1) * t ^ (2 * k + 2))
      = refE n (k + 1) s := by
    simp only [refE]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    have h1 : n - (k + 1) = n - k - 1 := by omega
    rw [h1]
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [h2]
  rw [hInt] at hstep
  exact hstep

lemma hden_odd (n : ℕ) (hn : 1 ≤ n) : ((2*n-1 : ℕ):ℝ) + 1 = 2*(n:ℝ) := by
  have h2 : (2*n-1 : ℕ) + 1 = 2*n := by omega
  calc ((2*n-1 : ℕ):ℝ) + 1 = ((2*n-1 : ℕ):ℝ) + ((1:ℕ):ℝ) := by norm_num
    _ = ((2*n-1+1 : ℕ):ℝ) := by rw [Nat.cast_add]
    _ = ((2*n : ℕ):ℝ) := by rw [h2]
    _ = 2*(n:ℝ) := by push_cast; ring

lemma integral_pow_even (x y : ℝ) (n : ℕ) :
    (∫ t in (-x)..y, t^(2*n)) = (y^(2*n+1) + x^(2*n+1)) / (2*(n:ℝ) + 1) := by
  rw [integral_pow]
  rw [Odd.neg_pow (show Odd (2*n+1) from ⟨n, by ring⟩)]
  push_cast
  ring

lemma integral_pow_sym (a : ℝ) (n : ℕ) :
    (∫ t in (-a)..a, t^(2*n)) = (2*a^(2*n+1)) / (2*(n:ℝ) + 1) := by
  rw [integral_pow]
  rw [Odd.neg_pow (show Odd (2*n+1) from ⟨n, by ring⟩)]
  push_cast
  ring

lemma integral_pow_odd (x y : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ t in (-x)..y, t^(2*n-1)) = (y^(2*n) - x^(2*n)) / (2*(n:ℝ)) := by
  have h : 2*n-1+1 = 2*n := by omega
  rw [integral_pow, h, Even.neg_pow (show Even (2*n) from ⟨n, by ring⟩), hden_odd n hn]

lemma final_conclusion {x y a : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n)
    (h1 : y^(2*n+1) + x^(2*n+1) = 2*a^(2*n+1)) (h2 : y^(2*n) = x^(2*n)) :
    x = a ∧ y = a := by
  have hmono2 : StrictMonoOn (fun z : ℝ => z^(2*n)) {a | 0 ≤ a} :=
    pow_left_strictMonoOn₀ (M₀ := ℝ) (by omega : 2*n ≠ 0)
  have hxy : x = y := hmono2.injOn (le_of_lt hx) (le_of_lt hy) h2.symm
  have hmono1 : StrictMonoOn (fun z : ℝ => z^(2*n+1)) {a | 0 ≤ a} :=
    pow_left_strictMonoOn₀ (M₀ := ℝ) (by omega : 2*n+1 ≠ 0)
  have hxa : x = a := by
    apply hmono1.injOn (le_of_lt hx) (le_of_lt ha)
    have h := h1
    rw [← hxy] at h
    linarith
  exact ⟨hxa, hxy ▸ hxa⟩

/-- **Step 3 of Ryabogin's even-dimensional construction.**
On an interval `[A,B]` on which the perturbation function `h` vanishes identically (in a whole
neighbourhood), the moment equations force the perturbed intersection functions `x`, `y` back to the
semicircle values `profileX`.  (The equations are assumed on the enlarged interval `[A-ε,B+ε]`
because the proof differentiates them.) -/
theorem returns_to_semicircle_of_moment_eqs
    (n : ℕ) (hn : 2 ≤ n) {x y f h : ℝ → ℝ} {A B ε : ℝ}
    (hε : 0 < ε) (hA : 0 < A) (hAB : A < B)
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h)
    (hh0 : ∀ s ∈ Set.Icc (A - ε) (B + ε), h s = 0)
    (hxpos : ∀ s ∈ Set.Icc (A - ε) (B + ε), 0 < x s)
    (hypos : ∀ s ∈ Set.Icc (A - ε) (B + ε), 0 < y s)
    (hroot : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      f (y s) ^ 2 = (s * y s + h s) ^ 2 ∧ f (-x s) ^ 2 = (s * (-x s) + h s) ^ 2)
    (hF : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ n) =
        (∫ t in (-(1 / Real.sqrt (1 + s ^ 2)))..(1 / Real.sqrt (1 + s ^ 2)),
          ((1 - t ^ 2) - (s * t) ^ 2) ^ n))
    (hH : ∀ s ∈ Set.Icc (A - ε) (B + ε),
      (∫ t in (-x s)..(y s), (f t ^ 2 - (s * t + h s) ^ 2) ^ (n - 1) * (t + deriv h s)) = 0) :
    ∀ s ∈ Set.Icc A B, x s = profileX s ∧ y s = profileX s := by
  let U : Set ℝ := Set.Ioo (A - ε) (B + ε) ∩ Set.Ioi 0
  have hUopen : IsOpen U := isOpen_Ioo.inter isOpen_Ioi
  have hUB : ∀ s ∈ U, s ∈ Set.Icc (A - ε) (B + ε) :=
    fun s hs => Set.Ioo_subset_Icc_self hs.1
  have hdh : ∀ s ∈ U, deriv h s = 0 := by
    intro s hs
    have hmem : U ∈ 𝓝 s := hUopen.mem_nhds hs
    have hev : h =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := by
      filter_upwards [hmem] with u hu
      exact hh0 u (hUB u hu)
    rw [hev.deriv_eq]
    simp
  have hABU : Set.Icc A B ⊆ U := by
    intro s hs
    have h3 : 0 < s := lt_of_lt_of_le hA hs.1
    have h1 : A - ε < s := by linarith [hε, hs.1]
    have h2 : s < B + ε := by linarith [hs.2, hAB, hε]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hbaseE : Set.EqOn (momE n f h x y 0) (refE n 0) U := by
    intro s hs
    have hthis := hF s (hUB s hs)
    simpa [momE, refE] using hthis
  have hbaseO : Set.EqOn (momO n f h x y 0) (fun _ => (0:ℝ)) U := by
    intro s hs
    have hthis := hH s (hUB s hs)
    rw [hdh s hs] at hthis
    simpa [momO] using hthis
  have hE : ∀ k, k ≤ n → Set.EqOn (momE n f h x y k) (refE n k) U := by
    intro k
    induction k with
    | zero => intro _; exact hbaseE
    | succ k ih =>
        intro hk
        have ihk := ih (le_trans (Nat.le_succ k) hk)
        intro s hsU
        have hsI := hUB s hsU
        have hmem : U ∈ 𝓝 s := hUopen.mem_nhds hsU
        have hev : (momE n f h x y k) =ᶠ[𝓝 s] (refE n k) := ihk.eventuallyEq_of_mem hmem
        have hstepE := momE_deriv_step (f := f) (h := h) (x := x) (y := y) (n := n) (k := k)
          hf hh hx hy hk (hh0 s hsI) (hdh s hsU) (hroot s hsI)
        have hstepR := refE_deriv_step (n := n) (k := k) hk s
        have hD := hstepE.unique (hstepR.congr_of_eventuallyEq hev)
        have hsne : s ≠ 0 := ne_of_gt hsU.2
        have hnk : ((n - k : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : n - k ≠ 0)
        have hc : -(2 * ((n - k : ℕ) : ℝ)) * s ≠ 0 := by
          apply mul_ne_zero
          · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnk)
          · exact hsne
        exact mul_left_cancel₀ hc hD
  have hO : ∀ k, k ≤ n - 1 → Set.EqOn (momO n f h x y k) (fun _ => (0:ℝ)) U := by
    intro k
    induction k with
    | zero => intro _; exact hbaseO
    | succ k ih =>
        intro hk
        have ihk := ih (le_trans (Nat.le_succ k) hk)
        intro s hsU
        have hsI := hUB s hsU
        have hmem : U ∈ 𝓝 s := hUopen.mem_nhds hsU
        have hev : (momO n f h x y k) =ᶠ[𝓝 s] (fun _ => (0:ℝ)) := ihk.eventuallyEq_of_mem hmem
        have hstep := momO_deriv_step (f := f) (h := h) (x := x) (y := y) (n := n) (k := k)
          hf hh hx hy (by omega : k + 2 ≤ n) (hh0 s hsI) (hdh s hsU) (hroot s hsI)
        have hstep0 : HasDerivAt (momO n f h x y k) 0 s :=
          (hasDerivAt_const s (0:ℝ)).congr_of_eventuallyEq hev
        have hD := hstep.unique hstep0
        have hsne : s ≠ 0 := ne_of_gt hsU.2
        have hnk : ((n - 1 - k : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (by omega : n - 1 - k ≠ 0)
        have hc : -(2 * ((n - 1 - k : ℕ) : ℝ)) * s ≠ 0 := by
          apply mul_ne_zero
          · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hnk)
          · exact hsne
        exact (mul_eq_zero.mp hD).resolve_left hc
  intro s hsAB
  have hsU := hABU hsAB
  have hsI := hUB s hsU
  have hspos : 0 < s := hsU.2
  have hEn := (hE n le_rfl) hsU
  have hOn := (hO (n - 1) le_rfl) hsU
  have hEn2 : (∫ t in (-x s)..(y s), t^(2*n))
      = (∫ t in (-(1/Real.sqrt (1 + s^2)))..(1/Real.sqrt (1+s^2)), t^(2*n)) := by
    have h := hEn
    simpa only [momE, refE, Nat.sub_self, pow_zero, one_mul] using h
  have hOn2 : (∫ t in (-x s)..(y s), t^(2*n-1)) = 0 := by
    have h := hOn
    simp only [momO, Nat.sub_self, pow_zero, one_mul] at h
    have h2n : 2*(n-1)+1 = 2*n-1 := by omega
    rw [h2n] at h
    exact h
  have h1 : (y s)^(2*n+1) + (x s)^(2*n+1) = 2*(profileX s)^(2*n+1) := by
    have hd : (2*(n:ℝ) + 1) ≠ 0 := by positivity
    have hthis := hEn2
    rw [integral_pow_even (x s) (y s) n, integral_pow_sym (1/Real.sqrt (1+s^2)) n] at hthis
    rw [div_eq_div_iff hd hd] at hthis
    have hcancel := mul_right_cancel₀ hd hthis
    simpa [profileX] using hcancel
  have h2 : (y s)^(2*n) = (x s)^(2*n) := by
    have hd : (2*(n:ℝ)) ≠ 0 := by positivity
    have hz : (y s)^(2*n) - (x s)^(2*n) = 0 := by
      have hthis := hOn2
      rw [integral_pow_odd (x s) (y s) n (by omega)] at hthis
      rcases (div_eq_zero_iff.mp hthis) with h | h
      · exact h
      · exact absurd h hd
    exact sub_eq_zero.mp hz
  exact final_conclusion (hxpos s hsI) (hypos s hsI) (profileX_pos s hspos) (by omega) h1 h2

end
end Commons.Geometry.Ulam
