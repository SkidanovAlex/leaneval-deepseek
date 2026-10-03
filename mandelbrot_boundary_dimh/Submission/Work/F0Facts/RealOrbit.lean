import Mathlib
import Submission.Work.F0Facts.Basic
import Submission.Work.F0Facts.Petal
import Submission.Work.F0Facts.real_orbit_mem_petal

/-!
# Real orbits of `f₀`

For real `t` the orbit of `t` under `f₀(z) = z + z²` is real.  For `t ≥ 0` it is increasing and
blows up unless `t = 0`; hence `0 ∉ Basin` and more generally `(ε : ℂ) ∉ Basin` for `ε > 0`.
For `t ∈ [-1/2, 0)` the orbit increases to `0` and never vanishes, so `(t : ℂ) ∈ Basin`.
-/

namespace Work.F0Facts

open MandelDim Filter Set Metric Topology
open scoped Topology

noncomputable section

/-! ## The orbit of a real point is real -/

lemma orbit_im_eq_zero (t : ℝ) : ∀ n : ℕ, (f0^[n] ((t : ℝ) : ℂ)).im = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have : (f0 (f0^[n] ((t:ℝ):ℂ))).im
        = (f0^[n] ((t:ℝ):ℂ)).im + 2 * (f0^[n] ((t:ℝ):ℂ)).re * (f0^[n] ((t:ℝ):ℂ)).im := by
      simp only [f0_eq, Complex.add_im, sq, Complex.mul_im, Complex.mul_re]
      ring
    rw [this, ih]
    ring

lemma orbit_re_succ (t : ℝ) (n : ℕ) :
    (f0^[n + 1] ((t : ℝ) : ℂ)).re
      = (f0^[n] ((t:ℝ):ℂ)).re + ((f0^[n] ((t:ℝ):ℂ)).re) ^ 2 := by
  rw [Function.iterate_succ_apply']
  have him := orbit_im_eq_zero t n
  have : (f0 (f0^[n] ((t:ℝ):ℂ))).re
      = (f0^[n] ((t:ℝ):ℂ)).re + ((f0^[n] ((t:ℝ):ℂ)).re ^ 2 - (f0^[n] ((t:ℝ):ℂ)).im ^ 2) := by
    simp only [f0_eq, Complex.add_re, sq, Complex.mul_re]
  rw [this, him]
  ring

/-! ## The orbit of `ε > 0` blows up -/

lemma orbit_re_ge (ε : ℝ) (hε : 0 < ε) : ∀ n : ℕ,
    ε * (1 + ε) ^ n ≤ (f0^[n] ((ε : ℝ) : ℂ)).re := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orbit_re_succ]
    have hle : ε * (1 + ε) ^ n ≤ (f0^[n] ((ε:ℝ):ℂ)).re := ih
    have h1 : ε ≤ (f0^[n] ((ε:ℝ):ℂ)).re := by
      have h2 : ε * 1 ≤ ε * (1 + ε) ^ n := by
        have : (1:ℝ) ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
        nlinarith
      linarith
    have hposn : 0 ≤ (f0^[n] ((ε:ℝ):ℂ)).re := le_trans hε.le h1
    have key : ε * (1 + ε) ^ (n+1) = (ε * (1 + ε) ^ n) * (1 + ε) := by ring
    rw [key]
    calc (ε * (1 + ε) ^ n) * (1 + ε)
        ≤ (f0^[n] ((ε:ℝ):ℂ)).re * (1 + ε) :=
          mul_le_mul_of_nonneg_right hle (by linarith : (0:ℝ) ≤ 1 + ε)
      _ ≤ (f0^[n] ((ε:ℝ):ℂ)).re * (1 + (f0^[n] ((ε:ℝ):ℂ)).re) :=
          mul_le_mul_of_nonneg_left (by linarith) hposn
      _ = (f0^[n] ((ε:ℝ):ℂ)).re + ((f0^[n] ((ε:ℝ):ℂ)).re) ^ 2 := by ring

lemma pos_real_not_mem_Basin (ε : ℝ) (hε : 0 < ε) : ((ε : ℝ) : ℂ) ∉ Basin := by
  rintro ⟨U, hU, hmap, hunif⟩
  have h1 : ∀ᶠ n in atTop, ∀ x ∈ U, dist 0 (f0^[n] x) < 1 := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    exact hunif 1 one_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1
  have htend : Tendsto (fun n : ℕ => ε * (1 + ε) ^ n) atTop atTop :=
    Tendsto.const_mul_atTop hε
      (tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1:ℝ) < 1 + ε))
  have hev : ∀ᶠ n in atTop, (1:ℝ) ≤ ε * (1 + ε) ^ n := htend.eventually (eventually_ge_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop N)).exists
  have h2 := hN n hn2 ((ε : ℝ) : ℂ) (mem_of_mem_nhds hU)
  rw [dist_comm, dist_zero_right] at h2
  have h3 : ε * (1 + ε) ^ n ≤ ‖f0^[n] ((ε:ℝ):ℂ)‖ :=
    le_trans (orbit_re_ge ε hε n) (Complex.re_le_norm _)
  linarith

lemma not_mem_Basin_zero : (0 : ℂ) ∉ Basin := by
  intro h0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_Basin.mem_nhds h0)
  have hmem : ((ε/2 : ℝ) : ℂ) ∈ Basin := hball (by
    rw [mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < ε/2)]
    linarith)
  exact pos_real_not_mem_Basin (ε/2) (by linarith) hmem

lemma f0_iterate_ne_zero {z : ℂ} (hz : z ∈ Basin) : ∀ n : ℕ, f0^[n] z ≠ 0 := by
  have hmem : ∀ n : ℕ, f0^[n] z ∈ Basin := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact f0_mem_Basin ih
  intro n h
  have h' := hmem n
  rw [h] at h'
  exact not_mem_Basin_zero h'

/-! ## Real points of `[-1/2, 0)` lie in the basin -/

lemma basin_of_iterate_mem {z : ℂ} : ∀ n : ℕ, f0^[n] z ∈ Basin → z ∈ Basin := by
  intro n
  induction n with
  | zero => intro h; simpa using h
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply'] at h
    exact ih (mem_Basin_of_f0_mem h)

lemma ofReal_mem_Basin {t : ℝ} (ht1 : -(1 / 2) ≤ t) (ht2 : t < 0) : (t : ℂ) ∈ Basin := by
  obtain ⟨r, M, hr, hM, h1rM, hsub, hconn, hint⟩ := exists_petal_data
  obtain ⟨N, hN⟩ := real_orbit_mem_petal hr h1rM ht1 ht2
  exact basin_of_iterate_mem N (hsub hN)

end
end Work.F0Facts
