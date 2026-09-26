/-
# The window-ball geometry for `Work.CKFinal.exists_F2_socket`

This file proves the elementary geometric input of the socket construction
(`Submission/Work/CKFinal/exists_F2_socket.lean`):

for `s > 0` the *hyperbolic* ball of radius `min s s⁻¹ / 16` about the centre `1 + i s`

* stays inside the region `|Re τ - 1| < thin (Im τ)` (`thin y = min (y²) 1 / 4`), and
* meets the "lens" `|τ ∓ 1/2| > 1/2` from the left of the line `Re τ = 1`; hence every point
  of the ball with `Re τ < 1` lies in the `Γ(2)`-fundamental domain `𝒟`.

The proof is in three algebraic steps.

1. `sq_sum_cosh` (from Mathlib's `UpperHalfPlane.cosh_dist'`): the Euclidean squared
   distance to a hyperbolic ball of radius `d` is
   `|z - w|² = 2 · Im z · Im w · (cosh d - 1)`.
   Since `cosh d - 1 = 2 sinh(d/2)²` and `sinh u ≤ 2u` for `u ≤ 1`, a point at hyperbolic
   distance `d < 1/16` satisfies
   `(Re τ - 1)² ≤ 4 · Im τ · s · d²` and `(Im τ - s)² ≤ 4 · Im τ · s · d²`.

2. `winBall_core` (real arithmetic): these two inequalities, together with
   `d < min s s⁻¹ / 16`, force `Im τ ∈ [(15/16)² s, (16/15)² s]` and
   `|Re τ - 1| < min ((Im τ)²) 1 / 4`.

3. `lens_mem` (real arithmetic): consequently a point of the ball with `Re τ < 1` has
   `-1 < Re τ < 1` and `|τ ∓ 1/2|² > 1/4`.

The three pieces are proved in the sibling modules `sq_sum_cosh`, `winBall_core`,
`lens_mem`, `sinh_le_two_mul` of this directory; this file assembles them.
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Basic
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.CKFinal.Socket.sinh_le_two_mul
import Submission.Work.CKFinal.Socket.sq_sum_cosh
import Submission.Work.CKFinal.Socket.winBall_core
import Submission.Work.CKFinal.Socket.lens_mem

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal.Socket

/-- `cosh d - 1 = 2 sinh(d/2)²`. -/
private lemma cc_cosh_sub_one_eq (d : ℝ) :
    Real.cosh d - 1 = 2 * Real.sinh (d / 2) ^ 2 := by
  have h2 : Real.cosh d = Real.cosh (2 * (d / 2)) := by congr 1; ring
  rw [h2, Real.cosh_two_mul, Real.cosh_sq]
  ring

/-- `min s s⁻¹ ≤ 1` for `s > 0`. -/
private lemma cc_min_self_inv_le_one (s : ℝ) : min s s⁻¹ ≤ 1 := by
  rcases le_total s 1 with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (inv_le_one_of_one_le₀ h)

theorem winBall_geometry (s : ℝ) (hs : 0 < s) :
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s hs) < min s s⁻¹ / 16 →
      |τ.re - 1| < Work.CKFinal.Socket.thin τ.im) ∧
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s hs) < min s s⁻¹ / 16 →
      τ.re < 1 → τ ∈ Work.Asymptotics.DomainD) := by
  have hmin1 : min s s⁻¹ ≤ 1 := cc_min_self_inv_le_one s
  have hpart1 : ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s hs) < min s s⁻¹ / 16 → |τ.re - 1| < thin τ.im := by
    intro τ hd
    set τ₀ := Work.Asymptotics.onePlusI s hs with hτ₀
    have hre0 : τ₀.re = 1 := Work.Asymptotics.onePlusI_re s hs
    have him0 : τ₀.im = s := Work.Asymptotics.onePlusI_im s hs
    have hy : 0 < τ.im := τ.im_pos
    have hd0 : 0 ≤ dist τ τ₀ := dist_nonneg
    -- Mathlib: `cosh (dist τ τ₀) = ((τ.re - 1)² + τ.im² + s²) / (2 τ.im s)`
    have hkey := sq_sum_cosh τ τ₀
    rw [hre0, him0] at hkey
    have hdd : dist τ τ₀ < min s s⁻¹ / 16 := hd
    have h16 : min s s⁻¹ / 16 ≤ 1 / 16 := by linarith
    have hhalf1 : dist τ τ₀ / 2 ≤ 1 := by linarith
    have hhalf0 : 0 ≤ dist τ τ₀ / 2 := by linarith
    have hs2 : Real.sinh (dist τ τ₀ / 2) ≤ 2 * (dist τ τ₀ / 2) :=
      sinh_le_two_mul _ hhalf0 hhalf1
    have hsinh0 : 0 ≤ Real.sinh (dist τ τ₀ / 2) := by
      rw [Real.sinh_nonneg_iff]; linarith
    have hsq : Real.sinh (dist τ τ₀ / 2) ^ 2 ≤ (dist τ τ₀) ^ 2 := by
      have h3 : (2 * (dist τ τ₀ / 2)) ^ 2 = (dist τ τ₀) ^ 2 := by ring
      calc Real.sinh (dist τ τ₀ / 2) ^ 2 ≤ (2 * (dist τ τ₀ / 2)) ^ 2 :=
            pow_le_pow_left₀ hsinh0 hs2 2
        _ = (dist τ τ₀) ^ 2 := h3
    have hcoshle : Real.cosh (dist τ τ₀) - 1 ≤ 2 * (dist τ τ₀) ^ 2 := by
      rw [cc_cosh_sub_one_eq]; linarith
    have hcf : 2 * τ.im * s * (Real.cosh (dist τ τ₀) - 1) ≤ 4 * τ.im * s * (dist τ τ₀) ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_left hcoshle (by positivity : (0 : ℝ) ≤ 2 * τ.im * s)
      nlinarith [h2]
    have hx : (τ.re - 1) ^ 2 ≤ 4 * τ.im * s * (dist τ τ₀) ^ 2 := by
      have h1 : (τ.re - 1) ^ 2 ≤ 2 * τ.im * s * (Real.cosh (dist τ τ₀) - 1) := by
        nlinarith [sq_nonneg (τ.im - s), hkey]
      linarith
    have hyy : (τ.im - s) ^ 2 ≤ 4 * τ.im * s * (dist τ τ₀) ^ 2 := by
      have h1 : (τ.im - s) ^ 2 ≤ 2 * τ.im * s * (Real.cosh (dist τ τ₀) - 1) := by
        nlinarith [sq_nonneg (τ.re - 1), hkey]
      linarith
    have hres := winBall_core s τ.re τ.im (dist τ τ₀) hs hy hd0 hdd hx hyy
    rw [thin]
    exact hres.1
  have hpart2 : ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s hs) < min s s⁻¹ / 16 →
      τ.re < 1 → τ ∈ Work.Asymptotics.DomainD := by
    intro τ hd hx1
    have h1 := lens_mem τ.re τ.im τ.im_pos hx1 (hpart1 τ hd)
    obtain ⟨hn1, hlt, hd1, hd2⟩ := h1
    rw [Work.Asymptotics.mem_DomainD]
    refine ⟨hn1, hlt, ?_, ?_⟩
    · have hcast : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      have hsq : ‖((τ : ℂ) - (1 / 2 : ℂ))‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
        rw [hcast, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      have h2 : (1 / 2 : ℝ) ^ 2 < ‖((τ : ℂ) - (1 / 2 : ℂ))‖ ^ 2 := by
        have hc : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
        rw [hc, hsq]
        exact hd1
      nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
    · have hcast : ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      have hsq : ‖((τ : ℂ) + (1 / 2 : ℂ))‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
        rw [hcast, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      have h2 : (1 / 2 : ℝ) ^ 2 < ‖((τ : ℂ) + (1 / 2 : ℂ))‖ ^ 2 := by
        have hc : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
        rw [hc, hsq]
        exact hd2
      nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]
  exact ⟨hpart1, hpart2⟩

end Work.CKFinal.Socket
