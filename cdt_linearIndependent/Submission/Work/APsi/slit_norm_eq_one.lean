import Mathlib
import Submission.Work.APsi.defs

/-!
# Area `Ψ_A`: the Joukowski cut-off for the slit map

The slit map `slit r z` (`(𝔻,0) ≅ (𝔻 ∖ (-1,-r], 0)`, CDT arXiv:2408.15403) satisfies the
Joukowski relation (`slit_joukowski_ab`, in `Submission.Work.APsi.defs`)

  `slit r z + (slit r z)⁻¹ = α (z + z⁻¹) + β`,  `α = (1+r)²/(4r)`, `β = -(r-1)²/(2r)`.

The point of this module is the converse direction of the disc bound: a point of the unit
circle can only be hit at `‖z‖ = 1`.  The reason is purely the Joukowski relation together
with the elementary fact that `z + z⁻¹ ∈ [-2,2]` forces `‖z‖ = 1`:

* if `‖slit r z‖ = 1` then `(slit r z) + (slit r z)⁻¹ = 2 Re (slit r z) ∈ [-2,2]`, so the
  Joukowski relation gives `z + z⁻¹ = u` for an explicit real `u` in `[-2,2]`;
* `z + z⁻¹ = u` real means `z` is a root of the real quadratic `X² - uX + 1`, whose other
  root is `1/z = conj z`, and `|u| ≤ 2` then forces `z conj z = 1`.

`add_inv_norm_eq_one_aux` is the second step, `slit_bound_aux` the numerically explicit form
of the first, and `slit_norm_eq_one` the combination.
-/

namespace Work.APsi

open Submission.CDTPlan Complex
open scoped ComplexConjugate

/-- A real Joukowski cut-off: if `z + z⁻¹` is a real number of modulus `≤ 2`, then `‖z‖ = 1`.

Indeed `z` is then a root of the quadratic `X ^ 2 - u * X + 1` with real coefficients `u`, and
its conjugate is the other root; if the roots coincide `z` is real and `|u| = |z + z⁻¹| ≥ 2`
forces `|z| = 1`, while otherwise `1 = z * conj z = ‖z‖ ^ 2`. -/
theorem add_inv_norm_eq_one_aux {z : ℂ} (hz : z ≠ 0) {u : ℝ}
    (h : z + z⁻¹ = (u : ℂ)) (hu : |u| ≤ 2) : ‖z‖ = 1 := by
  have hquad : z ^ 2 - (u : ℂ) * z + 1 = 0 := by
    have h1 : z * z + 1 = (u : ℂ) * z := by
      have h1' : z * (z + z⁻¹) = z * (u : ℂ) := by rw [h]
      rw [mul_add, mul_inv_cancel₀ hz] at h1'
      rw [mul_comm z (u : ℂ)] at h1'
      exact h1'
    rw [show z ^ 2 - (u : ℂ) * z + 1 = z * z + 1 - (u : ℂ) * z by ring, h1, sub_self]
  -- the conjugate of `z` is a root of the same real quadratic
  have hquadC : (conj z) ^ 2 - (u : ℂ) * conj z + 1 = 0 := by
    have hc := congrArg conj hquad
    simpa using hc
  -- subtracting the two quadratic relations
  have hsub : (z - conj z) * (z + conj z - (u : ℂ)) = 0 := by
    have h0 : (z ^ 2 - (u : ℂ) * z + 1) - ((conj z) ^ 2 - (u : ℂ) * conj z + 1) = 0 := by
      rw [hquad, hquadC, sub_zero]
    rwa [show (z ^ 2 - (u : ℂ) * z + 1) - ((conj z) ^ 2 - (u : ℂ) * conj z + 1)
        = (z - conj z) * (z + conj z - (u : ℂ)) by ring] at h0
  rcases mul_eq_zero.mp hsub with hd | hsum
  · -- `z = conj z`: `z` is real, and `|u| = |z + z⁻¹| ≥ 2` with `|u| ≤ 2` forces `|z| = 1`
    have hd' : z = conj z := sub_eq_zero.mp hd
    have hzim : z.im = 0 := Complex.conj_eq_iff_im.mp hd'.symm
    have hzre : z = (z.re : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp
      · simpa [Complex.ofReal_im] using hzim
    have hx : z.re + z.re⁻¹ = u := by
      have h' : ((z.re : ℂ) + ((z.re : ℂ))⁻¹) = (u : ℂ) := by
        have h'' := h
        rw [hzre] at h''
        exact h''
      rw [← Complex.ofReal_inv, ← Complex.ofReal_add] at h'
      exact Complex.ofReal_inj.mp h'
    have hxn : z.re ≠ 0 := by
      intro h0
      apply hz
      rw [hzre, h0]
      simp
    -- `(x - x⁻¹) ^ 2 = u ^ 2 - 4 ≤ 0` for `x = z.re`
    have hsq : (z.re - z.re⁻¹) ^ 2 = u ^ 2 - 4 := by
      rw [← hx]
      field_simp
      ring
    have hu2 : u ^ 2 ≤ 4 := by
      rcases abs_le.mp hu with ⟨h1, h2⟩
      nlinarith
    have hzero : z.re - z.re⁻¹ = 0 := by
      have hle : (z.re - z.re⁻¹) ^ 2 ≤ 0 := by rw [hsq]; linarith
      nlinarith [sq_nonneg (z.re - z.re⁻¹)]
    have hx2 : z.re ^ 2 = 1 := by
      have hh : z.re * (z.re - z.re⁻¹) = 0 := by rw [hzero, mul_zero]
      rw [mul_sub, mul_inv_cancel₀ hxn, sub_eq_zero] at hh
      rw [pow_two]
      exact hh
    have hnorm : ‖(z.re : ℂ)‖ = 1 := by
      have h2 : ‖(z.re : ℂ)‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        simpa [pow_two] using hx2
      nlinarith [norm_nonneg (z.re : ℂ)]
    rw [hzre]
    exact hnorm
  · -- `z + conj z = u`: the quadratic relation collapses to `z * conj z = 1`
    have hsum' : (u : ℂ) = z + conj z := (sub_eq_zero.mp hsum).symm
    have hmul : z * conj z = 1 := by
      have hq := hquad
      rw [hsum'] at hq
      have hh : (1 : ℂ) - conj z * z = 0 := by
        rw [← hq]
        ring
      rw [sub_eq_zero] at hh
      rw [mul_comm] at hh
      exact hh.symm
    have hmul' : ((Complex.normSq z : ℝ) : ℂ) = 1 := by
      rw [← Complex.mul_conj]
      exact hmul
    have hns : Complex.normSq z = 1 := Complex.ofReal_inj.mp hmul'
    have h2 : ‖z‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hns
    nlinarith [norm_nonneg z]

/-- The explicit Joukowski cut-off used for `slit`: for `0 < r` and `|c| ≤ 2`,
`(c + (r-1)²/(2r)) / ((1+r)²/(4r)) ∈ [-2,2]`.  Both endpoints are sharp: the upper one is
`2` identically, the lower one is `-(1+r²)/r ≤ -2`. -/
theorem slit_bound_aux (r c : ℝ) (hr0 : 0 < r) (hc : |c| ≤ 2) :
    |(c + (r - 1) ^ 2 / (2 * r)) / ((1 + r) ^ 2 / (4 * r))| ≤ 2 := by
  have hA : 0 < (1 + r) ^ 2 / (4 * r) := by positivity
  rw [abs_le] at hc ⊢
  obtain ⟨hc1, hc2⟩ := hc
  constructor
  · rw [le_div_iff₀ hA]
    have h1 : 2 ≤ 2 * ((1 + r) ^ 2 / (4 * r)) + (r - 1) ^ 2 / (2 * r) := by
      have h : 2 * ((1 + r) ^ 2 / (4 * r)) + (r - 1) ^ 2 / (2 * r) - 2 = (r - 1) ^ 2 / r := by
        field_simp
        ring
      have h2 : 0 ≤ (r - 1) ^ 2 / r := by positivity
      linarith
    nlinarith
  · rw [div_le_iff₀ hA]
    have h1 : 2 * ((1 + r) ^ 2 / (4 * r)) - (r - 1) ^ 2 / (2 * r) = 2 := by
      field_simp
      ring
    nlinarith

theorem slit_norm_eq_one (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    ‖Submission.CDTPlan.slit r z‖ = 1 → ‖z‖ = 1 := by
  intro h
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Submission.CDTPlan.slit] at h
  · set w : ℂ := Submission.CDTPlan.slit r z with hw
    have hw1 : ‖w‖ = 1 := by rw [hw]; exact h
    -- the Joukowski relation for the slit map, as an equation in `w`
    have hj := slit_joukowski_ab r hr0 z hz
    rw [← hw] at hj
    -- `w` lies on the unit circle, so `w + w⁻¹ = 2 Re w` is real
    have hcinv : w + w⁻¹ = (((2 * w.re : ℝ)) : ℂ) := by
      rw [Complex.inv_eq_conj hw1, Complex.add_conj]
    set A : ℝ := (1 + r) ^ 2 / (4 * r) with hA_def
    set B : ℝ := (r - 1) ^ 2 / (2 * r) with hB_def
    have hApos : 0 < A := by rw [hA_def]; positivity
    have hAne : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hApos)
    have hAcoef : ((1 + (r : ℂ)) ^ 2 / (4 * (r : ℂ))) = (A : ℂ) := by
      rw [hA_def]; push_cast; ring
    have hBcoef : (((r : ℂ) - 1) ^ 2 / (2 * (r : ℂ))) = (B : ℂ) := by
      rw [hB_def]; push_cast; ring
    have h2' : (A : ℂ) * (z + z⁻¹) - (B : ℂ) = (((2 * w.re : ℝ)) : ℂ) := by
      have h2 := hj
      rw [hAcoef, hBcoef, hcinv] at h2
      rw [h2]
    have hquad : (A : ℂ) * (z + z⁻¹) = (((2 * w.re : ℝ)) : ℂ) + (B : ℂ) :=
      sub_eq_iff_eq_add.mp h2'
    have hcast : (((2 * w.re + B : ℝ)) : ℂ) = (((2 * w.re : ℝ)) : ℂ) + (B : ℂ) := by
      push_cast; ring
    have hmain : z + z⁻¹ = (((2 * w.re + B) / A : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, hcast]
      rw [eq_div_iff hAne, mul_comm]
      exact hquad
    have hc2 : |2 * w.re| ≤ 2 := by
      have hre := Complex.abs_re_le_norm w
      rw [hw1] at hre
      calc |2 * w.re| = 2 * |w.re| := by rw [abs_mul]; norm_num
        _ ≤ 2 := by linarith
    have hbound : |((2 * w.re + B) / A)| ≤ 2 := by
      rw [hA_def, hB_def]
      exact slit_bound_aux r (2 * w.re) hr0 hc2
    exact add_inv_norm_eq_one_aux hz hmain hbound

end Work.APsi
