import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertU.geom

/-!
# The fat discs at `±I η` lie in the repelling sector `QLeft ξ`

Shishikura's repelling sector is `MandelDim.QLeft ξ = {w | π/3 < |arg (w + ξ)|}`, which by
`Work.PertU.QLeft_iff` is the elementary set `{w | 2 * (w + ξ).re < ‖w + ξ‖}`.

Here we treat the *fat* discs of radius `3η/10` centred at `I η` and `-I η` (as opposed to the
`η/4`-discs `MandelDim.Dsm η`), which is the shape the perturbation argument uses: for such a
disc the modulus of every point lies between `7η/10` and `13η/10` (exactly `η ∓ 3η/10`), and
for `η` large compared with `|ξ|` the whole union lies in the sector.

Geometrically: the discs sit at arguments within `arcsin(3/10) ≤ 18°` of `±π/2`, whereas the
boundary of the sector is at argument `±π/3`; the angular gap beats the shift `ξ` once
`η > (10 √3 / (7 - 3√3)) |ξ|`, and the numerical margin `4 √3 < 7` (i.e. `48 < 49`) makes
`η ≥ 10 |ξ| + 1` enough.  The elementary criterion, from `Work.PertU.geom`, is
`√3 · Re w < |Im w| ⟹ 2 Re w < ‖w‖`.
-/

namespace Work.Pert

open Complex Metric

noncomputable section

/-- The numerical margin `4 √3 < 7` (equivalently `48 < 49`). -/
lemma four_mul_sqrt_three_lt_seven : 4 * Real.sqrt 3 < 7 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 3, h3, sq_nonneg (7 - 4 * Real.sqrt 3)]

/-- `‖I · η‖ = η` for `η ≥ 0`. -/
lemma norm_I_mul_ofReal {η : ℝ} (hη : 0 ≤ η) : ‖I * (η : ℂ)‖ = η := by
  rw [Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hη]

/-- **Norm bounds on a fat disc.**  A point of the radius-`3η/10` disc around a centre of
norm `η` has norm between `7η/10` and `13η/10`. -/
lemma norm_bounds_of_mem_closedBall_fat {η : ℝ} {c z : ℂ} (hc : ‖c‖ = η)
    (hz : z ∈ closedBall c (3 * η / 10)) : 7 * η / 10 ≤ ‖z‖ ∧ ‖z‖ ≤ 13 * η / 10 := by
  have hzn : ‖z - c‖ ≤ 3 * η / 10 := by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact hz
  constructor
  · have h := (abs_le.mp (abs_norm_sub_norm_le c z)).2
    rw [norm_sub_rev] at h
    linarith
  · have h := norm_add_le (z - c) c
    have e : (z - c) + c = z := by ring
    rw [e, hc] at h
    linarith

/-- **Upper gate.**  If `η > 0` and `√3 (3η/10 + |ξ|) < 7η/10`, then the fat disc around
`I η` is contained in the sector `QLeft ξ`. -/
lemma mem_QLeft_of_mem_closedBall_I_mul {ξ η : ℝ} (hη : 0 < η)
    (hbig : Real.sqrt 3 * (3 * η / 10 + |ξ|) < 7 * η / 10) {z : ℂ}
    (hz : z ∈ closedBall (I * (η : ℂ)) (3 * η / 10)) : z ∈ MandelDim.QLeft ξ := by
  rw [Work.PertU.QLeft_iff]
  apply Work.PertU.two_mul_re_lt_norm_of_sqrt3_mul_re_lt_abs_im
  have hzn : ‖z - I * (η : ℂ)‖ ≤ 3 * η / 10 := by
    rw [mem_closedBall, dist_eq_norm] at hz
    exact hz
  -- real part bound
  have hRe : z.re ≤ 3 * η / 10 := by
    have h := Complex.abs_re_le_norm (z - I * (η : ℂ))
    have he : (z - I * (η : ℂ)).re = z.re := by simp [Complex.sub_re, Complex.mul_re]
    rw [he] at h
    linarith [(abs_le.mp h).2]
  -- imaginary part bound: `z` is in the upper half plane, far above the origin
  have hIm : 7 * η / 10 ≤ |z.im| := by
    have h := Complex.abs_im_le_norm (z - I * (η : ℂ))
    have he : (z - I * (η : ℂ)).im = z.im - η := by simp [Complex.sub_im, Complex.mul_im]
    rw [he] at h
    have h2 : η - 3 * η / 10 ≤ z.im := by linarith [(abs_le.mp h).1]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z.im)]
    linarith
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  have h1 : Real.sqrt 3 * (z.re + ξ) ≤ Real.sqrt 3 * (3 * η / 10 + |ξ|) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self ξ]) (Real.sqrt_nonneg 3)
  linarith

/-- **Lower gate.**  The reflection of the previous statement: if `η > 0` and
`√3 (3η/10 + |ξ|) < 7η/10`, then the fat disc around `-I η` is contained in `QLeft ξ`. -/
lemma mem_QLeft_of_mem_closedBall_neg_I_mul {ξ η : ℝ} (hη : 0 < η)
    (hbig : Real.sqrt 3 * (3 * η / 10 + |ξ|) < 7 * η / 10) {z : ℂ}
    (hz : z ∈ closedBall (-(I * (η : ℂ))) (3 * η / 10)) : z ∈ MandelDim.QLeft ξ := by
  -- reflect into the upper gate by complex conjugation
  have hconj : (starRingEnd ℂ) z ∈ closedBall (I * (η : ℂ)) (3 * η / 10) := by
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have e : (starRingEnd ℂ) z - I * (η : ℂ)
        = (starRingEnd ℂ) (z - (-(I * (η : ℂ)))) := by
      rw [map_sub, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [e, Complex.norm_conj]
    exact hz
  exact (Work.PertU.conj_mem_QLeft_iff ξ z).mp
    (mem_QLeft_of_mem_closedBall_I_mul hη hbig hconj)

theorem fat_discs_subset_QLeft (ξ : ℝ) : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
    (Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
        Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10)) ⊆ MandelDim.QLeft ξ ∧
      (∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
          Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10),
        7 * η / 10 ≤ ‖w‖ ∧ ‖w‖ ≤ 13 * η / 10) := by
  refine ⟨10 * |ξ| + 1, by positivity, ?_⟩
  intro η hη
  have hηpos : 0 < η := by
    have h0 : (0 : ℝ) < 10 * |ξ| + 1 := by positivity
    linarith
  -- `|ξ| < η/10`, which is the whole point of the threshold `10 |ξ| + 1`
  have hξη : |ξ| < η / 10 := by linarith
  -- the angular margin, using `4 √3 < 7`
  have hbig : Real.sqrt 3 * (3 * η / 10 + |ξ|) < 7 * η / 10 := by
    have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
    have h1 : 3 * η / 10 + |ξ| < 4 * η / 10 := by linarith
    have h2 : Real.sqrt 3 * (3 * η / 10 + |ξ|) < Real.sqrt 3 * (4 * η / 10) :=
      mul_lt_mul_of_pos_left h1 hs3
    have h3 : Real.sqrt 3 * (4 * η / 10) = (4 * Real.sqrt 3) * η / 10 := by ring
    have h4 : (4 * Real.sqrt 3) * η / 10 < 7 * η / 10 := by
      have h4' := mul_lt_mul_of_pos_right four_mul_sqrt_three_lt_seven hηpos
      linarith
    linarith
  constructor
  · intro z hz
    rcases hz with hz | hz
    · exact mem_QLeft_of_mem_closedBall_I_mul hηpos hbig hz
    · exact mem_QLeft_of_mem_closedBall_neg_I_mul hηpos hbig hz
  · intro w hw
    rcases hw with hw | hw
    · exact norm_bounds_of_mem_closedBall_fat (norm_I_mul_ofReal (le_of_lt hηpos)) hw
    · exact norm_bounds_of_mem_closedBall_fat
        (by rw [norm_neg, norm_I_mul_ofReal (le_of_lt hηpos)]) hw

end

end Work.Pert
