import Mathlib
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanSep.centre_numbers

/-!
# Holomorphy of the backward branch on balls about the axis points

Let `0 < a < 1`, let `c = -1/2 + 2k` (`k : ℤ`) be a point of the equichordal axis coset, and let
`R = (1-a)/8`.  Every point `Q` of the disc of radius `R` about `((c : ℂ), 0)` satisfies

* `‖Q₁ - c‖ < R ≤ s/4` and `‖Q₂‖ < R ≤ s/4`, where `s = |c + a/2| ≥ (1-a)/2` is the distance
  of the centre from the focus `-a/2` (`FanSep.centre_numbers`);

consequently, writing `W = Q₁ + a/2`,

* `|W.re| ≥ s - s/4 = 3s/4`, `|W.im| ≤ s/4` and `re(Q₂²) ≥ -‖Q₂‖² ≥ -(s/4)²`,

so that

`re((Q₁ + a/2)² + Q₂²) ≥ 9s²/16 - s²/16 - s²/16 = 7s²/16 > 0`.

Hence the radicand of `invBranch a s` lies in the open right half plane on this disc, the
principal square root is analytic there, and `invBranch a s` is holomorphic on the disc
(`analytic_invBranch`).
-/

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- On the disc of radius `(1-a)/8` about an axis point `c = -1/2 + 2k` the radicand
`(Q.1 + a/2)² + Q.2²` of the backward branch has positive real part. -/
lemma radicand_pos_ball {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℝ}
    (hc : ∃ k : ℤ, c = -1 / 2 + 2 * (k : ℝ)) {Q : ℂ × ℂ}
    (hQ : Q ∈ Metric.ball (((c : ℂ), (0 : ℂ))) ((1 - a) / 8)) :
    0 < (((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)).re := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨hcn1, _hcn2⟩ := FanSep.centre_numbers ha0 ha1
  -- the distance from the centre to the focus `-a/2`
  have hs : (1 - a) / 2 ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| := by
    have h := (hcn1 k).1
    rwa [FanSep.norm_ofReal_add_eq_abs] at h
  have hRle : (1 - a) / 8 ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by linarith
  have hs0 : 0 < |(-1 / 2 + 2 * (k : ℝ)) + a / 2| := by linarith
  -- coordinate bounds: both coordinates of `Q` are within `R ≤ s/4` of `(c, 0)`
  have hdist : dist Q ((((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ), (0 : ℂ))) < (1 - a) / 8 :=
    Metric.mem_ball.mp hQ
  have hd1 : dist Q.1 (((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ)) < (1 - a) / 8 := by
    rw [Prod.dist_eq] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) hdist
  have hd2 : dist Q.2 (0 : ℂ) < (1 - a) / 8 := by
    rw [Prod.dist_eq] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) hdist
  have hQ1 : ‖Q.1 - (((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ))‖
      ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by
    rw [dist_eq_norm] at hd1
    exact le_trans hd1.le hRle
  have hQ2 : ‖Q.2‖ ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by
    rw [dist_zero_right] at hd2
    exact le_trans hd2.le hRle
  have hre1 : |Q.1.re - (-1 / 2 + 2 * (k : ℝ))|
      ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by
    have h := Complex.abs_re_le_norm (Q.1 - (((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ)))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    exact le_trans h hQ1
  have him1 : |Q.1.im| ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by
    have h := Complex.abs_im_le_norm (Q.1 - (((-1 / 2 + 2 * (k : ℝ) : ℝ) : ℂ)))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact le_trans h hQ1
  -- the real part of `Q.1 + a/2` stays at distance `≤ s/4` from `± s`
  have hWre : 3 * |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4
      ≤ |(Q.1 + ((a / 2 : ℝ) : ℂ)).re| := by
    have h1 : (Q.1 + ((a / 2 : ℝ) : ℂ)).re
        = ((-1 / 2 + 2 * (k : ℝ)) + a / 2)
          + (Q.1.re - (-1 / 2 + 2 * (k : ℝ))) := by
      rw [Complex.add_re, Complex.ofReal_re]; ring
    rw [h1]
    have h2 : |(-1 / 2 + 2 * (k : ℝ)) + a / 2| - |Q.1.re - (-1 / 2 + 2 * (k : ℝ))|
        ≤ |((-1 / 2 + 2 * (k : ℝ)) + a / 2)
            + (Q.1.re - (-1 / 2 + 2 * (k : ℝ)))| := by
      have h3 := abs_sub_abs_le_abs_sub ((-1 / 2 + 2 * (k : ℝ)) + a / 2)
        (-(Q.1.re - (-1 / 2 + 2 * (k : ℝ))))
      rw [abs_neg] at h3
      have h4 : ((-1 / 2 + 2 * (k : ℝ)) + a / 2) - (-(Q.1.re - (-1 / 2 + 2 * (k : ℝ))))
          = ((-1 / 2 + 2 * (k : ℝ)) + a / 2)
            + (Q.1.re - (-1 / 2 + 2 * (k : ℝ))) := by ring
      rwa [h4] at h3
    linarith [h2, hre1]
  have hWim : |(Q.1 + ((a / 2 : ℝ) : ℂ)).im| ≤ |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact him1
  -- decompose the real part of the radicand
  have hre : (((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)).re
      = ((Q.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 - (Q.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2)
        + (Q.2.re ^ 2 - Q.2.im ^ 2) := by
    simp only [Complex.add_re, pow_two, Complex.mul_re]
  rw [hre]
  -- the three estimates
  have h1 : (3 * |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4) ^ 2
      ≤ (Q.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 := by
    have ht0 : 0 ≤ 3 * |(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4 := by positivity
    have h := pow_le_pow_left₀ ht0 hWre 2
    rwa [sq_abs (Q.1 + ((a / 2 : ℝ) : ℂ)).re] at h
  have h2 : (Q.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2
      ≤ (|(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Q.1 + ((a / 2 : ℝ) : ℂ)).im) hWim 2
    rwa [sq_abs (Q.1 + ((a / 2 : ℝ) : ℂ)).im] at h
  have h3 : -( (|(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4) ^ 2) ≤ Q.2.re ^ 2 - Q.2.im ^ 2 := by
    have h4 : Q.2.im ^ 2 ≤ ‖Q.2‖ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg Q.2.im) (Complex.abs_im_le_norm Q.2) 2
      rwa [sq_abs Q.2.im] at h
    have h5 : ‖Q.2‖ ^ 2 ≤ (|(-1 / 2 + 2 * (k : ℝ)) + a / 2| / 4) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hQ2 2
    nlinarith [h4, h5, sq_nonneg Q.2.re]
  nlinarith [h1, h2, h3, hs0]

/-- On the disc of radius `(1-a)/8` about any axis point `c = -1/2 + 2k` of the equichordal
grid, the radicand `(Q.1 + a/2)² + Q.2²` has positive real part, so the backward branch
`invBranch a s` is holomorphic there. -/
theorem invBranch_axis_differentiableOn_ball {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {c : ℝ} (hc : ∃ k : ℤ, c = -1 / 2 + 2 * (k : ℝ)) (s : Bool) :
    DifferentiableOn ℂ (Work.EQ.invBranch a s)
      (Metric.ball (((c : ℂ), (0 : ℂ))) ((1 - a) / 8)) := by
  intro Q hQ
  exact (analytic_invBranch (a := a) (s := s) (Q := Q)
    (radicand_pos_ball ha0 ha1 hc hQ)).differentiableWithinAt

end

end Work.EQ.FanTri
