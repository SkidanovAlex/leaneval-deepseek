import Mathlib
import Submission.Work.ANum.ACertD
import Submission.Work.ANum.spick_shim
import Submission.Work.ANum.spick_dist

/-!
# Sharp (pseudohyperbolic) disc bound for a self-map of the unit disc

We derive from the Schwarz–Pick *distance* inequality (`Work.ANum.spick_dist`) the sharp estimate

`‖f w - f c‖ ≤ (1 - ‖f c‖²) ρ / (1 - ‖c‖(‖c‖ + ρ) - ρ ‖f c‖)`

for a holomorphic self-map `f` of the unit disc and `‖w - c‖ ≤ ρ`, `‖c‖ + ρ < 1`.

The proof multiplies the Schwarz–Pick distance inequality by the denominator
`1 - star (f c) * f w`, bounds that denominator by the triangle inequality
`‖1 - star (f c) * f w‖ ≤ (1 - ‖f c‖²) + ‖f c‖ ‖f w - f c‖` (which uses `star a * a = ‖a‖²`) and
`‖1 - star c * w‖ ≥ 1 - ‖c‖(‖c‖ + ρ)`, and solves the resulting linear inequality for
`‖f w - f c‖`.  The degenerate case `‖f c‖ = 1` is handled by the maximum modulus principle.
-/

open Complex Metric
open scoped ComplexConjugate Topology

namespace Work.ANum

/-- **Numerator bound.** If `‖a‖ ≤ 1` then `‖1 - star a * x‖ ≤ (1 - ‖a‖²) + ‖a‖ ‖x - a‖`: this is
the triangle inequality applied to `1 - star a * x = (1 - star a * a) + star a * (a - x)` together
with `star a * a = ‖a‖²`. -/
lemma norm_one_sub_star_mul_le {a x : ℂ} (ha : ‖a‖ ≤ 1) :
    ‖1 - star a * x‖ ≤ (1 - ‖a‖ ^ 2) + ‖a‖ * ‖x - a‖ := by
  have hcast : 1 - star a * a = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self (z := a), Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h1 : 1 - star a * x = (1 - star a * a) + star a * (a - x) := by ring
  calc ‖1 - star a * x‖
      = ‖(1 - star a * a) + star a * (a - x)‖ := by rw [h1]
    _ ≤ ‖1 - star a * a‖ + ‖star a * (a - x)‖ := norm_add_le _ _
    _ = (1 - ‖a‖ ^ 2) + ‖a‖ * ‖x - a‖ := by
        rw [hcast, norm_mul, norm_star, norm_sub_rev a x,
          Complex.norm_of_nonneg (by nlinarith [norm_nonneg a, ha])]

/-- The case `‖f c‖ < 1` of the sharp disc bound. -/
theorem disc_selfmap_bound_hyper_lt {f : ℂ → ℂ} {c w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hd : ‖c‖ + ρ < 1) (hf : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ f z)
    (hmap : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1) (hw : ‖w - c‖ ≤ ρ) (hflt : ‖f c‖ < 1) :
    ‖f w - f c‖ ≤ (1 - ‖f c‖ ^ 2) * ρ / (1 - ‖c‖ * (‖c‖ + ρ) - ρ * ‖f c‖) := by
  have hc1 : ‖c‖ < 1 := by linarith
  have hwn : ‖w‖ ≤ ‖c‖ + ρ := by
    calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ρ := by linarith
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hwn hd
  have hfw1 : ‖f w‖ ≤ 1 := hmap w (le_of_lt hw1)
  have hA : 0 < 1 - ‖c‖ * (‖c‖ + ρ) := by nlinarith [norm_nonneg c, hd]
  have hd2 : 1 - ‖c‖ * (‖c‖ + ρ) ≤ ‖1 - star c * w‖ := by
    have h2 : ‖star c * w‖ ≤ ‖c‖ * (‖c‖ + ρ) := by
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left hwn (norm_nonneg c)
    have h3 : (1 : ℝ) - ‖star c * w‖ ≤ ‖1 - star c * w‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) (star c * w)
    linarith
  have hd1pos : 0 < ‖1 - star (f c) * f w‖ := by
    have h2 : ‖star (f c) * f w‖ ≤ ‖f c‖ := by
      rw [norm_mul, norm_star]
      calc ‖f c‖ * ‖f w‖ ≤ ‖f c‖ * 1 := mul_le_mul_of_nonneg_left hfw1 (norm_nonneg _)
        _ = ‖f c‖ := by ring
    have h3 : (1 : ℝ) - ‖star (f c) * f w‖ ≤ ‖1 - star (f c) * f w‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) (star (f c) * f w)
    linarith
  have hnum : ‖1 - star (f c) * f w‖ ≤ (1 - ‖f c‖ ^ 2) + ‖f c‖ * ‖f w - f c‖ :=
    norm_one_sub_star_mul_le (le_of_lt hflt)
  have hgd : DifferentiableOn ℂ f (ball (0 : ℂ) 1) :=
    fun z hz => (hf z (mem_ball_zero_iff.mp hz)).differentiableWithinAt
  have hgm : Set.MapsTo f (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := fun z hz => by
    rw [mem_closedBall_zero_iff]
    exact hmap z (le_of_lt (mem_ball_zero_iff.mp hz))
  have hspick := spick_dist hgd hgm hc1 hw1 hflt
  have h1 : ‖f w - f c‖ / ‖1 - star (f c) * f w‖ ≤ ρ / (1 - ‖c‖ * (‖c‖ + ρ)) :=
    hspick.trans (div_le_div₀ hρ hw hA hd2)
  have h2 : ‖f w - f c‖ ≤ (ρ / (1 - ‖c‖ * (‖c‖ + ρ))) * ‖1 - star (f c) * f w‖ := by
    have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (1 - star (f c) * f w))
    rwa [div_mul_cancel₀ _ (ne_of_gt hd1pos)] at h4
  have h3 : ‖f w - f c‖ * (1 - ‖c‖ * (‖c‖ + ρ)) ≤ ρ * ‖1 - star (f c) * f w‖ := by
    have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt hA)
    have h5 : ((ρ / (1 - ‖c‖ * (‖c‖ + ρ))) * ‖1 - star (f c) * f w‖)
        * (1 - ‖c‖ * (‖c‖ + ρ)) = ρ * ‖1 - star (f c) * f w‖ := by
      rw [mul_assoc, mul_comm ‖1 - star (f c) * f w‖ (1 - ‖c‖ * (‖c‖ + ρ)), ← mul_assoc,
        div_mul_cancel₀ ρ (ne_of_gt hA)]
    rwa [h5] at h4
  have h6 : ρ * ‖1 - star (f c) * f w‖
      ≤ ρ * ((1 - ‖f c‖ ^ 2) + ‖f c‖ * ‖f w - f c‖) := mul_le_mul_of_nonneg_left hnum hρ
  have h7 : ‖f w - f c‖ * (1 - ‖c‖ * (‖c‖ + ρ) - ρ * ‖f c‖) ≤ (1 - ‖f c‖ ^ 2) * ρ := by
    nlinarith [h3.trans h6]
  have h8 : 0 < 1 - ‖c‖ * (‖c‖ + ρ) - ρ * ‖f c‖ := by
    have hb : ρ * ‖f c‖ ≤ ρ := by nlinarith [hflt.le, hρ]
    have hcc : ‖c‖ * (‖c‖ + ρ) ≤ ‖c‖ := by nlinarith [norm_nonneg c, hd]
    have : 0 < 1 - ‖c‖ - ρ := by linarith
    linarith
  exact (le_div_iff₀ h8).mpr h7

/-- **Sharp disc bound for a self-map of the unit disc** (pseudohyperbolic form).  If `f` is
holomorphic on the unit disc with `‖f z‖ ≤ 1` for `‖z‖ ≤ 1`, and `‖w - c‖ ≤ ρ` with
`‖c‖ + ρ < 1`, then
`‖f w - f c‖ ≤ ρ (1 - ‖f c‖²) / (1 - ‖c‖(‖c‖ + ρ) - ρ ‖f c‖)`.
This is the Schwarz–Pick *distance* inequality combined with the triangle inequality
`‖1 - conj(f c) f w‖ ≤ (1 - ‖f c‖²) + ‖f c‖ ‖f w - f c‖`; it is the replacement of
`Work.ANum.disc_selfmap_bound` used by the radius recursion of the Theorem-A certificate (whose
Cauchy constant `2/(1-‖c‖-ρ)²` is ~170× too large at the intermediate points of the contour,
where `1 - ‖c‖ = 0.018`). -/
theorem disc_selfmap_bound_hyper {f : ℂ → ℂ} {c w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hd : ‖c‖ + ρ < 1)
    (hf : ∀ z : ℂ, ‖z‖ < 1 → DifferentiableAt ℂ f z) (hmap : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1)
    (hw : ‖w - c‖ ≤ ρ) :
    ‖f w - f c‖ ≤ (1 - ‖f c‖ ^ 2) * ρ / (1 - ‖c‖ * (‖c‖ + ρ) - ρ * ‖f c‖) := by
  have hc1 : ‖c‖ < 1 := by linarith
  have hwn : ‖w‖ ≤ ‖c‖ + ρ := by
    calc ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ρ := by linarith
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hwn hd
  have hfc_le : ‖f c‖ ≤ 1 := hmap c (le_of_lt hc1)
  rcases lt_or_eq_of_le hfc_le with hlt | heq
  · exact disc_selfmap_bound_hyper_lt hρ hd hf hmap hw hlt
  · -- degenerate case `‖f c‖ = 1`: the maximum modulus principle forces `f` to be constant
    have hd0 : DifferentiableOn ℂ f (ball (0 : ℂ) 1) :=
      fun z hz => (hf z (mem_ball_zero_iff.mp hz)).differentiableWithinAt
    have hcmem : c ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; exact hc1
    have hmax : IsMaxOn (norm ∘ f) (ball (0 : ℂ) 1) c := by
      intro y hy
      simp only [Function.comp_apply]
      rw [heq]
      exact hmap y (le_of_lt (mem_ball_zero_iff.mp hy))
    have hconst := Complex.eq_const_of_exists_max (b := 1) hd0 hcmem hmax
    have hwmem : w ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; exact hw1
    have hfw : f w = f c := hconst hwmem
    rw [hfw]
    simp [heq]

end Work.ANum
