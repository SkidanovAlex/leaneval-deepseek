import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.step_w

open Complex Work.EQ.FanSep

set_option maxHeartbeats 4000000

namespace Work.EQ

noncomputable section

/-! ## Auxiliary estimates for the backward fan step -/

/-- Parity of the reflected axis centre: if `x₁ = -1/2 + 2k` and `e = ±1`, then `-x₁ + e` is
again of the form `-1/2 + 2k'`. -/
lemma fan_centre_parity {x₁ : ℝ} {k : ℤ} (hx₁ : x₁ = -1 / 2 + 2 * k) {e : ℝ}
    (he : e = 1 ∨ e = -1) : ∃ k' : ℤ, -x₁ + e = -1 / 2 + 2 * (k' : ℝ) := by
  rcases he with rfl | rfl
  · exact ⟨1 - k, by rw [hx₁]; push_cast; ring⟩
  · exact ⟨-k, by rw [hx₁]; push_cast; ring⟩

/-- Explicit-constant (`2`) form of the first-coordinate estimate of the backward step (the
content of `Work.EQ.FanSep.step_x`, with the existential constant made explicit). -/
lemma fan_step_x2 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {s : Bool} {c : ℝ} {Q : ℂ × ℂ} {qw : ℝ}
    (hca : (1 - a) / 2 ≤ ‖((c : ℂ) + ((a / 2 : ℝ) : ℂ))‖)
    (hQ1 : ‖Q.1 - (c : ℂ)‖ ≤ (1 - a) / 8)
    (hQ2 : ‖Q.2‖ ≤ qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖) (hqw : qw ≤ 1 / 2) :
    ‖(invBranch a s Q).1 - ((((-c) + sgnB s * sgnR (c + a / 2) : ℝ)) : ℂ)‖ ≤
      ‖Q.1 - (c : ℂ)‖ + 2 * qw ^ 2 := by
  set z : ℂ := Q.1 + ((a / 2 : ℝ) : ℂ) with hz
  set w : ℂ := Q.2 with hw
  set r : ℝ := c + a / 2 with hr
  set σ : ℝ := sgnR r with hσ
  set D : ℂ := (σ : ℂ) * z with hD
  have hca' : (1 - a) / 2 ≤ |r| := by
    have h := hca
    rw [FanSep.norm_ofReal_add_eq_abs] at h
    rwa [← hr] at h
  have hz_off : ‖z - (r : ℂ)‖ ≤ (1 - a) / 8 := by
    have he : z - (r : ℂ) = Q.1 - (c : ℂ) := by rw [hz, hr]; push_cast; ring
    rw [he]; exact hQ1
  have hw_off : ‖w‖ ≤ qw * ‖z‖ := by
    rw [hw, hz]; exact hQ2
  obtain ⟨hDne, hDre, hDim, hwD_half0, hσD, hwD_qw, hwD_half⟩ :=
    FanSep.geom_bounds (a := a) (r := r) (qw := qw) (z := z) (w := w) (σ := σ) (D := D)
      ha0 ha1 hσ hD hca' hz_off hw_off hqw
  obtain ⟨-, hsqrt, hinv⟩ := FanSep.sqrt_step
  have hσsq : (σ : ℂ) * (σ : ℂ) = 1 := by
    have h : σ * σ = 1 := by rw [hσ]; exact sgnR_sq r
    rw [← Complex.ofReal_mul, h, Complex.ofReal_one]
  have hzsq : z ^ 2 = D ^ 2 := by
    rw [show z = (σ : ℂ) * D from hσD.symm, mul_pow, pow_two, hσsq, one_mul]
  have hρ_eq : (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) = D * sqHalf ((w / D) ^ 2) := by
    rw [hzsq]
    exact hsqrt hDne hDre hDim hwD_half0
  have hSne : sqHalf ((w / D) ^ 2) ≠ 0 := by
    intro h
    have h1 := hinv (w / D) hwD_half
    rw [h, inv_zero, zero_sub, norm_neg, norm_one] at h1
    have h2 : ‖w / D‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (w / D), hwD_half]
    nlinarith
  have hzdiv : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) = (σ : ℂ) * (sqHalf ((w / D) ^ 2))⁻¹ := by
    rw [hρ_eq, show z = (σ : ℂ) * D from hσD.symm]
    field_simp
  have hdiff : z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ)
      = (σ : ℂ) * ((sqHalf ((w / D) ^ 2))⁻¹ - 1) := by
    rw [hzdiv]; ring
  have hS_bound : ‖(sqHalf ((w / D) ^ 2))⁻¹ - 1‖ ≤ 2 * qw ^ 2 := by
    have h1 := hinv (w / D) hwD_half
    have h2 : ‖w / D‖ ^ 2 ≤ qw ^ 2 := by nlinarith [norm_nonneg (w / D), hwD_qw]
    linarith
  have hσn : ‖(σ : ℂ)‖ = 1 := by
    have h3 : ‖((σ : ℝ) : ℂ)‖ = |σ| := RCLike.norm_ofReal σ
    rw [h3, show |σ| = 1 from by rw [hσ]; exact abs_sgnR r]
  have hzρ : ‖z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ)‖ ≤ 2 * qw ^ 2 := by
    rw [hdiff, norm_mul, hσn, one_mul]
    exact hS_bound
  have hfst : (invBranch a s Q).1
      = -Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
    have h1 : (if s then (1 : ℂ) else -1) = (sgnB s : ℂ) := by cases s <;> simp [sgnB]
    have h2 : (-Q.1 + (if s then (1 : ℂ) else -1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) /
        ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ))
        = -Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)) := by
      rw [← hz, ← hw, h1, mul_div_assoc]
    simpa only [invBranch] using h2
  have htarget : (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)
      = -(c : ℂ) + (sgnB s : ℂ) * (σ : ℂ) := by
    rw [← hr, ← hσ]
    push_cast
    ring
  calc ‖(invBranch a s Q).1 - (((-c) + sgnB s * sgnR (c + a / 2) : ℝ) : ℂ)‖
      = ‖(-Q.1 + (sgnB s : ℂ) * (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ)))
          - (-(c : ℂ) + (sgnB s : ℂ) * (σ : ℂ))‖ := by rw [hfst, htarget]
    _ = ‖((c : ℂ) - Q.1) + (sgnB s : ℂ) *
          (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ))‖ := by
          congr 1; ring
    _ ≤ ‖(c : ℂ) - Q.1‖ + ‖(sgnB s : ℂ) *
          (z / (z ^ 2 + w ^ 2) ^ (1 / 2 : ℂ) - (σ : ℂ))‖ := norm_add_le _ _
    _ ≤ ‖Q.1 - (c : ℂ)‖ + 2 * qw ^ 2 := by
          have hs : ‖(sgnB s : ℂ)‖ = 1 := by
            have h3 : ‖((sgnB s : ℝ) : ℂ)‖ = |sgnB s| := RCLike.norm_ofReal (sgnB s)
            rw [h3, abs_sgnB s]
          rw [norm_mul, hs, one_mul, norm_sub_rev (c : ℂ) Q.1]
          linarith [hzρ]

/-- Axis arithmetic for an axis centre `x₁ = -1/2 + 2k`: with `b = a/2`, `g = (1-a)/2` and
`λ = eqLam a` one has `x₁ + b = 2k - g`, `g ≤ |x₁ + b|`, `x₁ + b ≠ 0`, the sharp non-resonance
`|x₁ + b| = g ∨ 2 - g ≤ |x₁ + b|`, `g ≤ |x₁ - b|`, and the extreme property
`λ|x₁ - b| ≤ |x₁ + b|`. -/
lemma fan_axis_facts {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x₁ : ℝ} {k : ℤ}
    (hx₁ : x₁ = -1 / 2 + 2 * k) :
    x₁ + a / 2 = 2 * (k : ℝ) - (1 - a) / 2 ∧
    (1 - a) / 2 ≤ |x₁ + a / 2| ∧ x₁ + a / 2 ≠ 0 ∧
    (|x₁ + a / 2| = (1 - a) / 2 ∨ 2 - (1 - a) / 2 ≤ |x₁ + a / 2|) ∧
    (1 - a) / 2 ≤ |x₁ - a / 2| ∧
    eqLam a * |x₁ - a / 2| ≤ |x₁ + a / 2| := by
  have hg0 : 0 < (1 - a) / 2 := by linarith
  obtain ⟨hcn1, hcn2⟩ := FanSep.centre_numbers ha0 ha1
  have heq : ((-1 / 2 + 2 * (k : ℝ) : ℝ)) = x₁ := by rw [hx₁]
  have hA : (1 - a) / 2 ≤ |x₁ + a / 2| := by
    have h := (hcn1 k).1
    rw [FanSep.norm_ofReal_add_eq_abs, heq] at h
    exact h
  have hB : (1 - a) / 2 ≤ |x₁ - a / 2| := by
    have h := (hcn1 k).2
    rw [FanSep.norm_ofReal_sub_eq_abs, heq] at h
    exact h
  have hC : eqLam a * |x₁ - a / 2| ≤ |x₁ + a / 2| := by
    have h := hcn2 k
    rw [FanSep.norm_ofReal_sub_eq_abs, FanSep.norm_ofReal_add_eq_abs, heq] at h
    exact h
  have hX : x₁ + a / 2 = 2 * (k : ℝ) - (1 - a) / 2 := by rw [hx₁]; push_cast; ring
  refine ⟨hX, hA, ?_, ?_, hB, hC⟩
  · intro h; rw [h] at hA; linarith
  · rcases eq_or_ne k 0 with hk | hk
    · left
      have hk0 : (k : ℝ) = 0 := by rw [hk]; norm_num
      have hh : x₁ + a / 2 = -((1 - a) / 2) := by rw [hX, hk0]; ring
      rw [hh, abs_neg, abs_of_pos hg0]
    · right
      have h2k : (2 : ℝ) ≤ |2 * (k : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
        have h3 : (1 : ℝ) ≤ |((k : ℤ) : ℝ)| := by exact_mod_cast h1
        have h4 : |2 * (k : ℝ)| = 2 * |(k : ℝ)| := by rw [abs_mul]; norm_num
        rw [h4]; linarith
      have hge : (2 : ℝ) - (1 - a) / 2 ≤ |2 * (k : ℝ) - (1 - a) / 2| := by
        have h5 := abs_sub_abs_le_abs_sub (2 * (k : ℝ)) ((1 - a) / 2)
        rw [abs_of_pos hg0] at h5
        linarith
      rw [hX]; exact hge

/-- Signed axis arithmetic: for `K = ±1` and an axis abscissa `X₀ = x₁ + a/2` with `|X₀| = g` or
`|X₀| ≥ 2 - g` (`g = (1-a)/2`), one has `|K - X₀| ≥ 1 - g` and `|a + K - X₀| ≥ g`. -/
lemma fan_signed_axis {a K X₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hK : K = 1 ∨ K = -1)
    (hg : |X₀| = (1 - a) / 2 ∨ 2 - (1 - a) / 2 ≤ |X₀|) :
    1 - (1 - a) / 2 ≤ |K - X₀| ∧ (1 - a) / 2 ≤ |a + K - X₀| := by
  have hg0 : 0 < (1 - a) / 2 := by linarith
  have hgh : (1 - a) / 2 ≤ 1 / 2 := by linarith
  have hKabs : |K| = 1 := by rcases hK with h | h <;> rw [h] <;> norm_num
  have hbig : 1 - (1 - a) / 2 ≤ abs (|X₀| - 1) := by
    rcases hg with h | h
    · rw [h]
      rw [show (1 - a) / 2 - 1 = -(1 - (1 - a) / 2) from by ring, abs_neg,
        abs_of_pos (by linarith)]
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ |X₀| - 1)]
      linarith
  constructor
  · have h1 : abs (|X₀| - 1) ≤ |K - X₀| := by
      have h := abs_abs_sub_abs_le_abs_sub X₀ K
      rw [hKabs] at h
      rw [abs_sub_comm X₀ K] at h
      exact h
    linarith
  · rcases hK with rfl | rfl
    · have h4 : |a + 1 - X₀| = |X₀ - (1 + a)| := by rw [abs_sub_comm]; ring_nf
      have h1 : abs (|X₀| - (1 + a)) ≤ |X₀ - (1 + a)| := by
        have h := abs_abs_sub_abs_le_abs_sub X₀ (1 + a)
        rwa [abs_of_pos (by linarith : (0 : ℝ) < 1 + a)] at h
      have h3 : (1 - a) / 2 ≤ abs (|X₀| - (1 + a)) := by
        rcases hg with h | h
        · rw [h]
          rw [show (1 - a) / 2 - (1 + a) = -(1 + a - (1 - a) / 2) from by ring, abs_neg,
            abs_of_pos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ |X₀| - (1 + a))]
          linarith
      rw [h4]; linarith
    · have h4 : |a + -1 - X₀| = |X₀ - (a - 1)| := by rw [abs_sub_comm]; ring_nf
      have h1 : abs (|X₀| - (1 - a)) ≤ |X₀ - (a - 1)| := by
        have h := abs_abs_sub_abs_le_abs_sub X₀ (a - 1)
        rw [abs_of_neg (by linarith : a - 1 < 0)] at h
        rw [show -(a - 1) = 1 - a from by ring] at h
        exact h
      have h3 : (1 - a) / 2 ≤ abs (|X₀| - (1 - a)) := by
        rcases hg with h | h
        · rw [h]
          rw [show (1 - a) / 2 - (1 - a) = -((1 - a) / 2) from by ring, abs_neg,
            abs_of_pos hg0]
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ |X₀| - (1 - a))]
          linarith
      rw [h4]; linarith

/-- The semi-projective factor of a point `Q` near an axis centre is at most
`(1/λ)(1 + 8ρ/g)`: from the extreme property `λ|x₁ - b| ≤ |x₁ + b|` and `ρ ≤ g/16` one has
`|Q.1 - b| ≤ |x₁ - b| + ρ` and `|Q.1 + b| ≥ |x₁ + b| - ρ`, and
`λ(|x₁ - b| + ρ) ≤ |x₁ + b| + λρ ≤ (|x₁ + b| - ρ)(1 + 8ρ/g)`. -/
lemma fan_ratio_factor' {a ρ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x₁ : ℝ} {k : ℤ}
    (hx₁ : x₁ = -1 / 2 + 2 * k) (hρ0 : 0 ≤ ρ) (hρg : ρ ≤ (1 - a) / 16) {Q : ℂ × ℂ}
    (hQx : ‖Q.1 - (x₁ : ℂ)‖ ≤ ρ) :
    ‖(Q.1 - ((a / 2 : ℝ) : ℂ)) / (Q.1 + ((a / 2 : ℝ) : ℂ))‖ ≤
      (1 / eqLam a) * (1 + 8 * ρ / ((1 - a) / 2)) := by
  set g : ℝ := (1 - a) / 2 with hgdef
  have hg0 : 0 < g := by rw [hgdef]; linarith
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  obtain ⟨-, hX0ge, -, -, -, hxbext⟩ := fan_axis_facts ha0 ha1 hx₁
  have hX0ge' : g ≤ |x₁ + a / 2| := by rw [hgdef]; exact hX0ge
  have hρX0 : ρ ≤ |x₁ + a / 2| / 8 := by linarith [hX0ge', hρg, hgdef]
  have hnum : ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ |x₁ - a / 2| + ρ := by
    have h : Q.1 - ((a / 2 : ℝ) : ℂ)
        = (Q.1 - (x₁ : ℂ)) + ((x₁ : ℂ) - ((a / 2 : ℝ) : ℂ)) := by ring
    calc ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖
        = ‖(Q.1 - (x₁ : ℂ)) + ((x₁ : ℂ) - ((a / 2 : ℝ) : ℂ))‖ := by rw [h]
      _ ≤ ‖Q.1 - (x₁ : ℂ)‖ + ‖(x₁ : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖Q.1 - (x₁ : ℂ)‖ + |x₁ - a / 2| := by rw [FanSep.norm_ofReal_sub_eq_abs]
      _ ≤ ρ + |x₁ - a / 2| := by linarith [hQx]
      _ = |x₁ - a / 2| + ρ := by ring
  have hden : |x₁ + a / 2| - ρ ≤ ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    have he : (x₁ : ℂ) + ((a / 2 : ℝ) : ℂ)
        = (Q.1 + ((a / 2 : ℝ) : ℂ)) - (Q.1 - (x₁ : ℂ)) := by ring
    have h := norm_sub_le (Q.1 + ((a / 2 : ℝ) : ℂ)) (Q.1 - (x₁ : ℂ))
    rw [← he, FanSep.norm_ofReal_add_eq_abs] at h
    linarith [h, hQx]
  have hkey : eqLam a * (|x₁ - a / 2| + ρ) ≤ (1 + 8 * ρ / g) * (|x₁ + a / 2| - ρ) := by
    have h1 : eqLam a * (|x₁ - a / 2| + ρ) ≤ |x₁ + a / 2| + eqLam a * ρ := by
      have h := mul_add (eqLam a) |x₁ - a / 2| ρ
      linarith [h, hxbext]
    have h2 : (1 + 8 * ρ / g) * (|x₁ + a / 2| - ρ)
        = |x₁ + a / 2| + 8 * ρ * |x₁ + a / 2| / g - ρ - 8 * ρ ^ 2 / g := by
      field_simp; ring
    have h4 : 8 * ρ ^ 2 / g ≤ ρ := by
      rw [div_le_iff₀ hg0]
      have h7 : 8 * ρ ≤ g := by
        have h8 : ρ ≤ g / 8 := by rw [hgdef]; linarith [hρg]
        linarith
      nlinarith [hρ0, h7]
    have h5 : 8 * ρ ≤ 8 * ρ * |x₁ + a / 2| / g := by
      rw [le_div_iff₀ hg0]
      nlinarith [hX0ge', hρ0]
    have h6 : eqLam a * ρ ≤ 6 * ρ := by nlinarith [hlam1, hρ0]
    rw [h2]; linarith
  rcases eq_or_ne (Q.1 + ((a / 2 : ℝ) : ℂ)) 0 with hzero | hne
  · rw [hzero, div_zero, norm_zero]; positivity
  · rw [norm_div]
    have hpos : 0 < ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := norm_pos_iff.mpr hne
    rw [div_le_iff₀ hpos]
    have h2 : |x₁ - a / 2| + ρ ≤ (1 / eqLam a) * (1 + 8 * ρ / g)
        * (|x₁ + a / 2| - ρ) := by
      rw [show (1 / eqLam a) * (1 + 8 * ρ / g) * (|x₁ + a / 2| - ρ)
          = ((1 + 8 * ρ / g) * (|x₁ + a / 2| - ρ)) / eqLam a by ring]
      rw [le_div_iff₀ hlam0]
      linarith [hkey]
    have h3 : (1 / eqLam a) * (1 + 8 * ρ / g) * (|x₁ + a / 2| - ρ)
        ≤ (1 / eqLam a) * (1 + 8 * ρ / g) * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by
      have hfac : 0 ≤ (1 / eqLam a) * (1 + 8 * ρ / g) := by positivity
      exact mul_le_mul_of_nonneg_left hden hfac
    linarith [hnum, h2, h3]

/-- Positivity of the radicand `(P.1 + a/2)^2 + P.2^2` at the point reached after one backward
step: for `P` near an axis centre `c = -1/2 + 2ℤ` with `‖P.1 - c‖ ≤ ρ' ≤ |c + a/2|/4` and
`‖P.2/(P.1 - a/2)‖ ≤ τ' ≤ λ/4`. -/
lemma fan_radicand_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c ρ τ : ℝ} {P : ℂ × ℂ}
    (hc : ∃ k : ℤ, c = -1 / 2 + 2 * (k : ℝ))
    (hρ0 : 0 ≤ ρ) (hτ0 : 0 ≤ τ) (hρs : ρ ≤ |c + a / 2| / 4) (hτl : τ ≤ eqLam a / 4)
    (hPx : ‖P.1 - (c : ℂ)‖ ≤ ρ) (hPb : P.1 - ((a / 2 : ℝ) : ℂ) ≠ 0)
    (hPw : ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ τ) :
    0 < (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨hcn1, hcn2⟩ := FanSep.centre_numbers ha0 ha1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set X : ℝ := -1 / 2 + 2 * (k : ℝ) with hXdef
  set s : ℝ := |X + a / 2| with hsdef
  have hsg : (1 - a) / 2 ≤ s := by
    have h := (hcn1 k).1
    rw [FanSep.norm_ofReal_add_eq_abs] at h
    rw [hsdef, hXdef]; linarith
  have hs0 : 0 < s := by linarith
  have hratio : |X - a / 2| * eqLam a ≤ s := by
    have h := hcn2 k
    rw [FanSep.norm_ofReal_sub_eq_abs, FanSep.norm_ofReal_add_eq_abs] at h
    rw [hsdef, hXdef]; linarith
  have hcd : |X - a / 2| ≤ s / eqLam a := by
    rw [le_div_iff₀ hlam0]; linarith [hratio]
  have hPb' : P.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := hPb
  have hPxc : ‖P.1 - (X : ℂ)‖ ≤ ρ := hPx
  have hP1 : ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ ≤ ρ + s / eqLam a := by
    have hsplit : P.1 - ((a / 2 : ℝ) : ℂ)
        = (P.1 - (X : ℂ)) + ((X : ℂ) - ((a / 2 : ℝ) : ℂ)) := by ring
    have h1 : ‖(P.1 - (X : ℂ)) + ((X : ℂ) - ((a / 2 : ℝ) : ℂ))‖
        ≤ ‖P.1 - (X : ℂ)‖ + |X - a / 2| := by
      have h1' := norm_add_le (P.1 - (X : ℂ)) ((X : ℂ) - ((a / 2 : ℝ) : ℂ))
      rwa [FanSep.norm_ofReal_sub_eq_abs] at h1'
    rw [hsplit]
    linarith [h1, hPxc, hcd]
  have hP2 : ‖P.2‖ ≤ τ * (ρ + s / eqLam a) := by
    have hdecomp : ‖P.2‖ = ‖P.2 / (P.1 - ((a / 2 : ℝ) : ℂ))‖ * ‖P.1 - ((a / 2 : ℝ) : ℂ)‖ := by
      rw [norm_div]; field_simp
    rw [hdecomp]
    exact mul_le_mul hPw hP1 (norm_nonneg _) hτ0
  have hρs' : ρ ≤ s / 4 := hρs
  have hP2' : ‖P.2‖ ≤ s * (5 / 16) := by
    have h3 : ‖P.2‖ ≤ τ * ρ + τ * (s / eqLam a) := by
      have he : τ * (ρ + s / eqLam a) = τ * ρ + τ * (s / eqLam a) := by ring
      linarith [hP2]
    have ha : τ * ρ ≤ s * (1 / 16) := by
      have h1 : τ * ρ ≤ (eqLam a / 4) * (s / 4) :=
        mul_le_mul hτl hρs' hρ0 (by positivity)
      have h2 : (eqLam a / 4) * (s / 4) = eqLam a * s / 16 := by ring
      have h4 : eqLam a * s / 16 ≤ s / 16 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 16)]
        nlinarith [hs0, hlam1, hlam0]
      linarith [h1, h2, h4]
    have hb : τ * (s / eqLam a) ≤ s * (1 / 4) := by
      have h1 : τ * (s / eqLam a) ≤ (eqLam a / 4) * (s / eqLam a) :=
        mul_le_mul_of_nonneg_right hτl (by positivity)
      have h2 : (eqLam a / 4) * (s / eqLam a) = s / 4 := by field_simp
      linarith [h1, h2]
    have h5 : s * (1 / 16) + s * (1 / 4) = s * (5 / 16) := by ring
    linarith [h3, ha, hb, h5]
  have him : |P.1.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (P.1 - (X : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    linarith [h, hPxc]
  have hredev : |P.1.re - X| ≤ ρ := by
    have h := Complex.abs_re_le_norm (P.1 - (X : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h
    linarith [h, hPxc]
  have hre : (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re
      = ((P.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 - (P.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2)
        + (P.2.re ^ 2 - P.2.im ^ 2) := by
    rw [Complex.add_re, pow_two, pow_two, Complex.mul_re, Complex.mul_re]; ring
  have hrez : (P.1 + ((a / 2 : ℝ) : ℂ)).re = X + a / 2 + (P.1.re - X) := by
    simp only [Complex.add_re, Complex.ofReal_re]; rw [hXdef]; ring
  have hreim : (P.1 + ((a / 2 : ℝ) : ℂ)).im = P.1.im := by
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  have hAre : (s - ρ) ^ 2 ≤ (P.1 + ((a / 2 : ℝ) : ℂ)).re ^ 2 := by
    rw [hrez]
    have h2 : s - ρ ≤ |X + a / 2 + (P.1.re - X)| := by
      have h4 : |X + a / 2| - |P.1.re - X| ≤ |X + a / 2 + (P.1.re - X)| := by
        have h5 := abs_sub_abs_le_abs_sub (X + a / 2) (-(P.1.re - X))
        rw [abs_neg] at h5
        have h7 : X + a / 2 - -(P.1.re - X) = X + a / 2 + (P.1.re - X) := by ring
        rwa [h7] at h5
      have h6 : |X + a / 2| = s := hsdef.symm
      linarith [h4, hredev, h6]
    have h5 : 0 ≤ s - ρ := by linarith [hρs', hs0]
    calc (s - ρ) ^ 2 ≤ |X + a / 2 + (P.1.re - X)| ^ 2 := pow_le_pow_left₀ h5 h2 2
      _ = (X + a / 2 + (P.1.re - X)) ^ 2 := sq_abs _
  have hBim : (P.1 + ((a / 2 : ℝ) : ℂ)).im ^ 2 ≤ ρ ^ 2 := by
    rw [hreim]
    have h := abs_le.mp him
    nlinarith [h.1, h.2]
  have hCim : P.2.re ^ 2 - P.2.im ^ 2 ≥ -‖P.2‖ ^ 2 := by
    have h4 : P.2.im ^ 2 ≤ ‖P.2‖ ^ 2 := by
      have h5 : |P.2.im| ≤ ‖P.2‖ := Complex.abs_im_le_norm P.2
      nlinarith [abs_nonneg P.2.im, h5, sq_abs P.2.im]
    nlinarith [sq_nonneg P.2.re, h4]
  have hmain : (((P.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2)).re
      ≥ (s - ρ) ^ 2 - ρ ^ 2 - ‖P.2‖ ^ 2 := by
    rw [hre]; linarith [hAre, hBim, hCim]
  have hfinal : (s - ρ) ^ 2 - ρ ^ 2 - ‖P.2‖ ^ 2 > 0 := by
    have h2 : ‖P.2‖ ^ 2 ≤ (s * (5 / 16)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hP2' 2
    nlinarith [hρs', h2, hs0]
  linarith [hmain, hfinal]

/-- **The backward step of the stable fan** (Rychlik Thm 7(1)/Lemma 14: the analytic core of the
uniform fan estimates).  The small quantity is the *semi-projective coordinate at `O₂`* of the
child, `|Q.2/(Q.1 - b)| ≤ τ`.

Notation: `b = a/2`, `λ = eqLam a = (1-a)/(1+a)`, `g = (1-a)/2`.  Let `x₁ = -1/2 + 2k` be an axis
centre and `Q : ℂ × ℂ` a point with `‖Q.1 - x₁‖ ≤ ρ`, `Q.1 - b ≠ 0`, `‖Q.2/(Q.1 - b)‖ ≤ τ`, where
`ρ ≤ g/16`, `τ ≤ g/16` and `τ ≤ λ²/8`.

Then `P = invBranch a s Q` satisfies:
* its abscissa is within `ρ + 64(ρ² + τ²)/(λ²g²)` of the new centre `-x₁ + εs·sgn (x₁ + b)`
  (`εs = ±1` according to `s`; note `x₁ + b` is real and nonzero);
* its semi-projective coordinate at `O₂` is at most `τ/λ · (1 + 8ρ/g)`;
* `P.1 ± b ≠ 0` and `0 < ((P.1 + b)^2 + P.2^2).re`. -/
theorem fan_invBranch_step {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {s : Bool} {x₁ ρ τ : ℝ} {k : ℤ}
    (hx₁ : x₁ = -1 / 2 + 2 * k) (hρ0 : 0 ≤ ρ) (hτ0 : 0 ≤ τ)
    (hρg : ρ ≤ (1 - a) / 16) (hτg : τ ≤ (1 - a) / 16) (hτl : τ ≤ eqLam a ^ 2 / 8)
    {Q : ℂ × ℂ} (hQx : ‖Q.1 - (x₁ : ℂ)‖ ≤ ρ) (hQb : Q.1 - (a / 2 : ℂ) ≠ 0)
    (hQw : ‖Q.2 / (Q.1 - (a / 2 : ℂ))‖ ≤ τ) :
    ‖(invBranch a s Q).1 -
        ((((-x₁ + (if s then (1 : ℝ) else -1) * (if 0 < x₁ + a / 2 then (1 : ℝ) else -1)) : ℝ)) : ℂ)‖
        ≤ ρ + 64 * (ρ ^ 2 + τ ^ 2) / (eqLam a ^ 2 * ((1 - a) / 2) ^ 2) ∧
      ‖(invBranch a s Q).2 / ((invBranch a s Q).1 - (a / 2 : ℂ))‖ ≤
        (1 / eqLam a) * τ * (1 + 8 * ρ / ((1 - a) / 2)) ∧
      (invBranch a s Q).1 + (a / 2 : ℂ) ≠ 0 ∧ (invBranch a s Q).1 - (a / 2 : ℂ) ≠ 0 ∧
      0 < (((invBranch a s Q).1 + (a / 2 : ℂ)) ^ 2 + (invBranch a s Q).2 ^ 2).re := by
  have hbc : ((a / 2 : ℝ) : ℂ) = (a / 2 : ℂ) := by push_cast; ring
  set g : ℝ := (1 - a) / 2 with hgdef
  have hg0 : 0 < g := by rw [hgdef]; linarith
  have hgh : g ≤ 1 / 2 := by rw [hgdef]; linarith
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hρg' : ρ ≤ g / 8 := by linarith [hρg, hgdef]
  have hτg' : τ ≤ g / 8 := by linarith [hτg, hgdef]
  obtain ⟨hX0eq, hX0ge, hX0ne, hX0cases, hx1bge, hxbext⟩ := fan_axis_facts ha0 ha1 hx₁
  have hX0ge' : g ≤ |x₁ + a / 2| := by rw [hgdef]; exact hX0ge
  have hX0cases' : |x₁ + a / 2| = g ∨ 2 - g ≤ |x₁ + a / 2| := by
    rcases hX0cases with h | h
    · exact Or.inl (by rw [hgdef]; exact h)
    · exact Or.inr (by rw [hgdef]; exact h)
  set qw : ℝ := (1 / eqLam a) * τ * (1 + 8 * ρ / g) with hqwdef
  have hqw0 : 0 ≤ qw := by rw [hqwdef]; positivity
  have hq1 : qw ≤ 2 * τ / eqLam a := by
    rw [hqwdef]
    have h2 : 1 + 8 * ρ / g ≤ 2 := by
      have h2a : 8 * ρ / g ≤ 1 := by rw [div_le_iff₀ hg0]; linarith [hρg', hg0]
      linarith [h2a]
    rw [show 2 * τ / eqLam a = (1 / eqLam a) * τ * 2 by ring]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hq1' : qw * eqLam a ≤ 2 * τ := by
    have h := mul_le_mul_of_nonneg_right hq1 (le_of_lt hlam0)
    rw [div_mul_cancel₀ _ (ne_of_gt hlam0)] at h
    linarith [h]
  have hqw_le : qw ≤ eqLam a / 4 := by
    have h3 : 2 * τ / eqLam a ≤ eqLam a / 4 := by
      rw [div_le_iff₀ hlam0]
      have h4 : 2 * τ ≤ eqLam a ^ 2 / 4 := by linarith [hτl]
      have h5 : eqLam a ^ 2 / 4 = eqLam a / 4 * eqLam a := by ring
      linarith [h4, h5]
    linarith [hq1, h3]
  have hqw_half : qw ≤ 1 / 2 := by linarith [hqw_le, hlam0, hlam1]
  have hqw_sq : 2 * qw ^ 2 ≤ g / 8 := by
    have h6 : 2 * qw ^ 2 * eqLam a ^ 2 ≤ 8 * τ ^ 2 := by
      have h8 : (qw * eqLam a) ^ 2 ≤ (2 * τ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hq1' 2
      nlinarith [h8]
    have hτmin : τ ≤ min (g / 8) (eqLam a ^ 2 / 8) := le_min hτg' hτl
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    rcases le_or_gt (g / 8) (eqLam a ^ 2 / 8) with h8 | h8
    · have h9 : τ ≤ g / 8 := le_trans hτmin (min_le_left _ _)
      have h10 : g ≤ eqLam a ^ 2 := by linarith [h8, hg0]
      nlinarith [h6, h9, hτ0, h10, hg0, hlam0]
    · have h9 : τ ≤ eqLam a ^ 2 / 8 := le_trans hτmin (min_le_right _ _)
      have h10 : eqLam a ^ 2 ≤ g := by linarith [h8]
      nlinarith [h6, h9, hτ0, h10, hg0, hlam0]
  have hsmall : ρ + 2 * qw ^ 2 < g := by linarith [hρg', hqw_sq, hg0]
  have hρ4 : ρ + 2 * qw ^ 2 ≤ g / 4 := by linarith [hρg', hqw_sq]
  set K : ℝ := sgnB s * sgnR (x₁ + a / 2) with hKdef
  have hKcases : K = 1 ∨ K = -1 := by
    rcases sgnB_cases s with h1 | h1 <;> rcases sgnR_cases (x₁ + a / 2) with h2 | h2 <;>
      rw [hKdef, h1, h2] <;> norm_num
  obtain ⟨hMK, hMKa⟩ := fan_signed_axis ha0 ha1 (K := K) (X₀ := x₁ + a / 2) hKcases hX0cases'
  set C : ℝ := -x₁ + K with hCdef
  have hCeq : C = -x₁ + (if s then (1 : ℝ) else -1)
      * (if 0 < x₁ + a / 2 then (1 : ℝ) else -1) := by
    rw [hCdef, hKdef]; simp only [sgnB, sgnR]
  have hCsub : C - a / 2 = K - (x₁ + a / 2) := by rw [hCdef]; ring
  have hCadd : C + a / 2 = a + K - (x₁ + a / 2) := by rw [hCdef]; ring
  have hCb : g ≤ |C + a / 2| := by rw [hCadd]; exact hMKa
  have hCmb : 1 - g ≤ |C - a / 2| := by rw [hCsub]; exact hMK
  have hXnorm : (1 - a) / 2 ≤ ‖(x₁ : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by
    rw [FanSep.norm_ofReal_add_eq_abs]; exact hX0ge
  have hQden : Q.1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hz
    have h1 : ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ = 0 := by rw [hz, norm_zero]
    have h2 : |x₁ + a / 2| ≤ ‖Q.1 - (x₁ : ℂ)‖ := by
      have h3 := norm_sub_le (Q.1 + ((a / 2 : ℝ) : ℂ)) (Q.1 - (x₁ : ℂ))
      have he : (x₁ : ℂ) + ((a / 2 : ℝ) : ℂ)
          = (Q.1 + ((a / 2 : ℝ) : ℂ)) - (Q.1 - (x₁ : ℂ)) := by ring
      rw [← he, FanSep.norm_ofReal_add_eq_abs] at h3
      rw [h1, zero_add] at h3
      exact h3
    linarith [h2, hQx, hX0ge', hg0]
  have hQ2bound : ‖Q.2‖ ≤ qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by
    have hratio := fan_ratio_factor' ha0 ha1 hx₁ hρ0 hρg hQx
    rw [← hgdef] at hratio
    have hQb' : Q.1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by rw [hbc]; exact hQb
    have hQw' : ‖Q.2 / (Q.1 - ((a / 2 : ℝ) : ℂ))‖ ≤ τ := by rw [hbc]; exact hQw
    have h1 : ‖Q.2‖ = ‖Q.2 / (Q.1 - ((a / 2 : ℝ) : ℂ))‖ * ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖ := by
      rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hQb')]
    have h2 : ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖
        = ‖(Q.1 - ((a / 2 : ℝ) : ℂ)) / (Q.1 + ((a / 2 : ℝ) : ℂ))‖
          * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by
      rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hQden)]
    calc ‖Q.2‖ = ‖Q.2 / (Q.1 - ((a / 2 : ℝ) : ℂ))‖ * ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖ := h1
      _ ≤ τ * ‖Q.1 - ((a / 2 : ℝ) : ℂ)‖ := mul_le_mul_of_nonneg_right hQw' (norm_nonneg _)
      _ = τ * (‖(Q.1 - ((a / 2 : ℝ) : ℂ)) / (Q.1 + ((a / 2 : ℝ) : ℂ))‖
            * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖) := by rw [h2]
      _ ≤ τ * (((1 / eqLam a) * (1 + 8 * ρ / g)) * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hratio (norm_nonneg _)) hτ0
      _ = qw * ‖Q.1 + ((a / 2 : ℝ) : ℂ)‖ := by rw [hqwdef]; ring
  have hpx0 := fan_step_x2 ha0 ha1 (s := s) (c := x₁) (Q := Q) (qw := qw) hXnorm
      (by linarith [hQx, hρg]) hQ2bound hqw_half
  have hpx : ‖(invBranch a s Q).1 - ((C : ℝ) : ℂ)‖ ≤ ρ + 2 * qw ^ 2 := by
    have h1 : ((((-x₁) + sgnB s * sgnR (x₁ + a / 2) : ℝ)) : ℂ) = ((C : ℝ) : ℂ) := by
      rw [hCdef, hKdef]
    rw [h1] at hpx0
    linarith [hpx0, hQx]
  have hstepw := FanSep.step_w_first (a := a) s (Q := Q) (qw := qw) hQden hqw0 hqw_half hQ2bound
  have hPw' : ‖(invBranch a s Q).2 / ((invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ))‖ ≤ qw := by
    by_cases h : (invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ) = 0
    · rw [h, div_zero, norm_zero]; exact hqw0
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr h)]
      exact hstepw
  have hP1add' : (invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hz
    have h1 : ‖(invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ)‖ = 0 := by rw [hz, norm_zero]
    have htri : |C + a / 2| ≤ ‖(invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ)‖
        + ‖(invBranch a s Q).1 - ((C : ℝ) : ℂ)‖ := by
      have he : ((C : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)
          = ((invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ))
            - ((invBranch a s Q).1 - ((C : ℝ) : ℂ)) := by ring
      calc |C + a / 2| = ‖((C : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ)‖ := by
            rw [FanSep.norm_ofReal_add_eq_abs]
        _ = ‖((invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ))
              - ((invBranch a s Q).1 - ((C : ℝ) : ℂ))‖ := by rw [he]
        _ ≤ _ := norm_sub_le _ _
    rw [h1, zero_add] at htri
    linarith [htri, hpx, hsmall, hCb]
  have hP1sub' : (invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    intro hz
    have h1 : ‖(invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ)‖ = 0 := by rw [hz, norm_zero]
    have htri : |C - a / 2| ≤ ‖(invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ)‖
        + ‖(invBranch a s Q).1 - ((C : ℝ) : ℂ)‖ := by
      have he : ((C : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)
          = ((invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ))
            - ((invBranch a s Q).1 - ((C : ℝ) : ℂ)) := by ring
      calc |C - a / 2| = ‖((C : ℝ) : ℂ) - ((a / 2 : ℝ) : ℂ)‖ := by
            rw [FanSep.norm_ofReal_sub_eq_abs]
        _ = ‖((invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ))
              - ((invBranch a s Q).1 - ((C : ℝ) : ℂ))‖ := by rw [he]
        _ ≤ _ := norm_sub_le _ _
    rw [h1, zero_add] at htri
    linarith [htri, hpx, hsmall, hCmb, hgh]
  obtain ⟨k', hk'⟩ := fan_centre_parity hx₁ hKcases
  have hCc : C = -1 / 2 + 2 * (k' : ℝ) := by rw [hCdef]; exact hk'
  have hrad : 0 < (((invBranch a s Q).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (invBranch a s Q).2 ^ 2).re :=
    fan_radicand_pos ha0 ha1 (c := C) (ρ := ρ + 2 * qw ^ 2) (τ := qw)
      (P := invBranch a s Q) ⟨k', hCc⟩ (by positivity) hqw0
      (by linarith [hρ4, hCb]) hqw_le hpx hP1sub' hPw'
  have h2qw2 : 2 * qw ^ 2 ≤ 64 * (ρ ^ 2 + τ ^ 2) / (eqLam a ^ 2 * g ^ 2) := by
    have hA : 2 * qw ^ 2 * eqLam a ^ 2 ≤ 8 * τ ^ 2 := by
      have h8 : (qw * eqLam a) ^ 2 ≤ (2 * τ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hq1' 2
      nlinarith [h8]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < eqLam a ^ 2 * g ^ 2)]
    have h9 : 2 * qw ^ 2 * eqLam a ^ 2 * g ^ 2 ≤ 8 * τ ^ 2 * g ^ 2 := by
      have := mul_le_mul_of_nonneg_right hA (sq_nonneg g)
      linarith [this]
    have h10 : 8 * τ ^ 2 * g ^ 2 ≤ 64 * τ ^ 2 := by
      have hg2 : g ^ 2 ≤ 1 / 4 := by nlinarith [hgh, hg0]
      have h11 : 8 * τ ^ 2 * g ^ 2 ≤ 8 * τ ^ 2 * (1 / 4) :=
        mul_le_mul_of_nonneg_left hg2 (by positivity)
      nlinarith [h11, hτ0]
    nlinarith [h9, h10, sq_nonneg ρ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hCeq]
    calc ‖(invBranch a s Q).1 - ((C : ℝ) : ℂ)‖ ≤ ρ + 2 * qw ^ 2 := hpx
      _ ≤ ρ + 64 * (ρ ^ 2 + τ ^ 2) / (eqLam a ^ 2 * g ^ 2) := by linarith [h2qw2]
  · have hgoal : ‖(invBranch a s Q).2 / ((invBranch a s Q).1 - (a / 2 : ℂ))‖
        = ‖(invBranch a s Q).2 / ((invBranch a s Q).1 - ((a / 2 : ℝ) : ℂ))‖ := by rw [hbc]
    rw [hgoal]
    exact hPw'
  · rw [← hbc]
    exact hP1add'
  · rw [← hbc]
    exact hP1sub'
  · rw [← hbc]
    exact hrad

end

end Work.EQ
