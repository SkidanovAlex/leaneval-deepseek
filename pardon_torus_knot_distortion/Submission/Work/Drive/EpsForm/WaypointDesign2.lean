import Mathlib
import Submission.Work.Drive.EpsForm.WaypointDesign
import Submission.Work.Drive.EpsForm.profW_levels

/-!
# The corrected profile of the disc map (`profX`)

The original waypoint profile `profW` of `WaypointDesign.lean` had five waypoints
`W1 → W2c t → W3c t → W4 → W5c t` at levels `0 < sig1 < sig2 < tauP < 1`, where
`W4 = (0,0)` is *fixed*.  The last two pieces (levels `[sig2, tauP]` and `[tauP, 1]`)
therefore do not shrink as `t` approaches the ends `u0`, `v0` of the chord range, where
`sig1 = sig2 = tauP = 1`: the profile is discontinuous at `(u0,1)` and `(v0,1)`
(and `eFun` with it), see the review of `continuousOn_eFun2`.

The fix is to drop the fixed waypoint `W4` and use the three-waypoint profile

  `profX t s = W1 → W2c t → W3c t → W5c t`   at levels `0 → sig1 → sig2 → 1`,

whose last piece `[W3c t, W5c t]` joins two points of the unit circle and hence runs
*strictly inside* the unit circle except at its endpoints.  As `t → u0` (or `→ v0`) all
waypoints `W2c t, W3c t, W5c t` converge to the single point `W5c u0` (resp. `W5c v0`),
so the whole profile converges to the straight segment `[W1, W5c u0]`, which is exactly
`profX u0 ·`; the profile is therefore continuous on the parameter rectangle.

The interior intersection of the image with the torus is unchanged: it is still the union
of the two chords `t ↦ eFunX t (sig1 t)` and `t ↦ eFunX t (sig2 t)`, because the unit
circle is met by the profile exactly at the levels `sig1 t`, `sig2 t` and `1`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

noncomputable section

/-! ## The corrected profile -/

/-- **The corrected waypoint profile** in tube coordinates: the polyline through the four
waypoints `W1 → W2c t → W3c t → W5c t` at levels `0 ≤ sig1c t ≤ sig2c t ≤ 1`. -/
def profX (t s : ℝ) : ℝ × ℝ :=
  if s ≤ sig1c t then seg W1 (W2c t) 0 (sig1c t) s
  else if s ≤ sig2c t then seg (W2c t) (W3c t) (sig1c t) (sig2c t) s
  else seg (W3c t) (W5c t) (sig2c t) 1 s

theorem profX_br1 {t s : ℝ} (h : s ≤ sig1c t) :
    profX t s = seg W1 (W2c t) 0 (sig1c t) s := by
  unfold profX; rw [if_pos h]

theorem profX_br2 {t s : ℝ} (h1 : ¬ s ≤ sig1c t) (h2 : s ≤ sig2c t) :
    profX t s = seg (W2c t) (W3c t) (sig1c t) (sig2c t) s := by
  unfold profX; rw [if_neg h1, if_pos h2]

theorem profX_br3 {t s : ℝ} (h1 : ¬ s ≤ sig1c t) (h2 : ¬ s ≤ sig2c t) :
    profX t s = seg (W3c t) (W5c t) (sig2c t) 1 s := by
  unfold profX; rw [if_neg h1, if_neg h2]

/-! ## The corrected tube-coordinate map -/

/-- **The corrected disc map** in tube coordinates: azimuth `t`, tube coordinates
`profX t s`. -/
def eFunX (t s : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then (2 + (profX t s).1) * Real.cos t
    else if i.val = 1 then (2 + (profX t s).1) * Real.sin t
    else (profX t s).2)

/-- `eFunX` as a function of a pair. -/
def eFunX2 (p : ℝ × ℝ) : R3 := eFunX p.1 p.2

/-- **The corrected disc map** on the closed unit disc. -/
def eDiscX (z : Metric.closedBall (0 : ℂ) 1) : R3 :=
  eFunX (Complex.arg (z : ℂ)) ‖(z : ℂ)‖

theorem eFunX_apply_zero (t s : ℝ) :
    eFunX t s 0 = (2 + (profX t s).1) * Real.cos t := by
  simp only [eFunX, WithLp.ofLp_toLp]; simp

theorem eFunX_apply_one (t s : ℝ) :
    eFunX t s 1 = (2 + (profX t s).1) * Real.sin t := by
  simp only [eFunX, WithLp.ofLp_toLp]; simp

theorem eFunX_apply_two (t s : ℝ) : eFunX t s 2 = (profX t s).2 := by
  simp only [eFunX, WithLp.ofLp_toLp]; simp

theorem eFunX_eq_iff (t s t' s' : ℝ) :
    eFunX t s = eFunX t' s' ↔
      (2 + (profX t s).1) * Real.cos t = (2 + (profX t' s').1) * Real.cos t' ∧
      (2 + (profX t s).1) * Real.sin t = (2 + (profX t' s').1) * Real.sin t' ∧
      (profX t s).2 = (profX t' s').2 := by
  constructor
  · intro h
    exact ⟨by rw [← eFunX_apply_zero t s, ← eFunX_apply_zero t' s', h],
      by rw [← eFunX_apply_one t s, ← eFunX_apply_one t' s', h],
      by rw [← eFunX_apply_two t s, ← eFunX_apply_two t' s', h]⟩
  · rintro ⟨h0, h1, h2⟩
    exact WithLp.ofLp_injective 2 (by
      funext i
      fin_cases i
      · simpa [eFunX, WithLp.ofLp_toLp] using h0
      · simpa [eFunX, WithLp.ofLp_toLp] using h1
      · simpa [eFunX, WithLp.ofLp_toLp] using h2)

theorem profX_zero (t : ℝ) : profX t 0 = W1 := by
  rw [profX_br1 (le_of_lt (sig1c_pos t))]
  simp [seg]

theorem eFunX_zero (t : ℝ) : eFunX t 0 = 0 := by
  exact WithLp.ofLp_injective 2 (by
    funext i
    fin_cases i <;> simp [eFunX, WithLp.ofLp_toLp, profX_zero, W1])

/-! ## The level `s = 1` -/

theorem profX_one (t : ℝ) : profX t 1 = W5c t := by
  by_cases hin : inRange t
  · by_cases h1 : (1 : ℝ) ≤ sig1c t
    · have hs1 : sig1c t = 1 := le_antisymm (sig1c_le_one t) h1
      have hsig1 : sig1 t = 1 := by rw [← hs1]; simp only [sig1c, if_pos hin]
      have hbump : bump t = 0 := by unfold sig1 at hsig1; linarith
      have hW : W2c t = W5c t := by
        rcases (bump_eq_zero_iff hin).1 hbump with h | h
        · rw [h]; exact W2c_u0
        · rw [h]; exact W2c_v0
      rw [profX_br1 h1, hs1, seg_right (by norm_num : (1 : ℝ) - 0 ≠ 0), hW]
    · have hsig1 : sig1 t < 1 := by
        have hs1c : sig1c t = sig1 t := by simp only [sig1c, if_pos hin]
        rw [← hs1c]; exact lt_of_not_ge h1
      have hbump : 0 < bump t := by unfold sig1 at hsig1; linarith
      have hopen := (bump_pos_iff hin).1 hbump
      have hs2c : sig2c t = sig2 t := by simp only [sig2c, if_pos hin]
      have h2 : ¬(1 : ℝ) ≤ sig2c t := by
        rw [hs2c]; intro hh
        linarith [sig2_lt_tauP hopen.1 hopen.2, tauP_lt_one hopen.1 hopen.2]
      rw [profX_br3 h1 h2, hs2c,
        seg_right (by linarith [sig1_lt_one hopen.1 hopen.2] : (1 : ℝ) - sig2 t ≠ 0)]
  · have hs1c : sig1c t = 1 := by simp only [sig1c, if_neg hin]
    have hW : W2c t = W5c t := W2c_eq_of_not_inRange hin
    have h1 : (1 : ℝ) ≤ sig1c t := by rw [hs1c]
    rw [profX_br1 h1, hs1c, hW, seg_right (by norm_num : (1 : ℝ) - 0 ≠ 0)]


/-! ## The polar-coordinate round trip -/

theorem norm_ofReal (σ : ℝ) : ‖(σ : ℂ)‖ = |σ| := by
  have h : Complex.normSq (σ : ℂ) = ‖(σ : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
  rw [Complex.normSq_ofReal] at h
  have h' : ‖(σ : ℂ)‖ ^ 2 = |σ| ^ 2 := by rw [sq_abs, ← h]; ring
  nlinarith [norm_nonneg (σ : ℂ), abs_nonneg σ]

theorem norm_cos_add_sin_mul_I (t : ℝ) :
    ‖(Real.cos t : ℂ) + Real.sin t * Complex.I‖ = 1 := by
  rw [Complex.ofReal_cos t, Complex.ofReal_sin t, ← Complex.exp_mul_I]
  exact Complex.norm_exp_ofReal_mul_I t

theorem norm_mul_cos_add_sin_mul_I (t : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ‖(↑σ : ℂ) * ((Real.cos t : ℂ) + Real.sin t * Complex.I)‖ = σ := by
  rw [Complex.norm_mul, norm_ofReal, norm_cos_add_sin_mul_I, mul_one, abs_of_pos hσ]

theorem mem_closedBall_mul_cos_add_sin (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (↑σ * ((Real.cos t : ℂ) + Real.sin t * Complex.I)) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_mul_cos_add_sin_mul_I t hσ]
  exact hσ1

/-- Points of the disc written in polar coordinates with angle `t ∈ (-π,π]` and radius
`σ ∈ (0,1]` are mapped by `eDiscX` to `eFunX t σ`. -/
theorem eDiscX_mul_cos_add_sin {t σ : ℝ} (ht : t ∈ Set.Ioc (-Real.pi) Real.pi) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) :
    eDiscX ⟨↑σ * ((Real.cos t : ℂ) + Real.sin t * Complex.I),
        mem_closedBall_mul_cos_add_sin t hσ hσ1⟩ = eFunX t σ := by
  have harg : Complex.arg (↑σ * ((Real.cos t : ℂ) + Real.sin t * Complex.I)) = t := by
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I hσ ht
  have hnorm : ‖(↑σ : ℂ) * ((Real.cos t : ℂ) + Real.sin t * Complex.I)‖ = σ :=
    norm_mul_cos_add_sin_mul_I t hσ
  rw [eDiscX]
  simp only [Subtype.coe_mk]
  rw [harg, hnorm]

/-! ## The seam `t = ±π` and elementary bounds -/

theorem not_inRange_neg_pi : ¬ inRange (-Real.pi) := by
  intro h; simp only [inRange, u0, v0] at h; linarith [h.1, Real.pi_pos]

theorem not_inRange_pi : ¬ inRange Real.pi := by
  intro h; simp only [inRange, u0, v0] at h; linarith [h.2, Real.pi_pos]

theorem W5c_neg_pi : W5c (-Real.pi) = W5c Real.pi := by
  simp only [W5c, Real.cos_neg, Real.sin_neg, Real.cos_pi, Real.sin_pi]
  norm_num

theorem W2c_neg_pi : W2c (-Real.pi) = W2c Real.pi := by
  unfold W2c
  rw [if_neg not_inRange_neg_pi, if_neg not_inRange_pi, W5c_neg_pi]

theorem sig1c_neg_pi : sig1c (-Real.pi) = sig1c Real.pi := by
  unfold sig1c; rw [if_neg not_inRange_neg_pi, if_neg not_inRange_pi]

theorem W2c_fst_ge (t : ℝ) : -1 ≤ (W2c t).1 := by
  unfold W2c; split_ifs with h
  · exact Real.neg_one_le_cos _
  · simp only [W5c]; exact Real.neg_one_le_cos t

theorem W3c_fst_ge (t : ℝ) : -1 ≤ (W3c t).1 := by
  unfold W3c; split_ifs with h
  · exact Real.neg_one_le_cos _
  · simp only [W5c]; exact Real.neg_one_le_cos t

theorem W5c_fst_ge (t : ℝ) : -1 ≤ (W5c t).1 := by
  simp only [W5c]; exact Real.neg_one_le_cos t

theorem sig1_le_one_of_inRange {t : ℝ} (h : inRange t) : sig1 t ≤ 1 := by
  have hb := bump_nonneg_of_inRange h
  unfold sig1; linarith

theorem sig2_le_one_of_inRange {t : ℝ} (h : inRange t) : sig2 t ≤ 1 := by
  have hb := bump_nonneg_of_inRange h
  unfold sig2; linarith

theorem sig2_pos (t : ℝ) : 0 < sig2 t := by
  have hb : bump t ≤ 1 := Real.sin_le_one _
  unfold sig2; linarith

/-- The first waypoint level is bounded below by `3/4`. -/
theorem sig1c_ge (t : ℝ) : 3 / 4 ≤ sig1c t := by
  by_cases h : inRange t
  · rw [sig1c, if_pos h]
    have hb : bump t ≤ 1 := Real.sin_le_one _
    unfold sig1; linarith
  · rw [sig1c, if_neg h]; norm_num

/-- A segment joining two points of `[-1,∞)²`, evaluated between its levels, has first
coordinate `> -2`. -/
theorem seg_fst_gt {P Q : ℝ × ℝ} (hP : -1 ≤ P.1) (hQ : -1 ≤ Q.1) {a b s : ℝ}
    (h1 : a ≤ s) (h2 : s ≤ b) : -2 < (seg P Q a b s).1 := by
  by_cases hab : b - a = 0
  · have hsa : s = a := by linarith
    have : seg P Q a b a = P := by simp [seg]
    rw [hsa, this]; linarith
  · have hba : 0 < b - a := lt_of_le_of_ne (by linarith) (Ne.symm hab)
    have hlam0 : 0 ≤ (s - a) / (b - a) := div_nonneg (by linarith) hba.le
    have hlam1 : (s - a) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith)
    simp only [seg]
    nlinarith

/-- A segment from `W1 = (-2,0)` to a point of `[-1,∞)²`, evaluated strictly after its
lower level, has first coordinate `> -2`. -/
theorem seg_W1_fst_gt {Q : ℝ × ℝ} (hQ : -1 ≤ Q.1) {b s : ℝ} (hb : 0 < b) (h1 : 0 < s)
    (h2 : s ≤ b) : -2 < (seg W1 Q 0 b s).1 := by
  have hlam0 : 0 < s / b := div_pos h1 hb
  have hlam1 : s / b ≤ 1 := (div_le_one hb).mpr h2
  simp only [seg, W1, sub_zero]
  nlinarith

/-- On the way to the boundary the profile stays strictly to the right of the axis point
`(-2,0)`: this is the fact that makes the azimuth visible in the image of `eFunX`. -/
theorem profX_fst_gt (t s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : -2 < (profX t s).1 := by
  rw [profX]
  split_ifs with h1 h2
  · exact seg_W1_fst_gt (W2c_fst_ge t) (sig1c_pos t) hs h1
  · exact seg_fst_gt (W2c_fst_ge t) (W3c_fst_ge t) (le_of_lt (lt_of_not_ge h1)) h2
  · exact seg_fst_gt (W3c_fst_ge t) (W5c_fst_ge t) (le_of_lt (lt_of_not_ge h2)) hs1

theorem W3c_neg_pi : W3c (-Real.pi) = W3c Real.pi := by
  unfold W3c
  rw [if_neg not_inRange_neg_pi, if_neg not_inRange_pi, W5c_neg_pi]

theorem sig2c_neg_pi : sig2c (-Real.pi) = sig2c Real.pi := by
  unfold sig2c; rw [if_neg not_inRange_neg_pi, if_neg not_inRange_pi]

theorem profX_neg_pi_eq (s : ℝ) : profX (-Real.pi) s = profX Real.pi s := by
  unfold profX
  rw [sig1c_neg_pi, sig2c_neg_pi, W2c_neg_pi, W3c_neg_pi, W5c_neg_pi]

/-- The two parametrisations `t = ±π` of the degenerate profile agree. -/
theorem eFunX_neg_pi_eq (s : ℝ) : eFunX (-Real.pi) s = eFunX Real.pi s := by
  rw [eFunX_eq_iff, profX_neg_pi_eq]
  refine ⟨?_, ?_, rfl⟩
  · rw [Real.cos_neg]
  · rw [Real.sin_neg, Real.sin_pi]; ring

end

end Work.Drive.EpsForm
