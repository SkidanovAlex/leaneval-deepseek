import Mathlib
import Submission.Work.Surf.grbDefs
import Submission.Work.Surf.grbCurve
import Submission.Work.Surf.Neutral.GrbLevel
import Submission.Work.Surf.Neutral.GrbTransport
import Submission.Work.Surf.goodRayDefs
import Submission.Work.Surf.defs
import Submission.Work.Drive.Neutral.HalfDir
import Submission.Work.Surf.Neutral.WindingEqTwoMulDegreeHalfDir
import Submission.Work.Surf.ncard_crossSet_mod_two
import Submission.Work.Surf.hasDerivAt_of_lift_arg
import Submission.Work.Surf.volume_badSet_eq_zero
import Submission.Work.Surf.chordFamily
import Submission.Work.Drive.winding_homotopy
import Submission.Work.Surf.Neutral.GrbBadSet
import Submission.Work.Surf.Neutral.GrbDegEqStraight
import Submission.Work.Surf.chordMeet_straight_odd

/-!
# (Neutral copy) `ExistsGoodRayBoundaryOdd`

Verbatim copy of the module `Work.Surf.ChordN.exists_good_ray_boundary_odd` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
/-!
# A good ray direction for the difference map of two chords, with an odd boundary count
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open Set Work.Surf.GRB Work.Drive

noncomputable section

open scoped Topology



/-! ## Elementary consequences of the hypotheses -/

/-- The imaginary part of the quotient of two complexifications, in closed form. -/
lemma gToC_div_im_mul {y z : ℝ × ℝ} (hz : z ≠ 0) :
    (gToC y / gToC z).im * (z.1 ^ 2 + z.2 ^ 2) = cross2 z y := by
  have hnsq : (gToC z).normSq = z.1 ^ 2 + z.2 ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [gToC, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hN : z.1 ^ 2 + z.2 ^ 2 ≠ 0 := by
    intro h
    have h1 : z.1 = 0 := by nlinarith [sq_nonneg z.2, sq_nonneg z.1]
    have h2 : z.2 = 0 := by nlinarith [sq_nonneg z.2, sq_nonneg z.1]
    exact hz (Prod.ext h1 h2)
  rw [Complex.div_im, hnsq]
  simp only [gToC, Complex.ofReal_re, Complex.ofReal_im, cross2]
  rw [sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
    mul_div_cancel_right₀ _ hN, mul_div_cancel_right₀ _ hN]
  ring

/-- The imaginary part of the quotient vanishes exactly when the two vectors are parallel. -/
lemma gToC_div_im_ne_zero_iff {y z : ℝ × ℝ} (hz : z ≠ 0) :
    (gToC y / gToC z).im ≠ 0 ↔ cross2 z y ≠ 0 := by
  have hz2 : z.1 ^ 2 + z.2 ^ 2 ≠ 0 := by
    intro h
    have h1 : z.1 = 0 := by nlinarith [sq_nonneg z.2, sq_nonneg z.1]
    have h2 : z.2 = 0 := by nlinarith [sq_nonneg z.2, sq_nonneg z.1]
    exact hz (Prod.ext h1 h2)
  have key : (gToC y / gToC z).im * (z.1 ^ 2 + z.2 ^ 2) = cross2 z y := gToC_div_im_mul hz
  constructor
  · intro h hc
    exact h ((mul_eq_zero.mp (by rw [key, hc])).resolve_right hz2)
  · intro h hi
    exact h (by rw [← key, hi, zero_mul])

/-- **The derivative of the lift of the honest direction is non-zero at a transverse crossing.** -/
lemma deriv_grbLift_ne_zero_of_cross2 {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {u : ℝ} (h : cross2 (grbCurveR a b u) (deriv (grbCurveR a b) u) ≠ 0) :
    deriv (grbLift a b ha hb hint) u ≠ 0 := by
  have hd : deriv (grbLift a b ha hb hint) u
      = (deriv (grbCurveC a b) u / grbCurveC a b u).im / (2 * Real.pi) :=
    (hasDerivAt_grbLift (a := a) (b := b) ha hb hint u).deriv
  rw [hd, deriv_grbCurveC ha hb u]
  rw [div_ne_zero_iff]
  refine ⟨?_, by positivity⟩
  have hne : grbCurveR a b u ≠ 0 := grbCurveR_ne_zero (a := a) (b := b) hint u
  exact (gToC_div_im_ne_zero_iff (y := deriv (grbCurveR a b) u) (z := grbCurveR a b u)
    hne).mpr h

/-- Under `hint`, the two starting points `a 0` and `b 0` of the chords are linearly independent. -/
lemma det2_start_ne_zero {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : Work.Drive.IsChord a)
    (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) :
    det2 (a 0) (b 0) ≠ 0 := by
  intro h0
  have hb0 : b 0 ≠ 0 := by
    intro h
    have hn : ‖b 0‖ = 1 := hb.start
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨lam, hlam⟩ := Work.Surf.det2_eq_zero_imp_smul hb0 h0
  have hnorm : ‖a 0‖ = |lam| := by
    rw [hlam, norm_smul, Real.norm_eq_abs, hb.start, mul_one]
  have h1 : |lam| = 1 := by rw [← hnorm]; exact ha.start
  have hb1 : b 1 = - b 0 := by
    have h := hb.periodic 0
    rw [zero_add] at h
    rw [h, Work.Drive.antipode_apply]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h1 with h | h
  · have hb' : a 0 = b 0 := by rw [hlam, h, one_smul]
    exact absurd (hint 0 0 (by norm_num) (by norm_num) hb').1.1 (lt_irrefl 0)
  · have hb' : a 0 = b 1 := by rw [hlam, h, neg_one_smul, hb1]
    exact absurd (hint 0 1 (by norm_num) (by norm_num) hb').1.1 (lt_irrefl 0)

/-- **The straight chords satisfy the `hint` hypothesis.** -/
lemma hint_straightChords {z w : EuclideanSpace ℝ (Fin 2)} (hz : z ∈ Work.Drive.unitCircle)
    (hw : w ∈ Work.Drive.unitCircle) (hzw : det2 z w ≠ 0) :
    ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      Work.Drive.straightChord z s = Work.Drive.straightChord w t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧
        ‖Work.Drive.straightChord z s‖ < 1 := by
  intro s t hs ht heq
  have hz1 : ‖z‖ = 1 := hz
  have heq' : Real.cos (Real.pi * s) • z = Real.cos (Real.pi * t) • w := by
    simpa only [Work.Drive.straightChord] using heq
  have hcs : Real.cos (Real.pi * s) = 0 := by
    have h := congrArg (fun y => det2 y w) heq'
    rw [Work.Drive.det2_smul_left, Work.Drive.det2_smul_left, Work.Drive.det2_self,
      mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hzw
  have hct : Real.cos (Real.pi * t) = 0 := by
    have h := congrArg (fun y => det2 z y) heq'
    rw [Work.Drive.det2_smul_right, Work.Drive.det2_smul_right, Work.Drive.det2_self,
      mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hzw
  have hs0 : s ≠ 0 := by
    intro h; rw [h, mul_zero, Real.cos_zero] at hcs; exact one_ne_zero hcs
  have hs1 : s ≠ 1 := by
    intro h; rw [h, mul_one, Real.cos_pi] at hcs; norm_num at hcs
  have ht0 : t ≠ 0 := by
    intro h; rw [h, mul_zero, Real.cos_zero] at hct; exact one_ne_zero hct
  have ht1 : t ≠ 1 := by
    intro h; rw [h, mul_one, Real.cos_pi] at hct; norm_num at hct
  refine ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩,
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, ?_⟩
  rw [Work.Drive.straightChord_norm z hz1 s, hcs]
  norm_num

/-! ## The level set of the honest direction -/

/-- The finiteness half of `grb_level_odd`. -/
theorem grb_level_finite {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    (α : ℝ) (htr : ∀ t ∈ Set.Ico (0:ℝ) 1,
      (∃ k : ℤ, grbLift a b ha hb hint t - α = (k : ℝ)) →
      deriv (grbLift a b ha hb hint) t ≠ 0) :
    ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧
      grbDir a b (t : UnitAddCircle) = (α : UnitAddCircle)} : Set ℝ).Finite := by
  have hset : {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ ∃ k : ℤ,
      (fun t : ℝ => grbLift a b ha hb hint t - α) t = (k:ℝ)}
      = {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = (α : UnitAddCircle)} := by
    ext t
    constructor
    · rintro ⟨ht, k, hk⟩
      refine ⟨ht, ?_⟩
      have hLt : grbLift a b ha hb hint t = α + (k:ℝ) := by linarith
      rw [← grbLift_lifts ha hb hint t, hLt]
      have : (((α + (k:ℝ)) : ℝ) : UnitAddCircle) = (α : UnitAddCircle) := by
        rw [AddCircle.coe_add, show (((k:ℝ)) : UnitAddCircle) = 0 from ?_, add_zero]
        rw [show (k:ℝ) = k • (1:ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period (1:ℝ),
          zsmul_zero]
      exact this
    · rintro ⟨ht, ht'⟩
      refine ⟨ht, ?_⟩
      have h1 : ((grbLift a b ha hb hint t : ℝ) : UnitAddCircle) = (α : UnitAddCircle) := by
        rw [grbLift_lifts ha hb hint t]; exact ht'
      have h2 : ((grbLift a b ha hb hint t - α : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, h1, sub_self]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1:ℝ))).mp h2
      refine ⟨k, ?_⟩
      show grbLift a b ha hb hint t - α = (k : ℝ)
      rw [← hk, zsmul_eq_mul, mul_one]
  set G : ℝ → ℝ := fun t => grbLift a b ha hb hint t - α with hG
  have hGcont : Continuous G := (continuous_grbLift ha hb hint).sub continuous_const
  have hGper : ∀ t : ℝ, G (t + 1) = G t + (grbDeg a b ha hb hint : ℝ) := by
    intro t
    simp only [hG]
    rw [grbLift_add_one ha hb hint t]
    ring
  have hGderiv : ∀ t : ℝ, t ∈ Set.Ico (0:ℝ) 1 → (∃ k : ℤ, G t = (k:ℝ)) →
      HasDerivAt G (deriv G t) t ∧ deriv G t ≠ 0 := by
    intro t ht hk
    have hk' : ∃ k : ℤ, grbLift a b ha hb hint t - α = (k:ℝ) := hk
    have hdL : deriv (grbLift a b ha hb hint) t ≠ 0 := htr t ht hk'
    have h1 : HasDerivAt (grbLift a b ha hb hint) (deriv (grbLift a b ha hb hint) t) t := by
      have h := hasDerivAt_grbLift (a := a) (b := b) ha hb hint t
      exact h.congr_deriv h.deriv.symm
    have h2 : HasDerivAt G (deriv (grbLift a b ha hb hint) t) t := by
      simpa only [hG] using h1.sub_const α
    have h3 : deriv G t = deriv (grbLift a b ha hb hint) t := by
      simp only [hG, deriv_sub_const]
    exact ⟨h3 ▸ h2, by rw [h3]; exact hdL⟩
  rw [← hset]
  exact (ncard_crossSet_mod_two G hGcont (grbDeg a b ha hb hint) hGper hGderiv).1

/-- **The level condition is the ray condition.** -/
lemma grbDir_eq_gDir_iff {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {v : ℝ × ℝ} (hv : v ≠ 0) (u : ℝ) :
    (grbDir a b (u : UnitAddCircle) = gDir v) ↔
      ∃ r : ℝ, 0 < r ∧ grbCurveR a b u = r • v := by
  rw [grbDir_apply_eq a b u]
  exact gDir_eq_iff (grbCurveR_ne_zero (a := a) (b := b) hint u) hv

/-- At a corner time the direction of the curve value is a corner direction. -/
lemma mem_gCornerSet_of_corner {g : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {u : ℝ}
    (hu : u ∈ ({0, 1/4, 1/2, 3/4} : Set ℝ))
    (hray : ∃ r : ℝ, 0 < r ∧ g u = r • v) :
    v ∈ gCornerSet g := by
  obtain ⟨r, hr, hru⟩ := hray
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hgen : ∀ j : Fin 4, u = ((j : ℝ) / 4) → v ∈ gCornerSet g := by
    intro j hj
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    refine ⟨r⁻¹, ?_⟩
    rw [hj] at hru
    show r⁻¹ • g ((j : ℝ) / 4) = v
    rw [hru, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff] at hu
  rcases hu with h | h | h | h
  · exact hgen 0 (by rw [h]; norm_num)
  · exact hgen 1 (by rw [h]; norm_num)
  · exact hgen 2 (by rw [h]; norm_num)
  · exact hgen 3 (by rw [h]; norm_num)

/-- At a ray meeting that avoids the tangent cone, the curve crosses the ray transversally. -/
lemma cross2_ne_of_notMem_gTanCone {g : ℝ → ℝ × ℝ} {v : ℝ × ℝ}
    (hv : v ∉ gTanCone g) {u : ℝ}
    (hray : ∃ r : ℝ, 0 < r ∧ g u = r • v) :
    cross2 (g u) (deriv g u) ≠ 0 := by
  intro h0
  obtain ⟨r, hr, hru⟩ := hray
  have hr0 : r ≠ 0 := ne_of_gt hr
  refine hv ⟨(u, r⁻¹), ⟨?_, Set.mem_univ _⟩, ?_⟩
  · exact h0
  · show r⁻¹ • g u = v
    rw [hru, smul_smul, inv_mul_cancel₀ hr0, one_smul]

/-! ## The straight chords -/

lemma sqRamp_half : sqRamp (1 / 2) = 1 / 2 := by norm_num [sqRamp]

lemma sqK_half : sqK (1 / 2) = 6 := by norm_num [sqK]

/-- `sqPar (7/8)` is the midpoint of the left edge. -/
lemma sqPar_seven_eighths : sqPar (7 / 8) = ((0 : ℝ), 1 / 2) := by
  rw [sqPar_eq_edge4 (by norm_num) (by norm_num),
    show (4:ℝ) * (7 / 8) - 3 = 1 / 2 by norm_num, sqRamp_half]
  norm_num

/-- **The boundary curve of the two straight chords is the boundary of a parallelogram**: it is
`u ↦ cos (π s u) ● ẑ - cos (π t u) ● ŵ`. -/
lemma grbCurveR_straight (z w : EuclideanSpace ℝ (Fin 2)) (u : ℝ) :
    grbCurveR (Work.Drive.straightChord z) (Work.Drive.straightChord w) u
      = Real.cos (Real.pi * (sqPar u).1) • gEu z
        - Real.cos (Real.pi * (sqPar u).2) • gEu w := by
  rw [grbCurveR, grbCurve_coe, grbDiff, Work.Drive.straightChord, Work.Drive.straightChord,
    map_smul, map_smul]

/-- The derivative of the straight boundary curve at `u = 7/8` (the midpoint of the left edge). -/
lemma deriv_straight_seven_eighths (z w : EuclideanSpace ℝ (Fin 2)) :
    deriv (grbCurveR (Work.Drive.straightChord z) (Work.Drive.straightChord w)) (7 / 8)
      = ((-(6 * Real.pi)) : ℝ) • gEu w := by
  have hev : (fun u : ℝ =>
      grbCurveR (Work.Drive.straightChord z) (Work.Drive.straightChord w) u)
      =ᶠ[𝓝 (7 / 8 : ℝ)]
      (fun u : ℝ => gEu z
        - Real.cos (Real.pi * (1 - sqRamp (4 * u - 3))) • gEu w) := by
    filter_upwards [Ioo_mem_nhds (show (3:ℝ)/4 < 7/8 by norm_num)
      (show (7:ℝ)/8 < 1 by norm_num)] with u hu
    rw [grbCurveR_straight, sqPar_eq_edge4 (le_of_lt hu.1) (le_of_lt hu.2)]
    norm_num
  rw [hev.deriv_eq]
  -- the explicit derivative
  have hsq : HasDerivAt (fun u : ℝ => sqRamp (4 * u - 3)) (6 : ℝ) (7 / 8) := by
    have h := hasDerivAt_sqRamp_shift 3 (7 / 8 : ℝ)
    convert h using 1
    norm_num [sqK]
  have hinner : HasDerivAt (fun u : ℝ => Real.pi * (1 - sqRamp (4 * u - 3)))
      (Real.pi * (-(6:ℝ))) (7 / 8) := by
    have h1 : HasDerivAt (fun u : ℝ => 1 - sqRamp (4 * u - 3)) (-(6:ℝ)) (7 / 8) :=
      hsq.const_sub 1
    have h2 := h1.const_mul Real.pi
    convert h2 using 1
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (Real.pi * (1 - sqRamp (4 * u - 3))))
      (-(Real.sin (Real.pi * (1 - sqRamp (4 * (7/8) - 3)))) * (Real.pi * (-(6:ℝ)))) (7 / 8) :=
    hinner.cos
  have hval : (-(Real.sin (Real.pi * (1 - sqRamp (4 * (7/8) - 3)))) * (Real.pi * (-(6:ℝ))))
      = 6 * Real.pi := by
    rw [show (4:ℝ) * (7/8) - 3 = 1/2 by norm_num, sqRamp_half,
      show Real.pi * (1 - 1/2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    ring
  rw [hval] at hcos
  have hfull : HasDerivAt (fun u : ℝ => gEu z
      - Real.cos (Real.pi * (1 - sqRamp (4 * u - 3))) • gEu w)
      (-((6 * Real.pi) • gEu w)) (7 / 8) :=
    (hcos.smul_const (gEu w)).const_sub (gEu z)
  have hgoal : (-((6 * Real.pi) • gEu w)) = (-(6 * Real.pi)) • gEu w := by
    rw [neg_smul]
  rw [← hgoal]
  exact hfull.deriv


/-- **The level set of the two straight chords in the direction of `ẑ = gEu z` is the single time
`7/8`, the midpoint of the left edge.** -/
lemma levelSet_straight (z w : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Work.Drive.unitCircle)
    (hw : w ∈ Work.Drive.unitCircle) (hzw : det2 z w ≠ 0) :
    {u : ℝ | u ∈ Set.Ico (0:ℝ) 1 ∧
      grbDir (Work.Drive.straightChord z) (Work.Drive.straightChord w) (u : UnitAddCircle)
        = gDir (gEu z)} = {7 / 8} := by
  have hz1 : ‖z‖ = 1 := hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hgz : gEu z ≠ 0 := fun h => hz0 (gEu_injective (by rw [h, map_zero]))
  have hcross : cross2 (gEu z) (gEu w) ≠ 0 := by rw [gCross_eu]; exact hzw
  ext u
  constructor
  · rintro ⟨hu, hu'⟩
    obtain ⟨r, hr, hru⟩ := (grbDir_eq_gDir_iff (hint_straightChords hz hw hzw) hgz u).mp hu'
    rw [grbCurveR_straight] at hru
    have hsub : (Real.cos (Real.pi * (sqPar u).1) - r) • gEu z
        = Real.cos (Real.pi * (sqPar u).2) • gEu w := by
      rw [sub_smul, sub_eq_iff_eq_add, ← hru]
      abel
    have hct : Real.cos (Real.pi * (sqPar u).2) = 0 := by
      have h := congrArg (fun y => cross2 (gEu z) y) hsub
      simp only [cross2_smul_right, cross2_self, mul_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hcross
    have hcs : Real.cos (Real.pi * (sqPar u).1) = r := by
      have h := congrArg (fun y => cross2 y (gEu w)) hsub
      simp only [cross2_smul_left, cross2_self, mul_zero] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hcross)
    have ht1 : (sqPar u).2 = 1 / 2 := by
      have h2 : (sqPar u).2 ∈ Set.Icc (0:ℝ) 1 := (sqPar_mem_sqBoxBdry u).1.2
      have hne0 : (sqPar u).2 ≠ 0 := by
        intro h; rw [h, mul_zero, Real.cos_zero] at hct; exact one_ne_zero hct
      have hne1 : (sqPar u).2 ≠ 1 := by
        intro h; rw [h, mul_one, Real.cos_pi] at hct; norm_num at hct
      exact Work.Drive.cos_pi_mul_eq_zero_of_mem_Ioo
        ⟨lt_of_le_of_ne h2.1 (Ne.symm hne0), lt_of_le_of_ne h2.2 hne1⟩ hct
    have hs0 : (sqPar u).1 = 0 := by
      have hmem := (sqPar_mem_sqBoxBdry u).2
      rcases hmem with h | h | h | h
      · exact h
      · rw [h, mul_one, Real.cos_pi] at hcs
        linarith [hr]
      · rw [h] at ht1; norm_num at ht1
      · rw [ht1] at h; norm_num at h
    have hpar : sqPar u = sqPar (7 / 8) := by
      rw [sqPar_seven_eighths]; exact Prod.ext hs0 ht1
    have hu78 : u = 7 / 8 := sqPar_injOn hu ⟨by norm_num, by norm_num⟩ hpar
    rw [hu78]
    exact Set.mem_singleton _
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    refine ⟨by norm_num, ?_⟩
    rw [grbDir_apply_eq]
    congr 1
    rw [grbCurveR_straight, sqPar_seven_eighths,
      show Real.pi * (0:ℝ) = 0 by ring, Real.cos_zero, one_smul,
      show Real.pi * (1/2) = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_smul, sub_zero]

/-- **The honest degree of the boundary curve of two straight chords is odd.** -/
theorem grbStraightDeg_odd (z w : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ Work.Drive.unitCircle)
    (hw : w ∈ Work.Drive.unitCircle) (hzw : det2 z w ≠ 0)
    (hintS : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      Work.Drive.straightChord z s = Work.Drive.straightChord w t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖Work.Drive.straightChord z s‖ < 1) :
    Odd (grbDeg (Work.Drive.straightChord z) (Work.Drive.straightChord w)
      (Work.Drive.straightChord_isChord hz).contDiff
      (Work.Drive.straightChord_isChord hw).contDiff hintS) := by
  have hzC : ContDiff ℝ 1 (Work.Drive.straightChord z) :=
    (Work.Drive.straightChord_isChord hz).contDiff
  have hwC : ContDiff ℝ 1 (Work.Drive.straightChord w) :=
    (Work.Drive.straightChord_isChord hw).contDiff
  have hz1 : ‖z‖ = 1 := hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz1; exact zero_ne_one hz1
  have hcross : cross2 (gEu z) (gEu w) ≠ 0 := by rw [gCross_eu]; exact hzw
  have hcurve78 : grbCurveR (Work.Drive.straightChord z) (Work.Drive.straightChord w) (7 / 8)
      = gEu z := by
    rw [grbCurveR_straight, sqPar_seven_eighths,
      show Real.pi * (0:ℝ) = 0 by ring, Real.cos_zero, one_smul,
      show Real.pi * (1/2) = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_smul, sub_zero]
  have htr : ∀ t ∈ Set.Ico (0:ℝ) 1, (∃ k : ℤ,
      grbLift (Work.Drive.straightChord z) (Work.Drive.straightChord w) hzC hwC hintS t
        - (Complex.arg (gToC (gEu z)) / (2 * Real.pi)) = (k : ℝ)) →
      deriv (grbLift (Work.Drive.straightChord z) (Work.Drive.straightChord w) hzC hwC hintS)
        t ≠ 0 := by
    intro t ht hk
    have hL : ((grbLift (Work.Drive.straightChord z) (Work.Drive.straightChord w) hzC hwC hintS
        t : ℝ) : UnitAddCircle) = gDir (gEu z) := by
      obtain ⟨k, hk'⟩ := hk
      rw [show grbLift (Work.Drive.straightChord z) (Work.Drive.straightChord w) hzC hwC hintS t
        = Complex.arg (gToC (gEu z)) / (2 * Real.pi) + (k : ℝ) by linarith]
      rw [AddCircle.coe_add, show (((k : ℝ)) : UnitAddCircle) = 0 from ?_, add_zero]
      · rfl
      · rw [show (k : ℝ) = k • (1:ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period (1:ℝ),
          zsmul_zero]
    have hlev : grbDir (Work.Drive.straightChord z) (Work.Drive.straightChord w)
        (t : UnitAddCircle) = gDir (gEu z) := by
      rw [← grbLift_lifts hzC hwC hintS t, hL]
    have ht78 : t = 7 / 8 := by
      have hmem : t ∈ ({7 / 8} : Set ℝ) := by
        rw [← levelSet_straight z w hz hw hzw]
        exact ⟨ht, hlev⟩
      exact hmem
    rw [ht78]
    refine deriv_grbLift_ne_zero_of_cross2 hzC hwC hintS ?_
    rw [hcurve78, deriv_straight_seven_eighths, cross2_smul_right]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) hcross
  have hset : ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧
      grbDir (Work.Drive.straightChord z) (Work.Drive.straightChord w) (t : UnitAddCircle)
        = ((Complex.arg (gToC (gEu z)) / (2 * Real.pi) : ℝ) : UnitAddCircle)}) = {7 / 8} := by
    rw [show ((Complex.arg (gToC (gEu z)) / (2 * Real.pi) : ℝ) : UnitAddCircle) = gDir (gEu z)
      from rfl]
    exact levelSet_straight z w hz hw hzw
  have hodd : Odd (({7 / 8} : Set ℝ).ncard) := by
    rw [Set.ncard_singleton]; exact ⟨0, by norm_num⟩
  refine (grb_level_odd hzC hwC hintS (Complex.arg (gToC (gEu z)) / (2 * Real.pi)) htr).mp ?_
  rw [hset]
  exact hodd

/-! ## The face derivatives and the transfer of the conclusions -/

lemma deriv_fBot {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (s : ℝ) :
    deriv (fBot a b) s = deriv (fun t : ℝ => gEu (a t)) s := by
  have h : fBot a b = fun s : ℝ => gEu (a s) - gEu (b 0) := by
    funext t; simp only [fBot, grbDiff]
  rw [h, deriv_sub_const]

lemma deriv_fTop {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (s : ℝ) :
    deriv (fTop a b) s = deriv (fun t : ℝ => gEu (a t)) s := by
  have h : fTop a b = fun s : ℝ => gEu (a s) - gEu (b 1) := by
    funext t; simp only [fTop, grbDiff]
  rw [h, deriv_sub_const]

lemma deriv_fLft {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (s : ℝ) :
    deriv (fLft a b) s = - deriv (fun t : ℝ => gEu (b t)) s := by
  have h : fLft a b = fun s : ℝ => gEu (a 0) - gEu (b s) := by
    funext t; simp only [fLft, grbDiff]
  rw [h, deriv_const_sub]

lemma deriv_fRgt {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (s : ℝ) :
    deriv (fRgt a b) s = - deriv (fun t : ℝ => gEu (b t)) s := by
  have h : fRgt a b = fun s : ℝ => gEu (a 1) - gEu (b s) := by
    funext t; simp only [fRgt, grbDiff]
  rw [h, deriv_const_sub]

lemma cross2_swap_ne {a b : ℝ × ℝ} (h : cross2 a b ≠ 0) : cross2 b a ≠ 0 := by
  intro h0
  exact h (by rw [cross2_skew, h0, neg_zero])

lemma cross2_ne_of_smul_left {r : ℝ} {a b : ℝ × ℝ} (h : cross2 (r • a) b ≠ 0) :
    cross2 b a ≠ 0 := by
  refine cross2_swap_ne ?_
  intro h0
  exact h (by rw [cross2_smul_left, h0, mul_zero])

lemma cross2_ne_of_smul_left_neg {r : ℝ} {a b : ℝ × ℝ} (h : cross2 (r • a) (-b) ≠ 0) :
    cross2 b a ≠ 0 := by
  intro h0
  refine h ?_
  rw [cross2_smul_left]
  have hz : cross2 a (-b) = 0 := by
    rw [show (-b) = (-1:ℝ) • b from by rw [neg_one_smul], cross2_smul_right,
      show cross2 a b = - cross2 b a from cross2_skew a b, h0, neg_zero, mul_zero]
  rw [hz, mul_zero]

/-- **The difference map of two chords is bounded on the boundary of the square.** -/
lemma exists_large_scale {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : Work.Drive.IsChord a)
    (hb : Work.Drive.IsChord b) {v₀ : ℝ × ℝ} (hv₀ : v₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Work.Surf.sqBdry, ‖a (x 0) - b (x 1)‖ < ‖c • gEuInv v₀‖ := by
  have hv : gEuInv v₀ ≠ 0 := fun h => hv₀ (by rw [← gEu_gEuInv v₀, h, map_zero])
  have hnorm : 0 < ‖gEuInv v₀‖ := norm_pos_iff.mpr hv
  have hc : 0 < 3 / ‖gEuInv v₀‖ := div_pos (by norm_num) hnorm
  refine ⟨3 / ‖gEuInv v₀‖, hc, fun x hx => ?_⟩
  have hna : ‖a (x 0)‖ ≤ 1 := ha.mem_disk (x 0) hx.1.1
  have hnb : ‖b (x 1)‖ ≤ 1 := hb.mem_disk (x 1) hx.1.2
  have hle : ‖a (x 0) - b (x 1)‖ ≤ 2 := by
    have := norm_sub_le (a (x 0)) (b (x 1))
    linarith
  have hval : ‖(3 / ‖gEuInv v₀‖) • gEuInv v₀‖ = 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, div_mul_cancel₀ _ (ne_of_gt hnorm)]
  rw [hval]
  linarith

/-- **Transfer of the good-ray conclusions from the product model to `EuclideanSpace ℝ (Fin 2)`.**
Given the ray-meeting conclusions in the product model `ℝ × ℝ` for the difference map
`grbDiff a b = gEu (a ·) - gEu (b ·)` in a direction `v₀ ≠ 0`, the corresponding conclusions hold in
`EuclideanSpace ℝ (Fin 2)` for the direction `c • gEuInv v₀` (`c > 0`). -/
theorem euclidean_transfer {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) {v₀ : ℝ × ℝ} (hv₀ : v₀ ≠ 0) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ x ∈ Work.Surf.sqBdry, ‖a (x 0) - b (x 1)‖ < ‖c • gEuInv v₀‖)
    (hfin : (rayMeetP (grbDiff a b) v₀ ∩ Work.Drive.sqBoxBdry).Finite)
    (hcorner : ∀ p ∈ Work.Drive.sqBoxBdry, p ∈ rayMeetP (grbDiff a b) v₀ →
      ¬ ((p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 0 ∨ p.2 = 1)))
    (htranss : ∀ p ∈ Work.Drive.sqBoxBdry, p ∈ rayMeetP (grbDiff a b) v₀ →
      ((p.2 = 0 ∨ p.2 = 1) → cross2 (deriv (fun s => gEu (a s)) p.1) v₀ ≠ 0) ∧
      ((p.1 = 0 ∨ p.1 = 1) → cross2 (deriv (fun t => gEu (b t)) p.2) v₀ ≠ 0))
    (hodd : Odd ((rayMeetP (grbDiff a b) v₀ ∩ Work.Drive.sqBoxBdry).ncard)) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      (∀ x ∈ Work.Surf.sqBdry, ‖a (x 0) - b (x 1)‖ < ‖v‖) ∧
      (Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1)) v ∩
        Work.Surf.sqBdry).Finite ∧
      (∀ x ∈ Work.Surf.sqBdry, x ∈ Work.Surf.rayMeet
          (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) v →
        ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1))) ∧
      (∀ x ∈ Work.Surf.sqBdry, x ∈ Work.Surf.rayMeet
          (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) v →
        ((x 1 = 0 ∨ x 1 = 1) → Work.Drive.det2 (deriv a (x 0)) v ≠ 0) ∧
        ((x 0 = 0 ∨ x 0 = 1) → Work.Drive.det2 (deriv b (x 1)) v ≠ 0)) ∧
      Odd ((Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1)) v ∩
        Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard) := by
  have hvE : gEuInv v₀ ≠ 0 := fun h => hv₀ (by rw [← gEu_gEuInv v₀, h, map_zero])
  have hgEu_vE : gEu (c • gEuInv v₀) = c • v₀ := by rw [map_smul, gEu_gEuInv]
  have hdiff : ∀ x : EuclideanSpace ℝ (Fin 2),
      gEu (a (x 0) - b (x 1)) = grbDiff a b (gEu x) := by
    intro x; rw [map_sub, grbDiff]; rfl
  have hmem : ∀ x : EuclideanSpace ℝ (Fin 2),
      (x ∈ Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1))
          (c • gEuInv v₀) ↔ gEu x ∈ rayMeetP (grbDiff a b) v₀) := by
    intro x
    constructor
    · rintro ⟨r, hr, hrx⟩
      change a (x 0) - b (x 1) = r • (c • gEuInv v₀) at hrx
      refine ⟨r * c, mul_pos hr hc, ?_⟩
      rw [← hdiff x, hrx, map_smul, hgEu_vE, smul_smul]
    · rintro ⟨r, hr, hrx⟩
      refine ⟨r / c, div_pos hr hc, ?_⟩
      apply gEu_injective
      rw [map_smul, hgEu_vE, hdiff x, hrx, smul_smul, div_mul_cancel₀ _ (ne_of_gt hc)]
  have hseteq : (Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1))
        (c • gEuInv v₀) ∩ Work.Surf.sqBdry)
      = gEuInv '' (rayMeetP (grbDiff a b) v₀ ∩ Work.Drive.sqBoxBdry) := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨hrm, hbd⟩
      exact ⟨gEu x, ⟨(hmem x).mp hrm, (gEu_mem_sqBoxBdry).mp hbd⟩, gEuInv_gEu x⟩
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨(hmem (gEuInv p)).mpr (by rwa [gEu_gEuInv]),
        (gEu_mem_sqBoxBdry).mp (by rwa [gEu_gEuInv])⟩
  have hinj : Function.Injective gEuInv := by
    intro x y h
    have h2 : gEu (gEuInv x) = gEu (gEuInv y) := by rw [h]
    rwa [gEu_gEuInv x, gEu_gEuInv y] at h2
  refine ⟨c • gEuInv v₀, ?_, hnorm, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : gEu (c • gEuInv v₀) = 0 := by rw [h, map_zero]
    rw [hgEu_vE] at h1
    exact hv₀ ((smul_eq_zero.mp h1).resolve_left (ne_of_gt hc))
  · rw [hseteq]
    exact hfin.image _
  · intro x hx hrm hcor
    exact hcorner (gEu x) ((gEu_mem_sqBoxBdry).mp hx) ((hmem x).mp hrm) hcor
  · intro x hx hrm
    have hx' : gEu x ∈ Work.Drive.sqBoxBdry := (gEu_mem_sqBoxBdry).mp hx
    have hr' : gEu x ∈ rayMeetP (grbDiff a b) v₀ := (hmem x).mp hrm
    have hxy0 : (gEu x).1 = x 0 := congrArg Prod.fst (gEu_apply x)
    have hxy1 : (gEu x).2 = x 1 := congrArg Prod.snd (gEu_apply x)
    constructor
    · intro h1
      have h := (htranss (gEu x) hx' hr').1 (by rw [gEu_apply]; exact h1)
      rw [hxy0] at h
      intro h0
      rw [← gCross_eu (deriv a (x 0)) (c • gEuInv v₀), ← gDeriv_eu ha (x 0), hgEu_vE,
        cross2_smul_right] at h0
      exact h ((mul_eq_zero.mp h0).resolve_left (ne_of_gt hc))
    · intro h1
      have h := (htranss (gEu x) hx' hr').2 (by rw [gEu_apply]; exact h1)
      rw [hxy1] at h
      intro h0
      rw [← gCross_eu (deriv b (x 1)) (c • gEuInv v₀), ← gDeriv_eu hb (x 1), hgEu_vE,
        cross2_smul_right] at h0
      exact h ((mul_eq_zero.mp h0).resolve_left (ne_of_gt hc))
  · rw [hseteq, Set.InjOn.ncard_image]
    · exact hodd
    · exact fun x _ y _ h => hinj h

/-! ## The main theorem -/

/-- **A good ray direction for the difference map of two chords, with an odd boundary count.**
For two chords `a`, `b` (`Work.Drive.IsChord`, `C¹`) satisfying `hint` and `htrans` there is a
direction `v ≠ 0` for which the difference map `x ↦ a (x 0) - b (x 1)` on the square

* is dominated by `v` on the boundary (`‖a (x 0) - b (x 1)‖ < ‖v‖` for `x ∈ sqBdry`, a harmless
  normalisation),
* meets the ray `{r • v : 0 < r}` in finitely many boundary points, none of them a corner of the
  square (`hcorner`),
* meets it transversally: at such a point the derivative of `a` along the face `x 1 ∈ {0,1}` (resp. of
  `b` along the face `x 0 ∈ {0,1}`) is not parallel to `v`,
* and in an **odd** number of boundary points. -/
theorem exists_good_ray_boundary_odd {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    (htrans : ∀ s t : ℝ, s ∈ Set.Ioo (0:ℝ) 1 → t ∈ Set.Ioo (0:ℝ) 1 → a s = b t →
      Work.Drive.det2 (deriv a s) (deriv b t) ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      (∀ x ∈ Work.Surf.sqBdry, ‖a (x 0) - b (x 1)‖ < ‖v‖) ∧
      (Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1)) v ∩
        Work.Surf.sqBdry).Finite ∧
      (∀ x ∈ Work.Surf.sqBdry, x ∈ Work.Surf.rayMeet
          (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) v →
        ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1))) ∧
      (∀ x ∈ Work.Surf.sqBdry, x ∈ Work.Surf.rayMeet
          (fun y : EuclideanSpace ℝ (Fin 2) => a (y 0) - b (y 1)) v →
        ((x 1 = 0 ∨ x 1 = 1) → Work.Drive.det2 (deriv a (x 0)) v ≠ 0) ∧
        ((x 0 = 0 ∨ x 0 = 1) → Work.Drive.det2 (deriv b (x 1)) v ≠ 0)) ∧
      Odd ((Work.Surf.rayMeet (fun x : EuclideanSpace ℝ (Fin 2) => a (x 0) - b (x 1)) v ∩
        Work.Surf.sqBdry : Set (EuclideanSpace ℝ (Fin 2))).ncard) := by
  have haC : ContDiff ℝ 1 a := ha.contDiff
  have hbC : ContDiff ℝ 1 b := hb.contDiff
  have hde2 : det2 (a 0) (b 0) ≠ 0 := det2_start_ne_zero ha hb hint
  have hS : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 →
      Work.Drive.straightChord (a 0) s = Work.Drive.straightChord (b 0) t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖Work.Drive.straightChord (a 0) s‖ < 1 :=
    hint_straightChords ha.start hb.start hde2
  obtain ⟨v₀, hv₀bad, hv₀ne⟩ := exists_notMem_grbBad haC hbC
  simp only [grbBad, Set.mem_union, not_or] at hv₀bad
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩ := hv₀bad
  -- the transversality input for `grb_level_odd`
  have htr : ∀ t ∈ Set.Ico (0:ℝ) 1, (∃ k : ℤ,
      grbLift a b haC hbC hint t - (Complex.arg (gToC v₀) / (2 * Real.pi)) = (k : ℝ)) →
      deriv (grbLift a b haC hbC hint) t ≠ 0 := by
    intro t ht hk
    have hL : ((grbLift a b haC hbC hint t : ℝ) : UnitAddCircle) = gDir v₀ := by
      obtain ⟨k, hk'⟩ := hk
      rw [show grbLift a b haC hbC hint t
        = Complex.arg (gToC v₀) / (2 * Real.pi) + (k : ℝ) by linarith]
      rw [AddCircle.coe_add, show (((k : ℝ)) : UnitAddCircle) = 0 from ?_, add_zero]
      · rfl
      · rw [show (k : ℝ) = k • (1:ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period (1:ℝ),
          zsmul_zero]
    have hlev : grbDir a b (t : UnitAddCircle) = gDir v₀ := by
      rw [← grbLift_lifts haC hbC hint t, hL]
    exact deriv_grbLift_ne_zero_of_cross2 haC hbC hint
      (cross2_ne_of_notMem_gTanCone hA ((grbDir_eq_gDir_iff hint hv₀ne t).mp hlev))
  -- the level set: finiteness and parity
  have hfinlev : ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle)
      = ((Complex.arg (gToC v₀) / (2 * Real.pi) : ℝ) : UnitAddCircle)} : Set ℝ).Finite :=
    grb_level_finite haC hbC hint (Complex.arg (gToC v₀) / (2 * Real.pi)) htr
  have hlevEq : ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = gDir v₀} : Set ℝ)
      = {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle)
          = ((Complex.arg (gToC v₀) / (2 * Real.pi) : ℝ) : UnitAddCircle)} := by
    ext t
    rw [show gDir v₀ = ((Complex.arg (gToC v₀) / (2 * Real.pi) : ℝ) : UnitAddCircle) from rfl]
  have hdegodd : Odd (grbDeg a b haC hbC hint) := by
    rw [grbDeg_eq_straight a b ha hb hint hS]
    exact grbStraightDeg_odd (a 0) (b 0) ha.start hb.start hde2 hS
  have hoddlev : Odd (Set.ncard
      ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = gDir v₀} : Set ℝ)) := by
    rw [hlevEq]
    exact (grb_level_odd haC hbC hint (Complex.arg (gToC v₀) / (2 * Real.pi)) htr).mpr hdegodd
  have hfinlev' : ({t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle)
      = gDir v₀} : Set ℝ).Finite := by
    rw [hlevEq]; exact hfinlev
  -- transport to the product model
  have hoddP : Odd ((rayMeetP (grbDiff a b) v₀ ∩ Work.Drive.sqBoxBdry : Set (ℝ × ℝ)).ncard) := by
    rw [ncard_rayMeetP_eq a b hint hv₀ne]; exact hoddlev
  have hfinP : (rayMeetP (grbDiff a b) v₀ ∩ Work.Drive.sqBoxBdry : Set (ℝ × ℝ)).Finite := by
    rw [rayMeetP_inter_eq_image a b hint hv₀ne]
    exact Set.Finite.image _ hfinlev'
  -- no corner ray-meets
  have hcornerP : ∀ p ∈ Work.Drive.sqBoxBdry, p ∈ rayMeetP (grbDiff a b) v₀ →
      ¬ ((p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 0 ∨ p.2 = 1)) := by
    rintro p hp hray ⟨h1, h2⟩
    obtain ⟨u, hu, rfl⟩ := sqPar_surjOn hp
    obtain ⟨r, hr, hru⟩ := hray
    have hcd := sqPar_corner_data hu
    have huc : u ∈ ({0, 1/4, 1/2, 3/4} : Set ℝ) := by
      have hcase : sqPar u = (0,0) ∨ sqPar u = (1,0) ∨ sqPar u = (1,1) ∨ sqPar u = (0,1) := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact Or.inl (Prod.ext h1 h2)
        · exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))
        · exact Or.inr (Or.inl (Prod.ext h1 h2))
        · exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))
      rcases hcase with h | h | h | h
      · rw [(hcd.1).mp h]; simp
      · rw [(hcd.2.1).mp h]; simp
      · rw [(hcd.2.2.1).mp h]; simp
      · rw [(hcd.2.2.2).mp h]; simp
    refine hF (mem_gCornerSet_of_corner (g := grbCurveR a b) huc ⟨r, hr, ?_⟩)
    rw [grbCurveR, grbCurve_coe]; exact hru
  -- the face transversality
  have htransP : ∀ p ∈ Work.Drive.sqBoxBdry, p ∈ rayMeetP (grbDiff a b) v₀ →
      ((p.2 = 0 ∨ p.2 = 1) → cross2 (deriv (fun s => gEu (a s)) p.1) v₀ ≠ 0) ∧
      ((p.1 = 0 ∨ p.1 = 1) → cross2 (deriv (fun t => gEu (b t)) p.2) v₀ ≠ 0) := by
    rintro p hp hray
    obtain ⟨u, hu, rfl⟩ := sqPar_surjOn hp
    obtain ⟨r, hr, hru⟩ := hray
    constructor
    · intro h2
      rcases h2 with h2 | h2
      · have hp2 : grbDiff a b ((sqPar u).1, (0:ℝ)) = grbDiff a b (sqPar u) := by
          rw [show ((sqPar u).1, (0:ℝ)) = sqPar u from Prod.ext rfl h2.symm]
        have hray' : ∃ s : ℝ, 0 < s ∧ fBot a b (sqPar u).1 = s • v₀ := ⟨r, hr, hp2.trans hru⟩
        have h := cross2_ne_of_notMem_gTanCone hB hray'
        have h3 : cross2 (r • v₀) (deriv (fun s => gEu (a s)) (sqPar u).1) ≠ 0 := by
          simpa only [fBot, deriv_fBot, hp2, hru] using h
        exact cross2_ne_of_smul_left h3
      · have hp2 : grbDiff a b ((sqPar u).1, (1:ℝ)) = grbDiff a b (sqPar u) := by
          rw [show ((sqPar u).1, (1:ℝ)) = sqPar u from Prod.ext rfl h2.symm]
        have hray' : ∃ s : ℝ, 0 < s ∧ fTop a b (sqPar u).1 = s • v₀ := ⟨r, hr, hp2.trans hru⟩
        have h := cross2_ne_of_notMem_gTanCone hC hray'
        have h3 : cross2 (r • v₀) (deriv (fun s => gEu (a s)) (sqPar u).1) ≠ 0 := by
          simpa only [fTop, deriv_fTop, hp2, hru] using h
        exact cross2_ne_of_smul_left h3
    · intro h1
      rcases h1 with h1 | h1
      · have hp1 : grbDiff a b ((0:ℝ), (sqPar u).2) = grbDiff a b (sqPar u) := by
          rw [show ((0:ℝ), (sqPar u).2) = sqPar u from Prod.ext h1.symm rfl]
        have hray' : ∃ s : ℝ, 0 < s ∧ fLft a b (sqPar u).2 = s • v₀ := ⟨r, hr, hp1.trans hru⟩
        have h := cross2_ne_of_notMem_gTanCone hD hray'
        have h3 : cross2 (r • v₀) (- deriv (fun t => gEu (b t)) (sqPar u).2) ≠ 0 := by
          simpa only [fLft, deriv_fLft, hp1, hru] using h
        exact cross2_ne_of_smul_left_neg h3
      · have hp1 : grbDiff a b ((1:ℝ), (sqPar u).2) = grbDiff a b (sqPar u) := by
          rw [show ((1:ℝ), (sqPar u).2) = sqPar u from Prod.ext h1.symm rfl]
        have hray' : ∃ s : ℝ, 0 < s ∧ fRgt a b (sqPar u).2 = s • v₀ := ⟨r, hr, hp1.trans hru⟩
        have h := cross2_ne_of_notMem_gTanCone hE hray'
        have h3 : cross2 (r • v₀) (- deriv (fun t => gEu (b t)) (sqPar u).2) ≠ 0 := by
          simpa only [fRgt, deriv_fRgt, hp1, hru] using h
        exact cross2_ne_of_smul_left_neg h3
  obtain ⟨c, hc, hnorm⟩ := exists_large_scale ha hb hv₀ne
  exact euclidean_transfer haC hbC hv₀ne c hc hnorm hfinP hcornerP htransP hoddP


end

end Work.Surf.ChordN
