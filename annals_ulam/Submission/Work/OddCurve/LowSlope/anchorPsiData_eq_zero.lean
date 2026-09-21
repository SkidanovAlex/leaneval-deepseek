import Mathlib
import Submission.Work.OddCurve.LowSlope.chord_eq_radial
import Submission.Work.OddCurve.LowSlope.radon_data_interface
import Submission.Work.OddCurve.LowSlope.Defs
import Submission.Work.OddCurve.LowSlope.radon_centroid_identity
import Submission.Work.OddCurve.LowSlope.radon_data_eq_centIntegral_weak
import Submission.Work.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub

/-!
# The second Radon datum of the anchor vanishes where the bump does

This is the companion of `Work.OddCurve.LowSlope.anchorPhiData_eq_ballData`: on a range of slopes
where the bump `h` and its derivative vanish, the centroid moment equation `(B) = 0` of the anchor
curve identifies the *second* Radon datum of the anchor body with `0`.  The proof is the centroid
part of Prop. `workHARD1` (`radon_data_eq_centIntegral_weak`) together with the identity
`momentB = centIntegral` of the low-slope regime.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- A linear function is concave on any interval. -/
private lemma concaveOn_const_mul (s A B : ℝ) :
    ConcaveOn ℝ (Set.Icc A B) (fun t : ℝ => s * t) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  have h : a * (s * x) + b * (s * y) = s * (a * x + b * y) := by ring
  linarith

/-- A linear function is convex on any interval. -/
private lemma convexOn_const_mul (s A B : ℝ) :
    ConvexOn ℝ (Set.Icc A B) (fun t : ℝ => s * t) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x _ y _ a b _ _ hab
  simp only [smul_eq_mul]
  have h : s * (a * x + b * y) = a * (s * x) + b * (s * y) := by ring
  linarith

/-- **The chord (concavity) bound at two points.**  A concave function on `[A,B]` dominates the
linear interpolation of its endpoint values. -/
private lemma concave_two_point_bound {F : ℝ → ℝ} {A B : ℝ} (hAB : A < B)
    (hF : ConcaveOn ℝ (Set.Icc A B) F) {t : ℝ} (ht : t ∈ Set.Ioo A B) :
    (B - t) * F A / (B - A) + (t - A) * F B / (B - A) ≤ F t := by
  have hden : 0 < B - A := sub_pos.mpr hAB
  have hla : 0 < (B - t) / (B - A) := div_pos (sub_pos.mpr ht.2) hden
  have hmu : 0 < (t - A) / (B - A) := div_pos (sub_pos.mpr ht.1) hden
  have hsum : (B - t) / (B - A) + (t - A) / (B - A) = 1 := by
    field_simp
    ring
  have hpt : (B - t) / (B - A) * A + (t - A) / (B - A) * B = t := by
    field_simp
    ring
  have hle := hF.2 ⟨le_rfl, hAB.le⟩ ⟨hAB.le, le_rfl⟩ hla.le hmu.le hsum
  simp only [smul_eq_mul] at hle
  rw [hpt] at hle
  calc (B - t) * F A / (B - A) + (t - A) * F B / (B - A)
      = (B - t) / (B - A) * F A + (t - A) / (B - A) * F B := by ring
    _ ≤ F t := hle

theorem anchorPsiData_eq_zero (n : ℕ) (hn : 1 ≤ n) {h X Y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h X Y (ρ u * u))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hzero : ∀ s ∈ Set.Icc a b, h s = 0)
    (hder0 : ∀ s ∈ Set.Icc a b, deriv h s = 0)
    (hB : ∀ s ∈ Set.Icc a b,
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0) :
    ∀ s ∈ Set.Ioo a b,
      Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
          ((Real.sqrt (1 + s ^ 2))⁻¹) = 0 := by
  intro s hs
  set f : ℝ → ℝ := Work.OddEnvelope.envelopeProfile h X Y with hf
  -- ## The slope and the cosine `c = (√(1+s²))⁻¹`
  have hspos : 0 < s := lt_of_lt_of_le ha hs.1.le
  have hsmem : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hs0 : h s = 0 := hzero s hsmem
  have hd0 : deriv h s = 0 := hder0 s hsmem
  have hsph : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := inv_pos.mpr hsph
  have hclt : (Real.sqrt (1 + s ^ 2))⁻¹ < 1 := by
    refine inv_lt_one_of_one_lt₀ ?_
    have h1 : (1 : ℝ) < 1 + s ^ 2 := by nlinarith [sq_pos_of_pos hspos]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h1
  have hcmem : (Real.sqrt (1 + s ^ 2))⁻¹ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hclt⟩
  have hcmem' : -((Real.sqrt (1 + s ^ 2))⁻¹) ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  -- ## The chord endpoints are the radial points
  have hchord := envelope_chord_eq_radial H hspos hs0 hρpos hgraph
  have hY : Y s = ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) := hchord.1
  have hX : X s = ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * ((Real.sqrt (1 + s ^ 2))⁻¹) := hchord.2
  have hmx : -(X s) ∈ Set.Ioo (-1 : ℝ) 1 := (Work.OddEnvelope.envelopeProfile_mem_Ioo H hspos).1
  have hy : Y s ∈ Set.Ioo (-1 : ℝ) 1 := (Work.OddEnvelope.envelopeProfile_mem_Ioo H hspos).2
  have hXpos : 0 < X s := H.toChordCurve_x.pos hspos
  have hYpos : 0 < Y s := H.toChordCurve_y.pos hspos
  have hxy : -(X s) < Y s := by linarith
  have hfy : f (Y s) = s * Y s := by
    have h1 := Work.OddEnvelope.envelopeProfile_root_right H hspos
    rw [hs0, add_zero] at h1
    rw [hf]; exact h1
  have hfx : f (-(X s)) = s * X s := by
    have h1 := Work.OddEnvelope.envelopeProfile_root_left H hspos
    rw [hs0, add_zero] at h1
    rw [hf, h1]; ring
  -- ## The uniqueness of the chord roots
  have hconc : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f := by
    rw [hf]; exact Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hf0 : f 0 = 1 := by rw [hf]; exact Work.OddEnvelope.envelopeProfile_zero
  have ht1 : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [← hY]; exact ⟨hYpos, H.toChordCurve_y.lt_one hspos⟩
  have ht2 : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) ∈
      Set.Ioo (-1 : ℝ) 0 := by
    have he : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(X s) := by
      rw [hX]; ring
    rw [he]; exact ⟨hmx.1, by linarith⟩
  have hrootR : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = s * t → t = Y s := by
    intro t ht hft
    have hfa : f (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹)) =
        s * (ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹)) := by
      rw [← hY]; exact hfy
    have h := eq_linear_unique_pos hconc hf0 ht1 hfa t ht hft
    rw [hY]; exact h
  have hrootL : ∀ t ∈ Set.Ioo (-1 : ℝ) 0, f t = -(s * t) → t = -(X s) := by
    intro t ht hft
    have he : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(X s) := by
      rw [hX]; ring
    have hfa : f (ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹))) =
        -(s * (ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)))) := by
      rw [he, hfx]; ring
    have h := eq_linear_unique_neg hconc hf0 ht2 hfa t ht hft
    rw [he] at h; exact h
  -- ## The monotonicity of `u ↦ ρ u * u` gives the derivative condition
  have hderivn : ∀ u ∈ Set.Ioo (-((Real.sqrt (1 + s ^ 2))⁻¹)) ((Real.sqrt (1 + s ^ 2))⁻¹),
      0 ≤ ρ u + u * deriv ρ u := by
    intro u hu
    have hu1 : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1, hclt], by linarith [hu.2, hclt]⟩
    have hmono' : MonotoneOn (fun v : ℝ => ρ v * v)
        (Set.Ioo (-((Real.sqrt (1 + s ^ 2))⁻¹)) ((Real.sqrt (1 + s ^ 2))⁻¹)) :=
      hρmono.monotoneOn.mono (fun v hv => ⟨by linarith [hv.1, hclt], by linarith [hv.2, hclt]⟩)
    have h1 : 0 ≤ derivWithin (fun v : ℝ => ρ v * v)
        (Set.Ioo (-((Real.sqrt (1 + s ^ 2))⁻¹)) ((Real.sqrt (1 + s ^ 2))⁻¹)) u :=
      hmono'.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hu)] at h1
    have hρd : DifferentiableAt ℝ ρ u :=
      (hρsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hu1)
    have hder : deriv (fun v : ℝ => ρ v * v) u = deriv ρ u * u + ρ u := by
      change deriv (fun v : ℝ => ρ v * id v) u = deriv ρ u * u + ρ u
      rw [deriv_fun_mul hρd differentiableAt_id]; simp
    rw [hder] at h1
    linarith
  -- ## The radial points sweep the chord
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) ∈
        Set.Ioo (-(X s)) (Y s) := by
    intro ν hν
    have hcm : (Real.sqrt (1 + s ^ 2))⁻¹ * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [hν.1, hcpos, hclt], by nlinarith [hν.2, hcpos, hclt]⟩
    have hlt1 : -((Real.sqrt (1 + s ^ 2))⁻¹) < (Real.sqrt (1 + s ^ 2))⁻¹ * ν := by
      nlinarith [hcpos, hν.1]
    have hlt2 : (Real.sqrt (1 + s ^ 2))⁻¹ * ν < (Real.sqrt (1 + s ^ 2))⁻¹ := by
      nlinarith [hcpos, hν.2]
    have h1 : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) <
        ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) :=
      hρmono hcmem' hcm hlt1
    have h2 : ρ ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) * ((Real.sqrt (1 + s ^ 2))⁻¹ * ν) <
        ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) :=
      hρmono hcm hcmem hlt2
    have hx' : -(X s) = ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) := by
      rw [hX]; ring
    rw [hx', hY]
    exact ⟨h1, h2⟩
  -- ## Positivity of the radicand on the chord
  have hradpos : ∀ t ∈ Set.Ioo (-(X s)) (Y s), 0 < rad0 f s t := by
    intro t ht
    have h1 := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
      (Work.OddEnvelope.concaveOn_envelopeProfile H) hspos t ht
    simpa [rad0, hs0] using h1
  -- ## Integrability of the two section integrands
  have hfcontBig : ContinuousOn f (Set.Icc (-1 : ℝ) 1) := by
    rw [hf]; exact Work.OddEnvelope.continuousOn_envelopeProfile' H
  have hfcont : ContinuousOn f (Set.Icc (-(X s)) (Y s)) :=
    hfcontBig.mono (fun x hx => ⟨le_of_lt (lt_of_lt_of_le hmx.1 hx.1),
      le_of_lt (lt_of_le_of_lt hx.2 hy.2)⟩)
  have hdcont : ContinuousOn (deriv f) (Set.Icc (-(X s)) (Y s)) := by
    have h0 : ContinuousOn (deriv (Work.OddEnvelope.envelopeProfile h X Y)) (Set.Ioo (-1 : ℝ) 1) :=
      (Work.OddEnvelope.envelopeProfile_contDiffOn H).continuousOn_deriv_of_isOpen
        isOpen_Ioo (by norm_num)
    rw [hf]
    exact h0.mono (fun x hx => ⟨lt_of_lt_of_le hmx.1 hx.1, lt_of_le_of_lt hx.2 hy.2⟩)
  have hRcont : ContinuousOn (fun t : ℝ => rad0 f s t) (Set.Icc (-(X s)) (Y s)) := by
    have h1 : ContinuousOn (fun t : ℝ => f t ^ 2) (Set.Icc (-(X s)) (Y s)) := hfcont.pow 2
    have h2 : ContinuousOn (fun t : ℝ => (s * t) ^ 2) (Set.Icc (-(X s)) (Y s)) :=
      ((continuous_const.mul continuous_id).continuousOn).pow 2
    have heq : (fun t : ℝ => rad0 f s t) = fun t : ℝ => f t ^ 2 - (s * t) ^ 2 := by
      funext t; simp only [rad0]
    rw [heq]
    exact h1.sub h2
  -- the second integrand is continuous on the closed interval
  have hI2 : IntervalIntegrable (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
      volume (-(X s)) (Y s) := by
    have hcont : ContinuousOn (fun t : ℝ => t * rad0 f s t ^ (n - 1) * Real.sqrt (rad0 f s t))
        (Set.uIcc (-(X s)) (Y s)) := by
      rw [Set.uIcc_of_le hxy.le]
      exact (continuousOn_id.mul (hRcont.pow (n - 1))).mul (Real.continuous_sqrt.comp_continuousOn hRcont)
    exact hcont.intervalIntegrable
  -- the first integrand: dominated by an inverse-square-root singularity
  have hXY : 0 < Y s + X s := by linarith
  have hconcI : ConcaveOn ℝ (Set.Icc (-(X s)) (Y s)) f :=
    (Work.OddEnvelope.concaveOn_envelopeProfile H).subset
      (fun t ht => ⟨le_of_lt (lt_of_lt_of_le hmx.1 ht.1), le_of_lt (lt_of_le_of_lt ht.2 hy.2)⟩)
      (convex_Icc _ _)
  have hgC : ConcaveOn ℝ (Set.Icc (-(X s)) (Y s)) (fun t : ℝ => f t - s * t) :=
    hconcI.sub (convexOn_const_mul s _ _)
  have hhC : ConcaveOn ℝ (Set.Icc (-(X s)) (Y s)) (fun t : ℝ => f t + s * t) :=
    hconcI.add (concaveOn_const_mul s _ _)
  have hc1 : 0 < 2 * s * X s / (Y s + X s) := by positivity
  have hc2 : 0 < 2 * s * Y s / (Y s + X s) := by positivity
  have hg_low : ∀ t ∈ Set.Ioo (-(X s)) (Y s),
      (2 * s * X s / (Y s + X s)) * (Y s - t) ≤ f t - s * t := by
    intro t ht
    have hb := concave_two_point_bound hxy hgC ht
    have h1 : f (-(X s)) - s * (-(X s)) = 2 * s * X s := by rw [hfx]; ring
    have h2 : f (Y s) - s * Y s = 0 := by rw [hfy]; ring
    rw [h1, h2] at hb
    have h3 : Y s - (-(X s)) = Y s + X s := by ring
    rw [h3] at hb
    simp only [mul_zero, zero_div, add_zero] at hb
    have h4 : (Y s - t) * (2 * s * X s) / (Y s + X s) =
        (2 * s * X s / (Y s + X s)) * (Y s - t) := by ring
    linarith [hb, h4]
  have hh_low : ∀ t ∈ Set.Ioo (-(X s)) (Y s),
      (2 * s * Y s / (Y s + X s)) * (t + X s) ≤ f t + s * t := by
    intro t ht
    have hb := concave_two_point_bound hxy hhC ht
    have h1 : f (-(X s)) + s * (-(X s)) = 0 := by rw [hfx]; ring
    have h2 : f (Y s) + s * Y s = 2 * s * Y s := by rw [hfy]; ring
    rw [h1, h2] at hb
    have h3 : Y s - (-(X s)) = Y s + X s := by ring
    have h4 : t - (-(X s)) = t + X s := by ring
    rw [h3, h4] at hb
    simp only [mul_zero, zero_div, zero_add] at hb
    have h5 : (t + X s) * (2 * s * Y s) / (Y s + X s) =
        (2 * s * Y s / (Y s + X s)) * (t + X s) := by ring
    linarith [hb, h5]
  have hR_low : ∀ t ∈ Set.Ioo (-(X s)) (Y s),
      (2 * s * X s / (Y s + X s)) * (Y s - t) * ((2 * s * Y s / (Y s + X s)) * (t + X s))
        ≤ rad0 f s t := by
    intro t ht
    have h1 := hg_low t ht
    have h2 := hh_low t ht
    have hpos2 : 0 ≤ (2 * s * Y s / (Y s + X s)) * (t + X s) :=
      mul_nonneg hc2.le (by linarith [ht.1])
    have hpos1 : 0 ≤ f t - s * t := le_trans (mul_nonneg hc1.le (by linarith [ht.2])) h1
    have hfact : rad0 f s t = (f t - s * t) * (f t + s * t) := by
      simp only [rad0]; ring
    rw [hfact]
    exact mul_le_mul h1 h2 hpos2 hpos1
  obtain ⟨T, hT⟩ := isCompact_Icc.exists_bound_of_continuousOn hRcont
  have hTnonneg : 0 ≤ T := le_trans (norm_nonneg _) (hT (Y s) ⟨hxy.le, le_rfl⟩)
  have hcoeffcont : ContinuousOn (fun t : ℝ => t * f t * (f t - t * deriv f t))
      (Set.Icc (-(X s)) (Y s)) :=
    (continuousOn_id.mul hfcont).mul (hfcont.sub (continuousOn_id.mul hdcont))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcoeffcont
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC (Y s) ⟨hxy.le, le_rfl⟩)
  set K : ℝ := C * (max T 1) ^ (n - 1) *
    (Real.sqrt (2 * s * X s / (Y s + X s)))⁻¹ *
    (Real.sqrt (2 * s * Y s / (Y s + X s)))⁻¹ with hK
  have hbound : ∀ t ∈ Set.Ioo (-(X s)) (Y s),
      ‖t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)‖
        ≤ K * ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹) := by
    intro t ht
    have hRpos : 0 < rad0 f s t := hradpos t ht
    have hcoeff : ‖t * f t * (f t - t * deriv f t)‖ ≤ C := hC t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hTt : rad0 f s t ≤ max T 1 := by
      have h1 := hT t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg hRpos.le] at h1
      exact le_trans h1 (le_max_left T 1)
    have hpow : rad0 f s t ^ (n - 1) ≤ (max T 1) ^ (n - 1) :=
      pow_le_pow_left₀ hRpos.le hTt (n - 1)
    have hRlow := hR_low t ht
    have hpl : 0 ≤ (2 * s * X s / (Y s + X s)) * (Y s - t) :=
      mul_nonneg hc1.le (by linarith [ht.2])
    have hsqrt_low : Real.sqrt (2 * s * X s / (Y s + X s)) * Real.sqrt (Y s - t) *
        (Real.sqrt (2 * s * Y s / (Y s + X s)) * Real.sqrt (t + X s)) ≤
        Real.sqrt (rad0 f s t) := by
      have h := Real.sqrt_le_sqrt hRlow
      rw [Real.sqrt_mul hpl, Real.sqrt_mul hc1.le (Y s - t),
        Real.sqrt_mul hc2.le (t + X s)] at h
      exact h
    have hPpos : 0 < Real.sqrt (2 * s * X s / (Y s + X s)) * Real.sqrt (Y s - t) *
        (Real.sqrt (2 * s * Y s / (Y s + X s)) * Real.sqrt (t + X s)) := by
      have h1 : 0 < Real.sqrt (2 * s * X s / (Y s + X s)) := Real.sqrt_pos.mpr hc1
      have h2 : 0 < Real.sqrt (Y s - t) := Real.sqrt_pos.mpr (by linarith [ht.2])
      have h3 : 0 < Real.sqrt (2 * s * Y s / (Y s + X s)) := Real.sqrt_pos.mpr hc2
      have h4 : 0 < Real.sqrt (t + X s) := Real.sqrt_pos.mpr (by linarith [ht.1])
      positivity
    have hrecip : 1 / Real.sqrt (rad0 f s t) ≤
        1 / (Real.sqrt (2 * s * X s / (Y s + X s)) * Real.sqrt (Y s - t) *
          (Real.sqrt (2 * s * Y s / (Y s + X s)) * Real.sqrt (t + X s))) :=
      one_div_le_one_div_of_le hPpos hsqrt_low
    have hfinal : 1 / (Real.sqrt (2 * s * X s / (Y s + X s)) * Real.sqrt (Y s - t) *
          (Real.sqrt (2 * s * Y s / (Y s + X s)) * Real.sqrt (t + X s)))
        = (Real.sqrt (2 * s * X s / (Y s + X s)))⁻¹ *
          (Real.sqrt (2 * s * Y s / (Y s + X s)))⁻¹ *
          ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹) := by
      simp only [one_div, mul_inv]
      ring
    rw [hfinal] at hrecip
    have hnorm : ‖t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)‖
        = ‖t * f t * (f t - t * deriv f t)‖ * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t) := by
      have h1 : ‖t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1)‖
          = ‖t * f t * (f t - t * deriv f t)‖ * rad0 f s t ^ (n - 1) := by
        rw [norm_mul]
        congr 1
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hRpos.le (n - 1))]
      have h2 : ‖Real.sqrt (rad0 f s t)‖ = Real.sqrt (rad0 f s t) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hRpos)]
      rw [norm_div, h1, h2]
    rw [hnorm]
    calc ‖t * f t * (f t - t * deriv f t)‖ * rad0 f s t ^ (n - 1) / Real.sqrt (rad0 f s t)
        = (‖t * f t * (f t - t * deriv f t)‖ * rad0 f s t ^ (n - 1)) *
            (1 / Real.sqrt (rad0 f s t)) := by rw [div_eq_mul_inv, one_div]
      _ ≤ (C * (max T 1) ^ (n - 1)) *
            ((Real.sqrt (2 * s * X s / (Y s + X s)))⁻¹ *
              (Real.sqrt (2 * s * Y s / (Y s + X s)))⁻¹ *
              ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹)) := by
          refine mul_le_mul (mul_le_mul hcoeff hpow (pow_nonneg hRpos.le _) hCnonneg)
            hrecip (by positivity) (by positivity)
      _ = K * ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹) := by
          rw [hK]; ring
  -- the dominating function is interval integrable
  have hmaj : IntervalIntegrable
      (fun t : ℝ => K * ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹))
      volume (-(X s)) (Y s) := by
    have h0 : IntervalIntegrable
        (fun y : ℝ => (Real.sqrt (y - (-(X s))))⁻¹ * (Real.sqrt (Y s - y))⁻¹)
        volume (-(X s)) (Y s) :=
      Commons.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub (t := -(X s)) (x := Y s) hxy
    refine (h0.const_mul K).congr ?_
    intro t _
    show K * ((Real.sqrt (t - (-(X s))))⁻¹ * (Real.sqrt (Y s - t))⁻¹)
      = K * ((Real.sqrt (t + X s))⁻¹ * (Real.sqrt (Y s - t))⁻¹)
    rw [show t - (-(X s)) = t + X s by ring]
  -- measurability of the integrand on the (half-open) interval
  have hAcont : ContinuousOn
      (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)) (Set.Ioo (-(X s)) (Y s)) := by
    have hnum : ContinuousOn
        (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1))
        (Set.Ioo (-(X s)) (Y s)) := by
      have h1 : ContinuousOn f (Set.Ioo (-(X s)) (Y s)) :=
        hfcont.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      have h2 : ContinuousOn (deriv f) (Set.Ioo (-(X s)) (Y s)) :=
        hdcont.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      have h3 : ContinuousOn (fun t : ℝ => rad0 f s t) (Set.Ioo (-(X s)) (Y s)) :=
        hRcont.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      exact (continuousOn_id.mul h1).mul (h1.sub (continuousOn_id.mul h2)) |>.mul (h3.pow (n - 1))
    refine hnum.div ?_ ?_
    · exact Real.continuous_sqrt.comp_continuousOn
        (hRcont.mono (fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
    · intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (hradpos t ht))
  have hsm : AEStronglyMeasurable
      (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)) (volume.restrict (Set.uIoc (-(X s)) (Y s))) := by
    have h1 : AEMeasurable
        (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) (volume.restrict (Set.Ioo (-(X s)) (Y s))) :=
      hAcont.aemeasurable measurableSet_Ioo
    have h2 : AEMeasurable
        (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
          Real.sqrt (rad0 f s t)) (volume.restrict (Set.uIoc (-(X s)) (Y s))) := by
      rw [Set.uIoc_of_le hxy.le, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
      exact h1
    exact h2.aestronglyMeasurable
  have hI1 : IntervalIntegrable
      (fun t : ℝ => t * f t * (f t - t * deriv f t) * rad0 f s t ^ (n - 1) /
        Real.sqrt (rad0 f s t)) volume (-(X s)) (Y s) := by
    refine hmaj.mono_fun' hsm ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hxy.le] at ht
    rcases eq_or_lt_of_le ht.2 with heq | hlt
    · subst heq
      have hzero : rad0 f s (Y s) = 0 := by
        simp only [rad0]; rw [hfy]; ring
      rw [hzero, Real.sqrt_zero, div_zero, norm_zero, sub_self, Real.sqrt_zero, inv_zero,
        mul_zero, mul_zero]
    · exact hbound t ⟨ht.1, hlt⟩
  -- ## The centroid integral vanishes
  have hcent : centIntegral n f X Y s = 0 := by
    have hB0 : Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0 :=
      hB s hsmem
    rw [momentB_eq_centIntegral (n := n) (h := h)
      (f := Work.OddEnvelope.envelopeProfile h X Y) (x := X) (y := Y) hs0 hd0] at hB0
    exact hB0
  -- ## The crux identity (Prop. `workHARD1`, centroid part) and the conclusion
  have hfC1 : ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) := by
    rw [hf]; exact (Work.OddEnvelope.envelopeProfile_contDiffOn H).of_le (by norm_num)
  have hweak := radon_data_eq_centIntegral_weak n hn f ρ X Y s hspos hfcontBig hfC1 hρpos hρsm
    hρmono hgraph hderivn hY.symm (by rw [hX]; ring) hmem hmx hy hfy hfx hrootR hrootL hxy
    hradpos hI1 hI2
  have hmain : Work.OddRadon.sphereArea (2 * n - 2) *
      (∫ ν in (-1 : ℝ)..1, (1 - ν ^ 2) ^ (n - 1) *
        ((fun u : ℝ => u * ρ u ^ (2 * n + 1)) ((Real.sqrt (1 + s ^ 2))⁻¹ * ν)) /
          Real.sqrt (1 - ν ^ 2)) =
      (2 * (n : ℝ) + 1) * ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        centIntegral n f X Y s := hweak
  rw [radonProfile_eq_natpow n hn (fun u : ℝ => u * ρ u ^ (2 * n + 1)) hcpos, hmain, hcent]
  ring

end

end Work.OddCurve.LowSlope
