import Mathlib
import Submission.Work.OddVolterra.Free.envProfileFreeTips
import Submission.Work.OddVolterra.Free.envelopeRight_contDiffOn_Ioo
import Submission.Work.OddVolterra.Free.radon_data_eq_inertiaIntegral_gen
import Submission.Work.OddVolterra.Free.radon_data_eq_centIntegral_gen
import Submission.Work.OddVolterra.Free.intervalIntegrable_radonIntegrands_gen
import Submission.Work.OddCurve.LowSlope.cent_inertia_of_datum_ball
import Submission.Work.OddCurve.LowSlope.refConst_eq_inertia

/-!
# The centroid and inertia conditions from the ball's Radon datum, free tips

Free-tip analogue of `Work.OddCurve.LowSlope.cent_inertia_of_datum_ball`
(`Submission/Work/OddCurve/LowSlope/cent_inertia_of_datum_ball.lean`, proved): if the two Radon
data of the radial function `ρ` are the ball's on `c ≥ (√(1+(1-2τ)²))⁻¹` and `ρ` traces the
untruncated (free-tip) envelope profile `envProfileFree h x y`, then on every slope
`s ≤ 1 - 2τ` the *centroid* condition `centIntegral = 0` and the *inertia* condition
`(1+s²)^{3/2} · inertiaIntegral = ballInertiaConst n` hold.

The proof is the source's, with the two new inputs that replace the tip normalisation:

* `Work.OddVolterra.Free.envProfileFree_chord_eq_radial` — the chord of a vanishing crop is the
  radial chord `ρ c · c = y s`, `ρ (-c) · (-c) = -(x s)`;
* `Work.OddVolterra.Free.contDiffOn_one_envProfileFree` — the untruncated profile is `C¹` on the
  (now possibly wider-than-`(-1,1)`) section interval;

together with the general-interval Radon identities
`radon_data_eq_inertiaIntegral_gen` / `radon_data_eq_centIntegral_gen` and the general-interval
integrability `intervalIntegrable_radonIntegrands_gen`.
-/

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {h x y : ℝ → ℝ}

/-- `1 ≤ ∞` in the smoothness order (`∞` is `↑(⊤ : ℕ∞)`, so this is `1 ≤ ⊤`). -/
private lemma one_le_smoothness_infty : (1 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)

/-- **The untruncated envelope profile is `C¹` on a section interval.** -/
theorem contDiffOn_one_envProfileFree (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y) {c : ℝ}
    (hc : 0 < c) : ContDiffOn ℝ 1 (envProfileFree h x y) (Set.Ioo (-(x c)) (y c)) := by
  intro t ht
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioo.mem_nhds ht)]
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · -- the left branch
    have hmem : t ∈ Set.Ioo (-(x c)) 0 := ⟨ht.1, hlt⟩
    have hev : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeLeft h x := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
      exact envProfileFree_of_neg hu
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) (x c), ∃ σ : ℝ, 0 < σ ∧ x σ = z :=
      fun z hz => exists_slope_x_lt H hc hz
    have hCinf : ContDiffOn ℝ ∞ (Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x)
        (Set.Ioo (0 : ℝ) (x c)) :=
      envelopeRight_contDiffOn_Ioo H.smooth_x H.x_deriv_neg H.smooth_h.neg hsurj
    have hneg : ContDiffOn ℝ ∞ (fun u : ℝ => -u) (Set.Ioo (-(x c)) 0) := by fun_prop
    have hcomp : ContDiffOn ℝ ∞
        (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))
        (Set.Ioo (-(x c)) 0) :=
      hCinf.comp hneg (fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    have heq2 : (fun u : ℝ => Work.OddEnvelope.envelopeRight (Work.OddEnvelope.negH h) x (-u))
        = Work.OddEnvelope.envelopeLeft h x := by
      funext u
      exact (Work.OddEnvelope.envelopeLeft_eq_negH h x u).symm
    rw [heq2] at hcomp
    exact (hcomp.contDiffAt (isOpen_Ioo.mem_nhds hmem)).of_le one_le_smoothness_infty
  · -- at `0` the profile is the semicircle
    subst heq
    have hmem : (0 : ℝ) ∈ Set.Ioo (-Work.OddEnvelope.tStar) Work.OddEnvelope.tStar :=
      ⟨by linarith [Work.OddEnvelope.tStar_pos], Work.OddEnvelope.tStar_pos⟩
    have h1 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
    have hev : envProfileFree h x y =ᶠ[𝓝 (0 : ℝ)] Work.OddEnvelope.semicircle := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem, isOpen_Ioo.mem_nhds h1] with u hu hu1
      rw [envProfileFree_eq_envelopeProfile hu1]
      exact Work.OddCurve.Free.envelopeProfile_eq_semicircle_free H hu
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact (Work.OddEnvelope.Semicircle.contDiffOn_semicircle.contDiffAt
      (isOpen_Ioo.mem_nhds h1)).of_le le_top
  · -- the right branch
    have hmem : t ∈ Set.Ioo (0 : ℝ) (y c) := ⟨hgt, ht.2⟩
    have hev : envProfileFree h x y =ᶠ[𝓝 t] Work.OddEnvelope.envelopeRight h y := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with u hu
      exact envProfileFree_of_pos hu.1
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hsurj : ∀ z ∈ Set.Ioo (0 : ℝ) (y c), ∃ σ : ℝ, 0 < σ ∧ y σ = z :=
      fun z hz => exists_slope_y_lt H hc hz
    have hCinf : ContDiffOn ℝ ∞ (Work.OddEnvelope.envelopeRight h y) (Set.Ioo (0 : ℝ) (y c)) :=
      envelopeRight_contDiffOn_Ioo H.smooth_y H.y_deriv_neg H.smooth_h hsurj
    exact (hCinf.contDiffAt (isOpen_Ioo.mem_nhds hmem)).of_le one_le_smoothness_infty

/-- **The centroid and inertia conditions from the ball's Radon datum, free tips.** -/
theorem cent_inertia_of_datum_ball_free (n : ℕ) (hn : 1 ≤ n) {h x y ρ : ℝ → ℝ}
    (H : Work.OddCurve.Free.IsEnvelopeCurveFree h x y)
    (hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddVolterra.Free.envProfileFree h x y (ρ u * u))
    (hball : ∀ c : ℝ, (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau →
      Work.OddCurve.LowSlope.centIntegral n (Work.OddVolterra.Free.envProfileFree h x y) x y s = 0 ∧
        (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
          Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y)
            x y s = Work.OddCurve.LowSlope.ballInertiaConst n := by
  intro s hs hsle
  obtain ⟨bY, hbYpos, hbY⟩ := H.y_tendsto_free
  obtain ⟨bX, hbXpos, hbX⟩ := H.x_tendsto_free
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcpos : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by positivity
  have hclt : (Real.sqrt (1 + s ^ 2))⁻¹ < 1 := by
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [hs, sq_nonneg s])
  have hcge : (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤
      (Real.sqrt (1 + s ^ 2))⁻¹ := by
    have hτpos : 0 < 1 - 2 * Work.OddEnvelope.tau := by norm_num [Work.OddEnvelope.tau]
    have hs2 : s ^ 2 ≤ (1 - 2 * Work.OddEnvelope.tau) ^ 2 := by nlinarith [hs.le, hsle, hτpos]
    have hsq : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    exact (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity))
      (Real.sqrt_pos.mpr (by positivity))).mpr hsq
  obtain ⟨hPhi, hPsi⟩ := hball ((Real.sqrt (1 + s ^ 2))⁻¹) hcge hclt
  have hPhi' : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2)) ((Real.sqrt (1 + s ^ 2))⁻¹) =
      Work.OddCurve.LowSlope.ballPhiData n ((Real.sqrt (1 + s ^ 2))⁻¹) := hPhi
  have hPsi' : Work.OddRadon.radonProfile (2 * n + 1)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) ((Real.sqrt (1 + s ^ 2))⁻¹) = 0 := hPsi
  have hz : h s = 0 := hzero s hs hsle
  -- the section interval, now possibly wider than `(-1,1)`
  have hc₀pos : 0 < s / 2 := by linarith
  have hc₀s : s / 2 < s := by linarith
  have hfx_c : x s < x (s / 2) := H.strictAntiOn_x hc₀pos hs hc₀s
  have hfy_c : y s < y (s / 2) := H.strictAntiOn_y hc₀pos hs hc₀s
  have hfC1 : ContDiffOn ℝ 1 (Work.OddVolterra.Free.envProfileFree h x y)
      (Set.Ioo (-(x (s / 2))) (y (s / 2))) :=
    contDiffOn_one_envProfileFree H hc₀pos
  have hmx : -(x s) ∈ Set.Ioo (-(x (s / 2))) (y (s / 2)) :=
    ⟨by linarith, by linarith [H.pos_x hs, H.pos_y hc₀pos]⟩
  have hy : y s ∈ Set.Ioo (-(x (s / 2))) (y (s / 2)) :=
    ⟨by linarith [H.pos_x hc₀pos, H.pos_y hs], hfy_c⟩
  -- the derivative of `ρ u · u` is non-negative on the section parameter range
  have hderivn : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) ((Real.sqrt (1 + s ^ 2))⁻¹),
      0 ≤ ρ u + u * deriv ρ u := by
    intro u hu
    have hu1 : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1, hclt], by linarith [hu.2, hclt]⟩
    have hdw : 0 ≤ derivWithin (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) u :=
      hρmono.monotoneOn.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hu1)] at hdw
    have hρd : HasDerivAt ρ (deriv ρ u) u :=
      ((hρsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hu1)).hasDerivAt
    have hd : HasDerivAt (fun u : ℝ => ρ u * u) (ρ u + u * deriv ρ u) u := by
      have h := hρd.mul (hasDerivAt_id u)
      have hfun : (fun u : ℝ => ρ u * u) = ρ * id := by funext u; rw [Pi.mul_apply]; simp
      rw [hfun]
      refine h.congr_deriv ?_
      simp only [id_eq, mul_one]
      ring
    rw [hd.deriv] at hdw
    exact hdw
  -- the chord of a vanishing crop is the radial chord
  have hchord := Work.OddVolterra.Free.envProfileFree_chord_eq_radial H hbY hbYpos hbX hbXpos
    hs hz hρpos hρsm.continuousOn hρmono hgraph
  have hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) = y s := hchord.1.symm
  have hend_x : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(x s) := by
    rw [hchord.2]
    ring
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) ∈
        Set.Ioo (-(x s)) (y s) := by
    intro ν hν
    have hcu : (Real.sqrt (1 + s ^ 2))⁻¹ * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [hcpos, hclt, hν.1], by nlinarith [hcpos, hclt, hν.2]⟩
    have hcmem : (Real.sqrt (1 + s ^ 2))⁻¹ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hclt⟩
    have hmcmem : -((Real.sqrt (1 + s ^ 2))⁻¹) ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by linarith, by linarith⟩
    have hlt1 : (Real.sqrt (1 + s ^ 2))⁻¹ * ν < (Real.sqrt (1 + s ^ 2))⁻¹ := by
      nlinarith [hcpos, hν.2]
    have hlt2 : -((Real.sqrt (1 + s ^ 2))⁻¹) < (Real.sqrt (1 + s ^ 2))⁻¹ * ν := by
      nlinarith [hcpos, hν.1]
    constructor
    · have hh : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) <
          ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) :=
        hρmono hmcmem hcu hlt2
      rwa [hend_x] at hh
    · have hh : ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) <
          ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) :=
        hρmono hcu hcmem hlt1
      rwa [hend_y] at hh
  have hfy : Work.OddVolterra.Free.envProfileFree h x y (y s) = s * y s := by
    have h := (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y
      H.x_deriv_neg H.y_deriv_neg (fun u hu => H.pos_x hu) (fun u hu => H.pos_y hu)).1 s hs
    rw [h, hz, add_zero]
  have hfx : Work.OddVolterra.Free.envProfileFree h x y (-(x s)) = s * x s := by
    have h := (Work.OddVolterra.Free.envProfileFree_chord h x y H.smooth_x H.smooth_y
      H.x_deriv_neg H.y_deriv_neg (fun u hu => H.pos_x hu) (fun u hu => H.pos_y hu)).2 s hs
    rw [h, hz, add_zero]
    ring
  have hxy : -(x s) < y s := by
    have h1 := H.pos_x hs
    have h2 := H.pos_y hs
    linarith
  have hrad : ∀ t ∈ Set.Ioo (-(x s)) (y s),
      0 < Work.OddCurve.LowSlope.rad0 (Work.OddVolterra.Free.envProfileFree h x y) s t := by
    intro t ht
    have hpos' := Work.OddVolterra.Free.envProfileFree_sub_sq_pos H hs t ht
    rwa [Work.OddCurve.LowSlope.rad0_eq_rad h (Work.OddVolterra.Free.envProfileFree h x y) hz t]
      at hpos'
  obtain ⟨hintA, hintC, hintB, hintD⟩ :=
    Work.OddVolterra.Free.intervalIntegrable_radonIntegrands_gen n hn hs hfC1 hρpos hρsm hgraph
      hderivn hend_y hend_x hmem hmx hy
  have hcruxI := Work.OddVolterra.Free.radon_data_eq_inertiaIntegral_gen n hn hs hfC1 hρpos hρsm
    hρmono hgraph hderivn hend_y hend_x hmem hmx hy hfy hfx hxy hrad hintA hintB
  have hcruxC := Work.OddVolterra.Free.radon_data_eq_centIntegral_gen n hn hs hfC1 hρpos hρsm
    hρmono hgraph hderivn hend_y hend_x hmem hmx hy hfy hfx hxy hrad hintC hintD
  have hballVol_pos : 0 < Work.OddCurve.LowSlope.ballVol (2 * n - 1) := by
    have h1 : 0 < Work.OddRadon.sphereArea (2 * n - 2) := Work.OddRadon.sphereArea_pos _
    have h2 : Work.OddRadon.sphereArea (2 * n - 2) =
        (2 * (n : ℝ) - 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) := by
      rw [Work.OddCurve.LowSlope.sphereArea_eq_ballVol (2 * n - 2)]
      have hcast : (((2 * n - 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) - 1 := by
        have h2 : 2 * n - 2 = 2 * (n - 1) := by omega
        rw [h2, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn]; ring
      have hidx : 2 * n - 2 + 1 = 2 * n - 1 := by omega
      rw [hcast, hidx]
    have h3 : (0 : ℝ) < 2 * (n : ℝ) - 1 := by
      have h' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact pos_of_mul_pos_right (h2 ▸ h1) h3.le
  refine ⟨?_, ?_⟩
  · have hzero2 : (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
        Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.centIntegral n (Work.OddVolterra.Free.envProfileFree h x y) x y s
        = 0 := by
      rw [← hcruxC, hPsi']
    have hne : (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
        Real.sqrt (1 + s ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by positivity) (ne_of_gt hballVol_pos)) (ne_of_gt hspos)
    exact (mul_eq_zero.mp hzero2).resolve_left hne
  · have hesq : ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 = (1 + s ^ 2)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have heq : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
        Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y)
          x y s
        = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
          Work.OddCurve.LowSlope.ballInertiaConst n * ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 := by
      rw [← hcruxI, hPhi']
      exact Work.OddCurve.LowSlope.ballPhiData_eq n hn hcpos (le_of_lt hclt)
    have hD : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) ≠ 0 :=
      mul_ne_zero (by positivity) (ne_of_gt hballVol_pos)
    have hmain : Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y)
          x y s
        = Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹ := by
      have h5 : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
          (Real.sqrt (1 + s ^ 2) *
            Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y)
              x y s)
          = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
            (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by
        calc (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
              (Real.sqrt (1 + s ^ 2) *
                Work.OddCurve.LowSlope.inertiaIntegral n
                  (Work.OddVolterra.Free.envProfileFree h x y) x y s)
            = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
                Real.sqrt (1 + s ^ 2) *
                Work.OddCurve.LowSlope.inertiaIntegral n
                  (Work.OddVolterra.Free.envProfileFree h x y) x y s := by ring
          _ = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
                Work.OddCurve.LowSlope.ballInertiaConst n * ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 := heq
          _ = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
                (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by
              rw [hesq]; ring
      exact mul_left_cancel₀ hD h5
    calc (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
          Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddVolterra.Free.envProfileFree h x y)
            x y s
        = (1 + s ^ 2) * (Real.sqrt (1 + s ^ 2) *
            Work.OddCurve.LowSlope.inertiaIntegral n
              (Work.OddVolterra.Free.envProfileFree h x y) x y s) := by ring
      _ = (1 + s ^ 2) * (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by
          rw [hmain]
      _ = Work.OddCurve.LowSlope.ballInertiaConst n := by field_simp

end

end Work.OddVolterra.Free
