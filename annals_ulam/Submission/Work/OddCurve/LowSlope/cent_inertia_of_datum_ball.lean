import Mathlib
import Submission.Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_Ioo
import Submission.Work.OddCurve.LowSlope.semicircle_sections
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo
import Submission.Work.OddCurve.LowSlope.chord_eq_radial
import Submission.Work.OddCurve.LowSlope.intervalIntegrable_radonIntegrands
import Submission.Work.OddRadon.sphereArea_pos

namespace Work.OddCurve.LowSlope

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 2000000 in
theorem cent_inertia_of_datum_ball (n : ℕ) (hn : 1 ≤ n) {h x y ρ : ℝ → ℝ}
    (H : Work.OddEnvelope.IsEnvelopeCurve h x y)
    (hzero : ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau → h s = 0)
    (hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u)
    (hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1))
    (hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1))
    (hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ρ u * Real.sqrt (1 - u ^ 2) = Work.OddEnvelope.envelopeProfile h x y (ρ u * u))
    (hball : ∀ c : ℝ, (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c → c < 1 →
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
        Work.OddCurve.LowSlope.radonPsi n ρ c = 0) :
    ∀ s : ℝ, 0 < s → s ≤ 1 - 2 * Work.OddEnvelope.tau →
      Work.OddCurve.LowSlope.centIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s = 0 ∧
        (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
          Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s =
            Work.OddCurve.LowSlope.ballInertiaConst n := by
  intro s hs hsle
  let c : ℝ := (Real.sqrt (1 + s ^ 2))⁻¹
  have hspos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcpos : 0 < c := by change 0 < (Real.sqrt (1 + s ^ 2))⁻¹; positivity
  have hclt : c < 1 := by
    change (Real.sqrt (1 + s ^ 2))⁻¹ < 1
    refine inv_lt_one_of_one_lt₀ ?_
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 + s ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [hs, sq_nonneg s])
  have hcpos' : 0 < (Real.sqrt (1 + s ^ 2))⁻¹ := by change 0 < c; exact hcpos
  have hclt' : (Real.sqrt (1 + s ^ 2))⁻¹ < 1 := by change c < 1; exact hclt
  have hcge : (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ c := by
    change (Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2))⁻¹ ≤ (Real.sqrt (1 + s ^ 2))⁻¹
    have hτpos : 0 < 1 - 2 * Work.OddEnvelope.tau := by norm_num [Work.OddEnvelope.tau]
    have hs2 : s ^ 2 ≤ (1 - 2 * Work.OddEnvelope.tau) ^ 2 := by nlinarith [hs.le, hsle, hτpos]
    have hsq : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (1 + (1 - 2 * Work.OddEnvelope.tau) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    exact (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))).mpr hsq
  obtain ⟨hPhi, hPsi⟩ := hball c hcge hclt
  have hPhi' : Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u ^ 2 * ρ u ^ (2 * n + 2))
      ((Real.sqrt (1 + s ^ 2))⁻¹) = Work.OddCurve.LowSlope.ballPhiData n ((Real.sqrt (1 + s ^ 2))⁻¹) := hPhi
  have hPsi' : Work.OddRadon.radonProfile (2 * n + 1) (fun u : ℝ => u * ρ u ^ (2 * n + 1))
      ((Real.sqrt (1 + s ^ 2))⁻¹) = 0 := hPsi
  have hz : h s = 0 := hzero s hs hsle
  have hfC1 : ContDiffOn ℝ 1 (Work.OddEnvelope.envelopeProfile h x y) (Set.Ioo (-1 : ℝ) 1) :=
    (Work.OddEnvelope.envelopeProfile_contDiffOn H).of_le (by norm_num)
  have hderivn : ∀ u ∈ Set.Ioo (-(Real.sqrt (1 + s ^ 2))⁻¹) ((Real.sqrt (1 + s ^ 2))⁻¹),
      0 ≤ ρ u + u * deriv ρ u := by
    intro u hu
    have hu1 : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1, hclt'], by linarith [hu.2, hclt']⟩
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
  have hchord := Work.OddCurve.LowSlope.envelope_chord_eq_radial H hs hz hρpos hgraph
  have hend_y : ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) = y s := hchord.1.symm
  have hend_x : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) = -(x s) := by
    rw [hchord.2]; ring
  have hmem : ∀ ν ∈ Set.Ioo (-1 : ℝ) 1,
      ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) ∈ Set.Ioo (-(x s)) (y s) := by
    intro ν hν
    have hcu : (Real.sqrt (1 + s ^ 2))⁻¹ * ν ∈ Set.Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [hcpos', hclt', hν.1], by nlinarith [hcpos', hclt', hν.2]⟩
    have hcmem : (Real.sqrt (1 + s ^ 2))⁻¹ ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hclt'⟩
    have hmcmem : -((Real.sqrt (1 + s ^ 2))⁻¹) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hlt1 : (Real.sqrt (1 + s ^ 2))⁻¹ * ν < (Real.sqrt (1 + s ^ 2))⁻¹ := by nlinarith [hcpos', hν.2]
    have hlt2 : -((Real.sqrt (1 + s ^ 2))⁻¹) < (Real.sqrt (1 + s ^ 2))⁻¹ * ν := by nlinarith [hcpos', hν.1]
    constructor
    · have hh : ρ (-((Real.sqrt (1 + s ^ 2))⁻¹)) * (-((Real.sqrt (1 + s ^ 2))⁻¹)) <
          ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) :=
        hρmono hmcmem hcu hlt2
      rwa [hend_x] at hh
    · have hh : ρ (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) * (((Real.sqrt (1 + s ^ 2))⁻¹) * ν) <
          ρ ((Real.sqrt (1 + s ^ 2))⁻¹) * ((Real.sqrt (1 + s ^ 2))⁻¹) :=
        hρmono hcu hcmem hlt1
      rwa [hend_y] at hh
  have hmemxy := Work.OddEnvelope.envelopeProfile_mem_Ioo H hs
  have hmx : -(x s) ∈ Set.Ioo (-1 : ℝ) 1 := hmemxy.1
  have hy : y s ∈ Set.Ioo (-1 : ℝ) 1 := hmemxy.2
  have hfy : Work.OddEnvelope.envelopeProfile h x y (y s) = s * y s := by
    rw [Work.OddEnvelope.envelopeProfile_root_right H hs, hz, add_zero]
  have hfx : Work.OddEnvelope.envelopeProfile h x y (-(x s)) = s * x s := by
    rw [Work.OddEnvelope.envelopeProfile_root_left H hs, hz, add_zero]
    ring
  have hconc := Work.OddEnvelope.strictConcaveOn_envelopeProfile H
  have hf0 : Work.OddEnvelope.envelopeProfile h x y 0 = 1 := Work.OddEnvelope.envelopeProfile_zero
  have hyI : y s ∈ Set.Ioo (0 : ℝ) 1 := ⟨H.toChordCurve_y.pos hs, hy.2⟩
  have hmxI : -(x s) ∈ Set.Ioo (-1 : ℝ) 0 :=
    ⟨hmx.1, by have h' := H.toChordCurve_x.pos hs; linarith⟩
  have hxy : -(x s) < y s := by
    have h' := H.toChordCurve_x.pos hs; have h'' := H.toChordCurve_y.pos hs; linarith
  have huniqy : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Work.OddEnvelope.envelopeProfile h x y t = s * t → t = y s :=
    fun t ht hft => Work.OddCurve.LowSlope.eq_linear_unique_pos hconc hf0 hyI hfy t ht hft
  have huniqx : ∀ t ∈ Set.Ioo (-1 : ℝ) 0,
      Work.OddEnvelope.envelopeProfile h x y t = -(s * t) → t = -(x s) := by
    intro t ht hft
    exact Work.OddCurve.LowSlope.eq_linear_unique_neg hconc hf0 hmxI (by rw [hfx]; ring) t ht hft
  have hrad : ∀ t ∈ Set.Ioo (-(x s)) (y s),
      0 < Work.OddCurve.LowSlope.rad0 (Work.OddEnvelope.envelopeProfile h x y) s t := by
    intro t ht
    have hh := Work.OddEnvelope.envelopeProfile_sub_sq_pos H
      (Work.OddEnvelope.concaveOn_envelopeProfile H) hs t ht
    rw [hz] at hh
    simpa [Work.OddCurve.LowSlope.rad0] using hh
  obtain ⟨hintA, hintC, hintB, hintD⟩ :=
    Work.OddCurve.LowSlope.intervalIntegrable_radonIntegrands n hn hs hfC1 hρpos hρsm hgraph
      hderivn hend_y hend_x hmem hmx hy
  have hcruxI := Work.OddCurve.LowSlope.radon_data_eq_inertiaIntegral_Ioo n hn
    (Work.OddEnvelope.envelopeProfile h x y) ρ x y s hs hfC1 hρpos hρsm hρmono hgraph hderivn
    hend_y hend_x hmem hmx hy hfy hfx huniqy huniqx hxy hrad hintA hintB
  have hcruxC := Work.OddCurve.LowSlope.radon_data_eq_centIntegral_Ioo n hn
    (Work.OddEnvelope.envelopeProfile h x y) ρ x y s hs hfC1 hρpos hρsm hρmono hgraph hderivn
    hend_y hend_x hmem hmx hy hfy hfx huniqy huniqx hxy hrad hintC hintD
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
  · have hzero2 : (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.centIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s = 0 := by
      rw [← hcruxC, hPsi']
    have hne : (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by positivity) (ne_of_gt hballVol_pos)) (ne_of_gt hspos)
    exact (mul_eq_zero.mp hzero2).resolve_left hne
  · have hesq : ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 = (1 + s ^ 2)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have heq : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s
        = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
          Work.OddCurve.LowSlope.ballInertiaConst n * ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 := by
      rw [← hcruxI, hPhi']
      exact Work.OddCurve.LowSlope.ballPhiData_eq n hn hcpos' (le_of_lt hclt')
    have hD : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) ≠ 0 :=
      mul_ne_zero (by positivity) (ne_of_gt hballVol_pos)
    have hmain : Real.sqrt (1 + s ^ 2) *
        Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s
        = Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹ := by
      have h5 : (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
          (Real.sqrt (1 + s ^ 2) *
            Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s)
          = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
            (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by
        calc (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
              (Real.sqrt (1 + s ^ 2) *
                Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s)
            = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) * Real.sqrt (1 + s ^ 2) *
                Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s := by ring
          _ = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
                Work.OddCurve.LowSlope.ballInertiaConst n * ((Real.sqrt (1 + s ^ 2))⁻¹) ^ 2 := heq
          _ = (2 * (n : ℝ) + 2) * Work.OddCurve.LowSlope.ballVol (2 * n - 1) *
                (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by rw [hesq]; ring
      exact mul_left_cancel₀ hD h5
    calc (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) *
          Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s
        = (1 + s ^ 2) * (Real.sqrt (1 + s ^ 2) *
            Work.OddCurve.LowSlope.inertiaIntegral n (Work.OddEnvelope.envelopeProfile h x y) x y s) := by ring
      _ = (1 + s ^ 2) * (Work.OddCurve.LowSlope.ballInertiaConst n * (1 + s ^ 2)⁻¹) := by rw [hmain]
      _ = Work.OddCurve.LowSlope.ballInertiaConst n := by
          field_simp

end Work.OddCurve.LowSlope
