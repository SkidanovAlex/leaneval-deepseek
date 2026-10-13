import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.Elliptic.DivSinTermwise
import Submission.Work.Elliptic.sharp_hardy_pi
import Submission.Work.Elliptic.sin_l2_weight_bound
import Submission.Work.Elliptic.power_hardy_bounds
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary facts about the angular interval

Everything below is one-dimensional `θ`-calculus on `Iθ = [0, π/2]`.  The open interval
`(0, π/2)` differs from `Iθ` by two points, so almost-everywhere statements can be checked
on the open interval, where the slices are smooth. -/

/-- `sin(2θ) > 0` on `(0, π/2)`. -/
lemma pz_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The measure on `Iθ` only sees the open interval `(0, π/2)`. -/
lemma pz_restrict_Iθ :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

/-- A function continuous on the open interval `(0, π/2)` is almost everywhere strongly
measurable for the measure of `Iθ`. -/
lemma pz_aesm_of_cont {u : ℝ → ℝ} (hu : ContinuousOn u (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) := by
  rw [pz_restrict_Iθ]
  exact hu.aestronglyMeasurable measurableSet_Ioo

/-! ## Continuity of the slices and of the weights -/

/-- `Dth1` preserves `C^∞` on an open set. -/
lemma pz_contDiffOn_Dth1_of {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ContDiffOn ℝ ⊤ (Dth1 f) s :=
  ((show ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) s by fun_prop)).mul
    (hf.deriv_of_isOpen hs le_top)

/-- Iterates of `Dth1` preserve `C^∞` on an open set. -/
lemma pz_contDiffOn_Dth1Iter_of {s : Set ℝ} (hs : IsOpen s) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ f s) : ∀ m : ℕ, ContDiffOn ℝ ⊤ (Dth1Iter m f) s
  | 0 => by simpa using hf
  | (m + 1) => by
      simpa only [Dth1Iter_succ] using pz_contDiffOn_Dth1_of hs (pz_contDiffOn_Dth1Iter_of hs hf m)

/-- The angular quotient of a smooth slice is `C^∞` on `(0, π/2)`. -/
lemma pz_contDiffOn_SinQ {h : ℝ → ℝ} (hsm : SmoothSlice h) :
    ContDiffOn ℝ ⊤ (SinQ h) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  exact (hsm.mono hsub).div (by fun_prop) (fun x hx => ne_of_gt (pz_sin_two_pos hx))

/-- The weight `sin(2θ)^{-η/2}` is continuous on `(0, π/2)`. -/
lemma pz_cont_weight (z : ℝ) :
    ContinuousOn (fun θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  exact continuousOn_const.div
    (hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (pz_sin_two_pos hx))))
    (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (pz_sin_two_pos hx) _))

/-- The weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on `(0, π/2)`. -/
lemma pz_cont_Wt (α z : ℝ) :
    ContinuousOn (fun θ => Work.Spaces.Wt α z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact continuousOn_const.mul
    (hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (pz_sin_two_pos hx))))

/-- The slices `θ ↦ D_z^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`. -/
lemma pz_cont_DzIter_div (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ)
    (hv : Work.Spaces.VanishTheta Φ) (i : ℕ) (z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨hsm, -, -⟩ := DivSinSliceFacts Φ hΦ hv i z hz
  have hcont : ContinuousOn (fun θ => Work.Spaces.DzIter i Φ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩)
  refine (hcont.div (by fun_prop) (fun x hx => ne_of_gt (pz_sin_two_pos hx))).congr ?_
  intro θ hθ
  exact DivSinFactor Φ i z θ hθ

/-- The mixed slices `θ ↦ D_z^j D_θ^i (Φ/sin 2θ) z θ` are continuous on `(0, π/2)`. -/
lemma pz_cont_mixed_div (Φ : ℝ → ℝ → ℝ) (hΦ : Work.Spaces.SmoothNbhd Φ)
    (hv : Work.Spaces.VanishTheta Φ) (j i : ℕ) (z : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  obtain ⟨hsm, -, -⟩ := DivSinSliceFacts Φ hΦ hv j z hz
  have hcd : ContDiffOn ℝ ⊤ (Dth1Iter i (SinQ (fun θ => Work.Spaces.DzIter j Φ z θ)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    pz_contDiffOn_Dth1Iter_of isOpen_Ioo (pz_contDiffOn_SinQ hsm) i
  refine hcd.continuousOn.congr ?_
  intro θ hθ
  exact dtw_mixed_div_eq_Dth1Iter Φ hΦ j i z θ hz hθ

/-! ## The integral of a finite sum of nonnegative functions -/

/-- The integral of a finite sum of almost-everywhere nonnegative, almost-everywhere strongly
measurable functions is at most the sum of the integrals.  (`MeasureTheory.integral_finsetSum`
gives equality but requires every summand to be integrable; here no integrability is needed.) -/
theorem pz_integral_finsetSum_le {ι : Type*} (s : Finset ι) {μ : Measure ℝ} {f : ι → ℝ → ℝ}
    (hm : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) (hn : ∀ i ∈ s, 0 ≤ᵐ[μ] f i) :
    (∫ a, ∑ i ∈ s, f i a ∂μ) ≤ ∑ i ∈ s, ∫ a, f i a ∂μ := by
  by_cases h : ∀ i ∈ s, Integrable (f i) μ
  · rw [integral_finsetSum s h]
  · push_neg at h
    obtain ⟨i, hi, hni⟩ := h
    have hsum_nni : ¬ Integrable (fun a => ∑ j ∈ s, f j a) μ := by
      intro hsum
      refine hni (hsum.mono' (hm i hi) ?_)
      filter_upwards [(eventually_all_finset s).mpr hn] with a ha
      rw [Real.norm_of_nonneg (ha i hi)]
      exact Finset.single_le_sum (fun j hj => ha j hj) hi
    rw [integral_undef hsum_nni]
    exact Finset.sum_nonneg fun j hj => integral_nonneg_of_ae (hn j hj)

/-- Two-function form of `pz_integral_finsetSum_le`. -/
theorem pz_integral_add_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f)
    (hgm : AEStronglyMeasurable g μ) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ a, (f a + g a) ∂μ) ≤ (∫ a, f a ∂μ) + ∫ a, g a ∂μ := by
  have h := pz_integral_finsetSum_le (μ := μ) (s := Finset.univ)
    (f := fun i : Fin 2 => if i = 0 then f else g)
    (by intro i _; fin_cases i
        · simpa using hfm
        · simpa using hgm)
    (by intro i _; fin_cases i
        · simpa using hfn
        · simpa using hgn)
  simpa [Fin.sum_univ_two] using h

/-! ## A sorry-free weighted Hardy inequality

`Work.Elliptic.DivSinHardy` (which the termwise bounds `DivSinTermwise` rest on) is currently
`:= by sorry`, so a proof that calls it inherits `sorryAx`.  For that reason the inequality is
re-proved here, via the sharp weighted Hardy inequality `sharp_hardy_sin_two` and the `η = 0`
case of `sin_l2_weight_bound` (a Poincaré inequality for slices vanishing at `θ = 0`):

  `∫ h²/s^{2+η} ≤ 1/(1+η)² ∫ (h')²/s^η + C(∫h² + ∫(h')²)
              ≤ 1/(1+η)² ∫ (h')²/s^η + C(K₀+1) ∫ (h')²/s^η`,

the last step using `∫h² ≤ K₀∫(h')²` and the pointwise comparison `(h')² ≤ (h')²/s^η`
(valid because `0 < sin(2θ) ≤ 1` on `(0, π/2)`). -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
lemma pz_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Almost every `θ ∈ Iθ` is in the open interval. -/
lemma pz_ae_mem_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [pz_restrict_Iθ]
  exact ae_restrict_mem measurableSet_Ioo

/-- Substitution `T = 2u` in an interval integral. -/
lemma pz_comp_two (G : ℝ → ℝ) :
    (∫ T in (0 : ℝ)..Real.pi, G T) = 2 * ∫ u in (0 : ℝ)..(Real.pi / 2), G (2 * u) := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := Real.pi / 2)
    G (c := (2 : ℝ)) (by norm_num)
  rw [show (2 : ℝ) * 0 = 0 by ring, show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at h
  rw [h]
  simp only [smul_eq_mul]
  ring

/-- A set integral over `Icc 0 π` is an interval integral. -/
lemma pz_setIntegral_Icc_pi (φ : ℝ → ℝ) :
    (∫ θ in Set.Icc 0 Real.pi, φ θ) = ∫ θ in (0 : ℝ)..Real.pi, φ θ := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi by positivity)]

/-- An interval integral over `(0, π/2)` is a set integral over `Iθ`. -/
lemma pz_interval_eq_setIntegral_Iθ (φ : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), φ θ) = ∫ θ in Work.Spaces.Iθ, φ θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]

/-- The weighted Hardy inequality for the weight `sin(2θ)`, sorry-free (a stand-in for
`Work.Elliptic.DivSinHardy`, whose file is `:= by sorry`).

Proof.  The sharp weighted Hardy inequality `Work.Elliptic.sharp_hardy_pi` on `[0, π]` for the
weight `sin` is applied to the rescaled slice `F T = h (T/2)` (`T = 2θ` converts `sin T` into
`sin(2θ)` and `[0,π]` into `Iθ = [0, π/2]`), giving

  `A ≤ 1/(1+η)² B + C (∫h² + ∫(h')²)`,

where `A = ∫_{Iθ} h²/sin(2θ)^{2+η}`, `B = ∫_{Iθ} (h')²/sin(2θ)^η`; the sub-leading terms are
absorbed with `∫h² ≤ K₀∫(h')²` (`sin_l2_weight_bound` with `η = 0`) and the pointwise
comparison `(h')² ≤ (h')²/sin(2θ)^η` (valid because `0 < sin(2θ) ≤ 1` on `(0,π/2)`). -/
theorem pzHardy :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ → ℝ), SmoothSlice h → h 0 = 0 → h (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K * ∫ θ in Work.Spaces.Iθ,
            (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
  obtain ⟨C, hCpos, hpi⟩ :=
    sharp_hardy_pi Work.Spaces.eta Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
  obtain ⟨K0, hK0pos, hL2⟩ := sin_l2_weight_bound (η := 0) le_rfl zero_lt_one
  refine ⟨1 / (1 + Work.Spaces.eta) ^ 2 + C * (K0 + 1 / 4) + 1, by positivity, ?_⟩
  intro h hsm h0 hp
  -- the rescaled slice on `[0, π]`
  set F : ℝ → ℝ := fun T => h (T / 2) with hF
  have hFcd : ContDiffOn ℝ 1 F (Set.Icc 0 Real.pi) := by
    have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    have hmaps : Set.MapsTo (fun T : ℝ => T / 2) (Set.Icc 0 Real.pi) (Set.Icc 0 (Real.pi / 2)) :=
      fun T hT => ⟨by linarith [hT.1], by linarith [hT.2, Real.pi_pos]⟩
    have hc := (hsm.mono hsub).comp (by fun_prop) hmaps
    have h1 := hc.of_le (le_top : (1 : WithTop ℕ∞) ≤ ⊤)
    simpa only [hF, Function.comp_def] using h1
  have hF0 : F 0 = 0 := by simp only [hF, zero_div]; exact h0
  have hFpi : F Real.pi = 0 := by simp only [hF]; exact hp
  have hderiv : ∀ T : ℝ, deriv F T = deriv h (T / 2) / 2 := by
    intro T
    have hfe : F = (h <| (1 / 2 : ℝ) * ·) := by
      funext S
      simp only [hF]
      congr 1
      ring
    rw [hfe, deriv_comp_mul_left]
    simp only [smul_eq_mul]
    rw [show (1 / 2 : ℝ) * T = T / 2 by ring]
    ring
  -- the four substitutions `T = 2θ`
  have hsub_a : (∫ T in Set.Icc 0 Real.pi, F T ^ 2 / (Real.sin T) ^ (2 + Work.Spaces.eta))
      = 2 * ∫ θ in Work.Spaces.Iθ,
          h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) := by
    rw [pz_setIntegral_Icc_pi,
      pz_comp_two (fun T => F T ^ 2 / (Real.sin T) ^ (2 + Work.Spaces.eta))]
    congr 1
    rw [← pz_interval_eq_setIntegral_Iθ
      (fun θ => h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [hF, show (2 * u) / 2 = u by ring]
  have hsub_b : (∫ T in Set.Icc 0 Real.pi, (deriv F T) ^ 2 / (Real.sin T) ^ Work.Spaces.eta)
      = (1 / 2) * ∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [pz_setIntegral_Icc_pi,
      pz_comp_two (fun T => (deriv F T) ^ 2 / (Real.sin T) ^ Work.Spaces.eta)]
    rw [← pz_interval_eq_setIntegral_Iθ
      (fun θ => (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)]
    have hpt : ∀ u : ℝ, (deriv F (2 * u)) ^ 2 / (Real.sin (2 * u)) ^ Work.Spaces.eta
        = (1 / 4) * ((deriv h u) ^ 2 / (Real.sin (2 * u)) ^ Work.Spaces.eta) := by
      intro u
      rw [hderiv (2 * u), show (2 * u) / 2 = u by ring]
      ring
    have hcongr : (∫ u in (0 : ℝ)..(Real.pi / 2),
          (deriv F (2 * u)) ^ 2 / (Real.sin (2 * u)) ^ Work.Spaces.eta)
        = (1 / 4) * ∫ u in (0 : ℝ)..(Real.pi / 2),
            (deriv h u) ^ 2 / (Real.sin (2 * u)) ^ Work.Spaces.eta := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => hpt u
    rw [hcongr]
    ring
  have hsub_c : (∫ T in Set.Icc 0 Real.pi, F T ^ 2)
      = 2 * ∫ θ in Work.Spaces.Iθ, h θ ^ 2 := by
    rw [pz_setIntegral_Icc_pi, pz_comp_two (fun T => F T ^ 2)]
    congr 1
    rw [← pz_interval_eq_setIntegral_Iθ (fun θ => h θ ^ 2)]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [hF, show (2 * u) / 2 = u by ring]
  have hsub_d : (∫ T in Set.Icc 0 Real.pi, (deriv F T) ^ 2)
      = (1 / 2) * ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 := by
    rw [pz_setIntegral_Icc_pi, pz_comp_two (fun T => (deriv F T) ^ 2)]
    rw [← pz_interval_eq_setIntegral_Iθ (fun θ => (deriv h θ) ^ 2)]
    have hpt : ∀ u : ℝ, (deriv F (2 * u)) ^ 2 = (1 / 4) * (deriv h u) ^ 2 := by
      intro u
      rw [hderiv (2 * u), show (2 * u) / 2 = u by ring]
      ring
    have hcongr : (∫ u in (0 : ℝ)..(Real.pi / 2), (deriv F (2 * u)) ^ 2)
        = (1 / 4) * ∫ u in (0 : ℝ)..(Real.pi / 2), (deriv h u) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => hpt u
    rw [hcongr]
    ring
  have hAhpi := hpi F hFcd hF0 hFpi
  have hcoef : 4 / (Work.Spaces.eta + 1) ^ 2 = 4 / (1 + Work.Spaces.eta) ^ 2 := by ring
  rw [hcoef] at hAhpi
  rw [hsub_a, hsub_b, hsub_c, hsub_d] at hAhpi
  -- sub-leading terms
  have hsubIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
  have hC1out : ContDiffOn ℝ 1 h (Set.Icc 0 (Real.pi / 2)) := (hsm.mono hsubIcc).of_le le_top
  have hB : (∫ θ in Work.Spaces.Iθ, h θ ^ 2) ≤ K0 * ∫ θ in Work.Spaces.Iθ,
      (deriv h θ) ^ 2 := by
    have hh := hL2 h hC1out h0
    simpa only [Work.Spaces.Iθ, neg_zero, Real.rpow_zero, mul_one] using hh
  obtain ⟨Ch, hCh0, -, hChd⟩ :=
    power_hardy_bounds (by positivity : (0 : ℝ) < Real.pi / 2) hC1out h0
  have hIntG : IntegrableOn
      (fun θ => (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      Work.Spaces.Iθ := by
    have hcont : ContinuousOn (fun θ => (deriv h θ) ^ 2
        / (Real.sin (2 * θ)) ^ Work.Spaces.eta) (Set.Ioo 0 (Real.pi / 2)) := by
      have hsubIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
        fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
      have hder : ContDiffOn ℝ ⊤ (deriv h) (Set.Ioo 0 (Real.pi / 2)) :=
        (hsm.mono hsubIoo).deriv_of_isOpen isOpen_Ioo le_top
      exact (hder.continuousOn.pow 2).div
        (((by fun_prop : Continuous fun θ : ℝ => Real.sin (2 * θ)).continuousOn).rpow_const
          (fun x hx => Or.inl (ne_of_gt (pz_sin_two_pos hx))))
        (fun x hx => ne_of_gt (Real.rpow_pos_of_pos (pz_sin_two_pos hx) _))
    refine integrableOn_of_rpow_majorant Work.Spaces.eta_pos.le Work.Spaces.eta_lt_one
      (C := Ch ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta) (by positivity) hcont ?_
    intro θ hθ
    have hs0 : 0 < Real.sin (2 * θ) := pz_sin_two_pos hθ
    have hmaj := Work.Spaces.sin_rpow_le_majorant Work.Spaces.eta θ Work.Spaces.eta_pos
      ⟨hθ.1.le, hθ.2.le⟩
    have hd : |deriv h θ| ≤ Ch := hChd θ hθ
    have hd2 : (deriv h θ) ^ 2 ≤ Ch ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rwa [sq_abs] at h
    have hinv : ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
          * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by
      rw [← Real.rpow_neg hs0.le Work.Spaces.eta]
      exact hmaj
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0.le _)), div_eq_mul_inv]
    calc (deriv h θ) ^ 2 * ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹
        ≤ Ch ^ 2 * ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ :=
          mul_le_mul_of_nonneg_right hd2 (inv_nonneg.mpr (Real.rpow_nonneg hs0.le _))
      _ ≤ Ch ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = Ch ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-Work.Spaces.eta) + (Real.pi / 2 - θ) ^ (-Work.Spaces.eta)) := by ring
  have hE : (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hIntG ?_
    filter_upwards [pz_ae_mem_Ioo] with θ hθ
    have hs0 : 0 < Real.sin (2 * θ) := pz_sin_two_pos hθ
    have hs1 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
      Real.rpow_le_one hs0.le (Real.sin_le_one _) Work.Spaces.eta_pos.le
    have hinv : 1 ≤ ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ :=
      (one_le_inv₀ (Real.rpow_pos_of_pos hs0 _)).mpr hs1
    calc (deriv h θ) ^ 2 = (deriv h θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (deriv h θ) ^ 2 * ((Real.sin (2 * θ)) ^ Work.Spaces.eta)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta := by rw [div_eq_mul_inv]
  -- final arithmetic
  have hA : (∫ θ in Work.Spaces.Iθ, h θ ^ 2 / (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
      ≤ 1 / (1 + Work.Spaces.eta) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        + C * (∫ θ in Work.Spaces.Iθ, h θ ^ 2)
        + C / 4 * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2) := by
    linear_combination (1 / 2) * hAhpi
  have h1 : C * (∫ θ in Work.Spaces.Iθ, h θ ^ 2) ≤ C * (K0 * ∫ θ in Work.Spaces.Iθ,
      (deriv h θ) ^ 2) := mul_le_mul_of_nonneg_left hB hCpos.le
  have h2 : C * (K0 * ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
      ≤ C * (K0 * (∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hK0pos.le) hCpos.le
  have h3 : C / 4 * (∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2)
      ≤ C / 4 * (∫ θ in Work.Spaces.Iθ,
          (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta) :=
    mul_le_mul_of_nonneg_left hE (by linarith [hCpos])
  have hBnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv h θ) ^ 2 / (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
    integral_nonneg_of_ae (pz_ae_mem_Ioo.mono fun θ hθ =>
      div_nonneg (sq_nonneg _) (Real.rpow_nonneg (pz_sin_two_nonneg ⟨hθ.1.le, hθ.2.le⟩) _))
  nlinarith [hA, h1, h2, h3, hBnn, hCpos.le, hK0pos.le]

/-- The per-slice termwise bounds: the same statement as `Work.Elliptic.DivSinTermwise`, but
derived here from the sorry-free Hardy inequality `pzHardy` (and the shared, sorry-free
`Work.Elliptic.DivSinIterUnif` for the higher angular derivatives), so that nothing in this
file depends on `Work.Elliptic.DivSinHardy` (which is `:= by sorry`) or on the Hardy
machinery of `sharp_hardy_sin_two`.  The assembly is the one of `DivSinTermwise`: apply
`dtw_SliceHardy` to each pure `D_z` summand and `dtw_SliceIter` to each mixed summand, after
identifying the `θ`-slices with `DivSinFactor`, `dtw_DthIter_slice_at`, `DivSinSliceIdent` and
`dtw_Dth1Iter_deriv_eq_mixed`. -/
theorem pzTermwise :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (Φ : ℝ → ℝ → ℝ),
      Work.Spaces.SmoothNbhd Φ → Work.Spaces.VanishTheta Φ → ∀ (z : ℝ), z ∈ Work.Spaces.Iz →
      (∀ i ∈ Finset.range 5,
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ C * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ∧ (∀ i ∈ Finset.Icc 1 4, ∀ j ∈ Finset.range 5, i + j ≤ 4 →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))) := by
  obtain ⟨K, hKpos, hHardy⟩ := pzHardy
  obtain ⟨C0, hC0pos, hIter⟩ := DivSinIterUnif
  refine ⟨max K C0, lt_of_lt_of_le hKpos (le_max_left K C0), ?_⟩
  intro α hα hα1 Φ hΦ hv z hz
  constructor
  · intro i hi
    obtain ⟨hsm, h0, hp⟩ := DivSinSliceFacts Φ hΦ hv i z hz
    have hslice := dtw_SliceHardy hHardy (fun θ => Work.Spaces.DzIter i Φ z θ) (Work.Spaces.w z) hsm h0 hp
    have hL : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i Φ z θ / Real.sin (2*θ)
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [dtw_ae_mem] with θ hθ
      rw [DivSinFactor Φ i z θ hθ]
    have hR : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.Spaces.DzIter i Φ z θ') θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [← dtw_deriv_DzIter_slice Φ hΦ i z θ hz hθ]
    rw [hL, hR]
    exact le_trans hslice (mul_le_mul_of_nonneg_right (le_max_left K C0)
      (integral_nonneg (fun θ => sq_nonneg _)))
  · intro i hi j hj hij
    obtain ⟨hsm, h0, hp⟩ := DivSinSliceFacts Φ hΦ hv j z hz
    have hslice := dtw_SliceIter hIter α hα hα1 (fun θ => Work.Spaces.DzIter j Φ z θ)
      (Work.Spaces.w z) hsm h0 hp i hi
    have hL : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Dth1Iter i (SinQ (fun θ' => Work.Spaces.DzIter j Φ z θ')) θ
              * (Work.Spaces.w z * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α / 2))))^2 := by
      apply integral_congr_ae
      filter_upwards [dtw_ae_mem] with θ hθ
      rw [dtw_mixed_div_eq_Dth1Iter Φ hΦ j i z θ hz hθ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    have hR1 : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.Spaces.DzIter j Φ z θ') θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta / 2)))^2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [← dtw_deriv_DzIter_slice Φ hΦ j z θ hz hθ]
    have hR2 : ∀ m ∈ Finset.Icc 1 i,
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (Dth1Iter m (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j Φ z θ'') θ') θ
              * (Work.Spaces.w z * (Real.sin (2*θ)) ^ (-(Work.Spaces.gam α / 2))))^2 := by
      intro m hm
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [dtw_Dth1Iter_deriv_eq_mixed Φ hΦ j m z θ hz hθ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    rw [hL, hR1, Finset.sum_congr rfl (fun m hm => hR2 m hm)]
    refine le_trans hslice (mul_le_mul_of_nonneg_right (le_max_right K C0) ?_)
    exact add_nonneg (integral_nonneg (fun θ => sq_nonneg _))
      (Finset.sum_nonneg (fun m _ => integral_nonneg (fun θ => sq_nonneg _)))

/-! ## The per-`z` comparison -/

/-- Per-`z` comparison of the whole `H^4` integrand of `Φ/sin(2θ)` with that of `∂_θΦ`,
assembled from the termwise bounds `DivSinTermwise`; the constant is independent of `α`, `Φ`, `z`.
`HkMem α 4 (pth Φ)` is assumed so that the right-hand integral is the honest one.
Outline: expand both sides as finite sums of the summands of `HkIntegrand` (the summands of the
left-hand side are integrable by `DivSinHkMemSlice`), apply `DivSinTermwise` to each summand, and
bound every right-hand summand by the full right-hand integrand via `sq_le_HkIntegrand_z` /
`sq_le_HkIntegrand_mixed` and `integral_mono_of_nonneg` (whose integrability hypothesis is
`HkMem α 4 (pth Φ)`). -/
theorem DivSinPerZ :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (Φ : ℝ → ℝ → ℝ),
      Work.Spaces.SmoothNbhd Φ → Work.Spaces.VanishTheta Φ →
      Work.Spaces.HkMem α 4 (Work.Spaces.pth Φ) → ∀ (z : ℝ), z ∈ Work.Spaces.Iz →
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth Φ) z θ) := by
  obtain ⟨C, hCpos, hTW⟩ := pzTermwise
  refine ⟨200 * C, by positivity, ?_⟩
  intro α hα hα1 Φ hΦ hv hmem z hz
  obtain ⟨hTWz1, hTWz2⟩ := hTW α hα hα1 Φ hΦ hv z hz
  -- the right-hand integral is honest and nonnegative
  have hRint_int : IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth Φ) z θ) Work.Spaces.Iθ :=
    hmem.1 z hz
  set Rint : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (Work.Spaces.pth Φ) z θ
    with hRint
  have hRint_nn : 0 ≤ Rint := by
    rw [hRint]
    exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 (Work.Spaces.pth Φ) z θ
  -- the summands of the two sums in `HkIntegrand`
  set u : ℝ → ℝ := fun θ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
    with hu
  set G1 : ℕ → ℝ → ℝ := fun i θ =>
    (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ * u θ) ^ 2 with hG1
  set G2 : ℕ → ℕ → ℝ → ℝ := fun i j θ =>
    if 1 ≤ i ∧ i + j ≤ 4 then
      (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
        * Work.Spaces.Wt α z θ) ^ 2
    else 0 with hG2
  -- the left-hand integrand is the sum of the two sums
  have hLdef : ∀ θ, Work.Spaces.HkIntegrand α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
      = (∑ i ∈ Finset.range 5, G1 i θ)
        + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ) := by
    intro θ
    have h45 : (4 : ℕ) + 1 = 5 := rfl
    simp only [Work.Spaces.HkIntegrand, hG1, hG2, hu, h45]
  -- continuity (hence a.e. strong measurability) of the summands
  have hG1_cont : ∀ i, ContinuousOn (G1 i) (Set.Ioo 0 (Real.pi / 2)) := by
    intro i
    have h1 := pz_cont_DzIter_div Φ hΦ hv i z hz
    have h2 := pz_cont_weight z
    have h3 : ContinuousOn (fun θ =>
        (Work.Spaces.DzIter i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) := (h1.mul h2).pow 2
    simpa only [hG1, hu] using h3
  have hG2_cont : ∀ i j, ContinuousOn (G2 i j) (Set.Ioo 0 (Real.pi / 2)) := by
    intro i j
    by_cases hcond : 1 ≤ i ∧ i + j ≤ 4
    · have h3 : ContinuousOn (fun θ =>
          (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
            * Work.Spaces.Wt α z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
        ((pz_cont_mixed_div Φ hΦ hv j i z hz).mul (pz_cont_Wt α z)).pow 2
      simpa only [hG2, if_pos hcond] using h3
    · have h3 : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioo 0 (Real.pi / 2)) :=
        continuousOn_const
      simpa only [hG2, if_neg hcond] using h3
  have hG1_aesm : ∀ i, AEStronglyMeasurable (G1 i) (volume.restrict Work.Spaces.Iθ) :=
    fun i => pz_aesm_of_cont (hG1_cont i)
  have hG2_aesm : ∀ i j, AEStronglyMeasurable (G2 i j) (volume.restrict Work.Spaces.Iθ) :=
    fun i j => pz_aesm_of_cont (hG2_cont i j)
  have hG1_nn_pt : ∀ i θ, 0 ≤ G1 i θ := by
    intro i θ
    simp only [hG1, hu]
    exact sq_nonneg _
  have hG2_nn_pt : ∀ i j θ, 0 ≤ G2 i j θ := by
    intro i j θ
    simp only [hG2]
    split_ifs with hh
    · exact sq_nonneg _
    · exact le_refl 0
  have hG1_nn : ∀ i, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] G1 i :=
    fun i => Eventually.of_forall (hG1_nn_pt i)
  have hG2_nn : ∀ i j, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] G2 i j :=
    fun i j => Eventually.of_forall (hG2_nn_pt i j)
  have hS1_nn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ i ∈ Finset.range 5, G1 i θ) :=
    Eventually.of_forall fun θ => Finset.sum_nonneg fun i _ => hG1_nn_pt i θ
  have hS2_nn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ) :=
    Eventually.of_forall fun θ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hG2_nn_pt i j θ
  have hS2i_cont : ∀ i, ContinuousOn (fun θ => ∑ j ∈ Finset.range 5, G2 i j θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun i => continuousOn_finsetSum _ fun j _ => hG2_cont i j
  have hS2i_nn : ∀ i, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => ∑ j ∈ Finset.range 5, G2 i j θ) :=
    fun i => Eventually.of_forall fun θ => Finset.sum_nonneg fun j _ => hG2_nn_pt i j θ
  have hS1_cont : ContinuousOn (fun θ => ∑ i ∈ Finset.range 5, G1 i θ)
      (Set.Ioo 0 (Real.pi / 2)) := continuousOn_finsetSum _ fun i _ => hG1_cont i
  have hS2_cont : ContinuousOn (fun θ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_finsetSum _ fun i _ =>
      continuousOn_finsetSum _ fun j _ => hG2_cont i j
  -- ### bound each summand
  have h5 : ∀ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G1 i θ) ≤ C * Rint := by
    intro i hi
    have hi4 : i ≤ 4 := by have h := Finset.mem_range.mp hi; omega
    have hA : (∫ θ in Work.Spaces.Iθ, G1 i θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      have h := hTWz1 i hi
      simpa only [hG1, hu] using h
    have hB : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ Rint := by
      rw [hRint]
      exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hRint_int
        (Eventually.of_forall fun θ =>
          Work.Spaces.sq_le_HkIntegrand_z α 4 (Work.Spaces.pth Φ) z θ i hi4)
    calc (∫ θ in Work.Spaces.Iθ, G1 i θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter i (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := hA
      _ ≤ C * Rint := mul_le_mul_of_nonneg_left hB hCpos.le
  have h6 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      (∫ θ in Work.Spaces.Iθ, G2 i j θ) ≤ 6 * C * Rint := by
    intro i hi j hj
    by_cases hcond : 1 ≤ i ∧ i + j ≤ 4
    · have hi4 : i ≤ 4 := by have h := Finset.mem_range.mp hi; omega
      have hj4 : j ≤ 4 := by have h := Finset.mem_range.mp hj; omega
      have himem : i ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hcond.1, hi4⟩
      have hG2eq : (∫ θ in Work.Spaces.Iθ, G2 i j θ)
          = ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j i (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with θ
        simp only [hG2]
        rw [if_pos hcond]
      have hA : (∫ θ in Work.Spaces.Iθ, G2 i j θ)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
        rw [hG2eq]
        exact hTWz2 i himem j hj hcond.2
      have hB1 : (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) ≤ Rint := by
        rw [hRint]
        exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hRint_int
          (Eventually.of_forall fun θ =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 (Work.Spaces.pth Φ) z θ j hj4)
      have hB2 : ∀ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) ≤ Rint := by
        intro m hm
        obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
        have hm4 : m ≤ 4 := by omega
        have hmj : m + j ≤ 4 := by omega
        rw [hRint]
        exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hRint_int
          (Eventually.of_forall fun θ =>
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 (Work.Spaces.pth Φ) z θ m j hm1 hmj)
      have hB2sum : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
          ≤ 5 * Rint := by
        calc (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
            ≤ ∑ m ∈ Finset.Icc 1 i, Rint := Finset.sum_le_sum hB2
          _ = ((Finset.Icc 1 i).card : ℝ) * Rint := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 5 * Rint := by
              refine mul_le_mul_of_nonneg_right ?_ hRint_nn
              have hsub : Finset.Icc 1 i ⊆ Finset.range 5 := fun m hm => by
                obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
                exact Finset.mem_range.mpr (by omega)
              have : (Finset.Icc 1 i).card ≤ 5 := by
                calc (Finset.Icc 1 i).card ≤ (Finset.range 5).card := Finset.card_le_card hsub
                  _ = 5 := Finset.card_range 5
              exact_mod_cast this
      calc (∫ θ in Work.Spaces.Iθ, G2 i j θ)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := hA
        _ ≤ C * (Rint + 5 * Rint) :=
            mul_le_mul_of_nonneg_left (add_le_add hB1 hB2sum) hCpos.le
        _ = 6 * C * Rint := by ring
    · have hzero : (∫ θ in Work.Spaces.Iθ, G2 i j θ) = 0 := by
        have hfun : G2 i j = fun _ => (0 : ℝ) := by
          funext θ
          simp only [hG2]
          rw [if_neg hcond]
        rw [hfun]
        simp
      rw [hzero]
      exact mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hRint_nn
  -- ### assemble
  have h1 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      = ∫ θ in Work.Spaces.Iθ, ((∑ i ∈ Finset.range 5, G1 i θ)
          + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ)) :=
    integral_congr_ae (Eventually.of_forall fun θ => hLdef θ)
  have h2 : (∫ θ in Work.Spaces.Iθ, ((∑ i ∈ Finset.range 5, G1 i θ)
          + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ)))
      ≤ (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, G1 i θ)
        + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ) :=
    pz_integral_add_le (pz_aesm_of_cont hS1_cont) hS1_nn
      (pz_aesm_of_cont hS2_cont) hS2_nn
  have h3 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, G1 i θ)
      ≤ ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G1 i θ) :=
    pz_integral_finsetSum_le (Finset.range 5) (fun i _ => hG1_aesm i) (fun i _ => hG1_nn i)
  have h4 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ)
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ) := by
    have houter := pz_integral_finsetSum_le (μ := volume.restrict Work.Spaces.Iθ)
      (s := Finset.range 5) (f := fun i θ => ∑ j ∈ Finset.range 5, G2 i j θ)
      (fun i _ => pz_aesm_of_cont (hS2i_cont i)) (fun i _ => hS2i_nn i)
    have hinner : ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 5, G2 i j θ)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ) :=
      Finset.sum_le_sum fun i _ =>
        pz_integral_finsetSum_le (μ := volume.restrict Work.Spaces.Iθ)
          (s := Finset.range 5) (f := G2 i) (fun j _ => hG2_aesm i j) (fun j _ => hG2_nn i j)
    exact le_trans houter hinner
  have hsum1 : ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G1 i θ) ≤ 5 * (C * Rint) := by
    calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G1 i θ)
        ≤ ∑ i ∈ Finset.range 5, (C * Rint) := Finset.sum_le_sum h5
      _ = 5 * (C * Rint) := by rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]
  have hsum2 : ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (∫ θ in Work.Spaces.Iθ, G2 i j θ) ≤ 25 * (6 * C * Rint) := by
    have hinner : ∀ i ∈ Finset.range 5,
        ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ) ≤ 5 * (6 * C * Rint) := by
      intro i hi
      calc ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ)
          ≤ ∑ j ∈ Finset.range 5, (6 * C * Rint) := Finset.sum_le_sum fun j hj => h6 i hi j hj
        _ = 5 * (6 * C * Rint) := by rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]
    calc ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ)
        ≤ ∑ i ∈ Finset.range 5, (5 * (6 * C * Rint)) := Finset.sum_le_sum hinner
      _ = 25 * (6 * C * Rint) := by
          rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]; ring
  have hmain : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
      ≤ 155 * C * Rint := by
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
        = ∫ θ in Work.Spaces.Iθ, ((∑ i ∈ Finset.range 5, G1 i θ)
            + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ)) := h1
      _ ≤ (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, G1 i θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, G2 i j θ) := h2
      _ ≤ (∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G1 i θ))
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, G2 i j θ) :=
          add_le_add h3 h4
      _ ≤ 5 * (C * Rint) + 25 * (6 * C * Rint) := add_le_add hsum1 hsum2
      _ = 155 * C * Rint := by ring
  exact le_trans hmain (by nlinarith [hCpos, hRint_nn])

end Work.Elliptic
