import Mathlib
import Submission.Work.NN.Core.VanishingDefs
import Submission.Work.NN.Core.holderNorm_zero_fiberPotAnn_le
import Submission.Work.NN.Core.continuousOn_fiberPotAnn
import Submission.Work.NN.Core.fderiv_fiberPotAnn_apply
import Submission.Work.NN.Core.holderNorm_le_wirtinger_coord_on
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.CR.Flat.Holder.contDiffOn_succ_of_wirtinger
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.NN.Core.contDiffOn_fiberPotAnn
import Submission.Work.NN.Core.differentiableOn_fiberPotAnn

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.NN.Core


/-! ## Integrability and linearity of the annulus potential in its datum

The annulus `fiberAnnulus (s j) R` is bounded and at distance `≥ s j - r j > 0` from the pole
`z j` of a point `z` of `polydisc 0 r`.  Hence for *continuous* data `ξ` the integrand of
`fiberPotAnn j l (fiberAnnulus (s j) R) ξ z` is integrable, and the potential is complex-linear
in the datum.  This is what allows the Wirtinger derivatives of the datum to be pulled through
the integral. -/

private lemma isFiniteMeasure_restrict_fiberAnnulus (s R : ℝ) :
    IsFiniteMeasure (volume.restrict (fiberAnnulus s R)) :=
  isFiniteMeasure_restrict_of_lt_top (volume_fiberAnnulus_lt_top s R)

private lemma pi_single_apply_ne_zero {n : ℕ} {i' j : Fin n} (h : i' ≠ j) (c : ℂ) :
    (Pi.single i' c : Cn n) j = 0 := by
  rw [Pi.single_apply]
  simp [Ne.symm h]

private lemma pi_single_apply_self {n : ℕ} (j : Fin n) (c : ℂ) :
    (Pi.single j c : Cn n) j = c := by
  rw [Pi.single_apply]
  simp

private lemma continuous_update_pi {n : ℕ} (j : Fin n) (z : Cn n) :
    Continuous fun w : ℂ => Function.update z j w := by
  refine continuous_pi fun i => ?_
  by_cases h : i = j
  · subst h; simp only [Function.update_self]; exact continuous_id
  · simp only [Function.update_of_ne h]; exact continuous_const

private lemma integrableOn_fiberPotAnn_integrand {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ}
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {ξ : Cn n → ℂ} (hξ : Continuous ξ) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    IntegrableOn (fun w : ℂ => ξ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      (fiberAnnulus (s j) R) := by
  have hd : 0 < s j - r j := by linarith [hr j, hrs j]
  have hzj : ‖z j‖ < r j := by simpa using hz j
  have hcontξ : Continuous fun w : ℂ => ξ (Function.update z j w) :=
    hξ.comp (continuous_update_pi j z)
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hcontξ.continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) R → ‖ξ (Function.update z j w)‖ ≤ M :=
    fun w hw => le_trans (hM₀ w (Metric.ball_subset_closedBall hw)) (le_max_left _ _)
  haveI : IsFiniteMeasure (volume.restrict (fiberAnnulus (s j) R)) :=
    isFiniteMeasure_restrict_fiberAnnulus (s j) R
  refine MeasureTheory.Integrable.of_bound ?_ (M * (s j - r j)⁻¹ ^ (l + 1)) ?_
  · exact (hcontξ.measurable.mul
      (((measurable_id.sub measurable_const).inv).pow_const (l + 1))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_fiberAnnulus (s j) R)] with w hw
    rw [norm_mul, norm_pow]
    have h1 : ‖ξ (Function.update z j w)‖ ≤ M := hM w (fiberAnnulus_subset_ball (s j) R hw)
    have h2 : ‖(w - z j)⁻¹‖ ^ (l + 1) ≤ (s j - r j)⁻¹ ^ (l + 1) :=
      pow_le_pow_left₀ (norm_nonneg _)
        (inv_norm_le_of_mem_fiberAnnulus hd hw (by linarith [le_of_lt hzj])) _
    exact mul_le_mul h1 h2 (by positivity) hM0

private lemma fiberPotAnn_add_of_integrable {n : ℕ} {j : Fin n} {l : ℕ} {A : Set ℂ} {z : Cn n}
    {ξ ζ : Cn n → ℂ}
    (hξ : IntegrableOn (fun w : ℂ => ξ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)) A)
    (hζ : IntegrableOn (fun w : ℂ => ζ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)) A) :
    fiberPotAnn j l A (fun y => ξ y + ζ y) z = fiberPotAnn j l A ξ z + fiberPotAnn j l A ζ z := by
  rw [fiberPotAnn_apply, fiberPotAnn_apply, fiberPotAnn_apply]
  have h1 : (fun w : ℂ => (fun y => ξ y + ζ y) (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      = fun w : ℂ => ξ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
          + ζ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1) := by
    funext w; ring
  rw [h1, MeasureTheory.integral_add hξ hζ]
  ring

private lemma fiberPotAnn_sub_of_integrable {n : ℕ} {j : Fin n} {l : ℕ} {A : Set ℂ} {z : Cn n}
    {ξ ζ : Cn n → ℂ}
    (hξ : IntegrableOn (fun w : ℂ => ξ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)) A)
    (hζ : IntegrableOn (fun w : ℂ => ζ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)) A) :
    fiberPotAnn j l A (fun y => ξ y - ζ y) z = fiberPotAnn j l A ξ z - fiberPotAnn j l A ζ z := by
  rw [fiberPotAnn_apply, fiberPotAnn_apply, fiberPotAnn_apply]
  have h1 : (fun w : ℂ => (fun y => ξ y - ζ y) (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1))
      = fun w : ℂ => ξ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1)
          - ζ (Function.update z j w) * ((w - z j)⁻¹) ^ (l + 1) := by
    funext w; ring
  rw [h1, MeasureTheory.integral_sub hξ hζ]
  ring

private lemma fiberPotAnn_linear {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {ξ ζ : Cn n → ℂ} (hξ : Continuous ξ) (hζ : Continuous ζ) (c d : ℂ) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y + d * ζ y) z
      = c * fiberPotAnn j l (fiberAnnulus (s j) R) ξ z
        + d * fiberPotAnn j l (fiberAnnulus (s j) R) ζ z := by
  have h1 : fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y + d * ζ y) z
      = fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y) z
        + fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => d * ζ y) z :=
    fiberPotAnn_add_of_integrable
      (integrableOn_fiberPotAnn_integrand (R := R) hr hrs (continuous_const.mul hξ) hz)
      (integrableOn_fiberPotAnn_integrand (R := R) hr hrs (continuous_const.mul hζ) hz)
  rw [h1, fiberPotAnn_const_mul, fiberPotAnn_const_mul]

private lemma continuous_dCoord {n : ℕ} {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) (i' : Fin n) :
    Continuous fun y => Work.CR.Flat.dCoord i' η y := by
  rw [show (fun y => Work.CR.Flat.dCoord i' η y)
      = Work.NN.Core.dCoordLin i' ∘ (fderiv ℝ η) from
      funext fun y => congrFun (Work.NN.Core.dCoord_eq_comp i' η) y]
  exact (Work.NN.Core.dCoordLin i').continuous.comp (hη.continuous_fderiv one_ne_zero)

private lemma continuous_dbarCoord {n : ℕ} {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) (i' : Fin n) :
    Continuous fun y => Work.CR.Flat.dbarCoord i' η y := by
  rw [show (fun y => Work.CR.Flat.dbarCoord i' η y)
      = Work.CR.Flat.Polydisc.dbarCoordPhi i' ∘ (fderiv ℝ η) from
      funext fun y => congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp i' η) y]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi i').continuous.comp
    (hη.continuous_fderiv one_ne_zero)


/-! ## The derivative formula on the polydisc -/

/-- `fderiv_fiberPotAnn_apply` specialised to points of the polydisc `polydisc 0 r`
(`r j < s j`, so the pole stays off the annulus). -/
private lemma fderiv_fiberPotAnn_apply_polydisc {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ}
    {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) (v : Cn n) :
    fderiv ℝ (fiberPotAnn j l (fiberAnnulus (s j) R) η) z v
      = fiberPotAnn j l (fiberAnnulus (s j) R)
          (fun y => fderiv ℝ η y (Function.update v j 0)) z
        + (l + 1) * (v j) * fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η z := by
  have hd : 0 < (s j + r j) / 2 := by linarith [hr j, hrs j]
  have hzj : ‖z j‖ < (s j + r j) / 2 := by
    have h : ‖z j‖ < r j := by simpa using hz j
    linarith [hrs j, hr j]
  set S : Set (Cn n) := {z' : Cn n | ‖z' j‖ < (s j + r j) / 2} ∩ Metric.ball z 1 with hSdef
  have hSnhds : S ∈ nhds z := by
    rw [hSdef]
    exact Filter.inter_mem
      ((isOpen_lt (continuous_apply j).norm continuous_const).mem_nhds hzj)
      (Metric.ball_mem_nhds z (by norm_num))
  have hAd : ∀ w ∈ fiberAnnulus (s j) R, (s j + r j) / 2 ≤ ‖w‖ := by
    intro w hw
    have h := hw.1
    linarith [hrs j]
  have hMs : ∀ z' ∈ S, ‖z' j‖ < (s j + r j) / 2 := fun z' hz' => hz'.1
  set ρ : ℝ := max (‖z‖ + 1) R with hρdef
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) (le_max_left _ _)
  have hsub : ∀ z' ∈ S, ∀ w ∈ fiberAnnulus (s j) R, ‖Function.update z' j w‖ ≤ ρ := by
    intro z' hz' w hw
    refine (pi_norm_le_iff_of_nonneg hρ0).mpr fun i => ?_
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      exact le_trans (le_of_lt hw.2) (le_max_right _ _)
    · rw [Function.update_of_ne hij]
      have hz'ball : z' ∈ Metric.ball z 1 := hz'.2
      have h2 : ‖z' i‖ ≤ ‖z'‖ := norm_le_pi_norm z' i
      have h3 : ‖z'‖ ≤ ‖z‖ + 1 := by
        have h4 : ‖z' - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz'ball
        have h5 : ‖z'‖ ≤ ‖z' - z‖ + ‖z‖ := by
          have := norm_add_le (z' - z) z
          simpa using this
        linarith
      exact le_trans (le_trans h2 h3) (le_max_left _ _)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Cn n) ρ).exists_bound_of_continuousOn
    hη.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : Cn n) ρ).exists_bound_of_continuousOn
    (hη.continuous_fderiv one_ne_zero).continuousOn
  set M : ℝ := max M₀ 0 with hMdef
  set M' : ℝ := max M₁ 0 with hM'def
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM0' : 0 ≤ M' := le_max_right _ _
  have hMbound : ∀ z' ∈ S, ∀ w ∈ fiberAnnulus (s j) R,
      ‖η (Function.update z' j w)‖ ≤ M := fun z' hz' w hw =>
    le_trans (hM₀ _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hsub z' hz' w hw))
      (le_max_left _ _)
  have hM'bound : ∀ z' ∈ S, ∀ w ∈ fiberAnnulus (s j) R,
      ‖fderiv ℝ η (Function.update z' j w)‖ ≤ M' := fun z' hz' w hw =>
    le_trans (hM₁ _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hsub z' hz' w hw))
      (le_max_left _ _)
  exact fderiv_fiberPotAnn_apply hη (measurableSet_fiberAnnulus (s j) R)
    (volume_fiberAnnulus_lt_top (s j) R) hSnhds hd hM0 hM0' hAd hMs hMbound hM'bound v

/-- The potential is complex-linear in the datum, in the two-parameter form used below. -/
private lemma fiberPotAnn_lincomb {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {ξ ζ : Cn n → ℂ} (hξ : Continuous ξ) (hζ : Continuous ζ) (c d : ℂ) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y + d * ζ y) z
      = c * fiberPotAnn j l (fiberAnnulus (s j) R) ξ z
        + d * fiberPotAnn j l (fiberAnnulus (s j) R) ζ z :=
  fiberPotAnn_linear hr hrs hξ hζ c d hz

/-- The potential is complex-linear in the datum, in the two-parameter form with a difference. -/
private lemma fiberPotAnn_lincomb_sub {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    {ξ ζ : Cn n → ℂ} (hξ : Continuous ξ) (hζ : Continuous ζ) (c d : ℂ) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y - d * ζ y) z
      = c * fiberPotAnn j l (fiberAnnulus (s j) R) ξ z
        - d * fiberPotAnn j l (fiberAnnulus (s j) R) ζ z := by
  have h1 : fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y - d * ζ y) z
      = fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => c * ξ y) z
        - fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => d * ζ y) z :=
    fiberPotAnn_sub_of_integrable
      (integrableOn_fiberPotAnn_integrand (R := R) hr hrs (continuous_const.mul hξ) hz)
      (integrableOn_fiberPotAnn_integrand (R := R) hr hrs (continuous_const.mul hζ) hz)
  rw [h1, fiberPotAnn_const_mul, fiberPotAnn_const_mul]

private lemma continuous_fderiv_apply {n : ℕ} {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) (v : Cn n) :
    Continuous fun y => fderiv ℝ η y v :=
  (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp (hη.continuous_fderiv one_ne_zero)

/-! ## The Wirtinger derivatives of the annulus potential -/

private lemma dCoord_fiberPotAnn_of_ne {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) {i' : Fin n} (hi' : i' ≠ j) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    Work.CR.Flat.dCoord i' (fiberPotAnn j l (fiberAnnulus (s j) R) η) z
      = fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y) z := by
  set ξ₁ : Cn n → ℂ := fun y => fderiv ℝ η y (Pi.single i' (1 : ℂ)) with hξ₁def
  set ξ₂ : Cn n → ℂ := fun y => fderiv ℝ η y (Pi.single i' (Complex.I : ℂ)) with hξ₂def
  have hc1 : Continuous ξ₁ := by rw [hξ₁def]; exact continuous_fderiv_apply hη _
  have hc2 : Continuous ξ₂ := by rw [hξ₂def]; exact continuous_fderiv_apply hη _
  have h1 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single i' 1)
  have h2 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single i' Complex.I)
  have hv1 : (Pi.single i' (1 : ℂ) : Cn n) j = 0 := pi_single_apply_ne_zero hi' 1
  have hv2 : (Pi.single i' (Complex.I : ℂ) : Cn n) j = 0 := pi_single_apply_ne_zero hi' Complex.I
  have hupd1 : Function.update (Pi.single i' (1 : ℂ) : Cn n) j 0 = Pi.single i' 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self, hv1]
    · rw [Function.update_of_ne hk]
  have hupd2 : Function.update (Pi.single i' (Complex.I : ℂ) : Cn n) j 0 = Pi.single i' Complex.I := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self, hv2]
    · rw [Function.update_of_ne hk]
  have hL : Work.CR.Flat.dCoord i' (fiberPotAnn j l (fiberAnnulus (s j) R) η) z
      = (1/2 : ℂ) * (fiberPotAnn j l (fiberAnnulus (s j) R) ξ₁ z
          - Complex.I * fiberPotAnn j l (fiberAnnulus (s j) R) ξ₂ z) := by
    rw [Work.CR.Flat.dCoord, h1, h2, hupd1, hupd2, hv1, hv2, ← hξ₁def, ← hξ₂def]
    simp only [mul_zero, zero_mul, add_zero, mul_one]
  have hP : fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y) z
      = (1/2 : ℂ) * (fiberPotAnn j l (fiberAnnulus (s j) R) ξ₁ z
          - Complex.I * fiberPotAnn j l (fiberAnnulus (s j) R) ξ₂ z) := by
    have hfun : (fun y : Cn n => Work.CR.Flat.dCoord i' η y)
        = fun y => (1/2 : ℂ) * ξ₁ y - (Complex.I / 2) * ξ₂ y := by
      funext y
      simp only [Work.CR.Flat.dCoord, hξ₁def, hξ₂def]
      ring
    rw [hfun, fiberPotAnn_lincomb_sub (R := R) (j := j) (l := l) hr hrs hc1 hc2
      (1/2 : ℂ) (Complex.I / 2) hz]
    ring
  rw [hL, ← hP]

private lemma dbarCoord_fiberPotAnn_of_ne {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) {i' : Fin n} (hi' : i' ≠ j) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    Work.CR.Flat.dbarCoord i' (fiberPotAnn j l (fiberAnnulus (s j) R) η) z
      = fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dbarCoord i' η y) z := by
  set ξ₁ : Cn n → ℂ := fun y => fderiv ℝ η y (Pi.single i' (1 : ℂ)) with hξ₁def
  set ξ₂ : Cn n → ℂ := fun y => fderiv ℝ η y (Pi.single i' (Complex.I : ℂ)) with hξ₂def
  have hc1 : Continuous ξ₁ := by rw [hξ₁def]; exact continuous_fderiv_apply hη _
  have hc2 : Continuous ξ₂ := by rw [hξ₂def]; exact continuous_fderiv_apply hη _
  have h1 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single i' 1)
  have h2 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single i' Complex.I)
  have hv1 : (Pi.single i' (1 : ℂ) : Cn n) j = 0 := pi_single_apply_ne_zero hi' 1
  have hv2 : (Pi.single i' (Complex.I : ℂ) : Cn n) j = 0 := pi_single_apply_ne_zero hi' Complex.I
  have hupd1 : Function.update (Pi.single i' (1 : ℂ) : Cn n) j 0 = Pi.single i' 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self, hv1]
    · rw [Function.update_of_ne hk]
  have hupd2 : Function.update (Pi.single i' (Complex.I : ℂ) : Cn n) j 0 = Pi.single i' Complex.I := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self, hv2]
    · rw [Function.update_of_ne hk]
  have hL : Work.CR.Flat.dbarCoord i' (fiberPotAnn j l (fiberAnnulus (s j) R) η) z
      = (1/2 : ℂ) * (fiberPotAnn j l (fiberAnnulus (s j) R) ξ₁ z
          + Complex.I * fiberPotAnn j l (fiberAnnulus (s j) R) ξ₂ z) := by
    rw [Work.CR.Flat.dbarCoord, h1, h2, hupd1, hupd2, hv1, hv2, ← hξ₁def, ← hξ₂def]
    simp only [mul_zero, zero_mul, add_zero, mul_one]
  have hP : fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dbarCoord i' η y) z
      = (1/2 : ℂ) * (fiberPotAnn j l (fiberAnnulus (s j) R) ξ₁ z
          + Complex.I * fiberPotAnn j l (fiberAnnulus (s j) R) ξ₂ z) := by
    have hfun : (fun y : Cn n => Work.CR.Flat.dbarCoord i' η y)
        = fun y => (1/2 : ℂ) * ξ₁ y + (Complex.I / 2) * ξ₂ y := by
      funext y
      simp only [Work.CR.Flat.dbarCoord, hξ₁def, hξ₂def]
      ring
    rw [hfun, fiberPotAnn_lincomb (R := R) (j := j) (l := l) hr hrs hc1 hc2
      (1/2 : ℂ) (Complex.I / 2) hz]
    ring
  rw [hL, ← hP]

private lemma dCoord_fiberPotAnn_self {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    Work.CR.Flat.dCoord j (fiberPotAnn j l (fiberAnnulus (s j) R) η) z
      = (l + 1) * fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η z := by
  have h1 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single j 1)
  have h2 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single j Complex.I)
  have hv1 : (Pi.single j (1 : ℂ) : Cn n) j = 1 := pi_single_apply_self j 1
  have hv2 : (Pi.single j (Complex.I : ℂ) : Cn n) j = Complex.I :=
    pi_single_apply_self j Complex.I
  have hupd1 : Function.update (Pi.single j (1 : ℂ) : Cn n) j 0 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hk, pi_single_apply_ne_zero (Ne.symm hk) 1]; simp
  have hupd2 : Function.update (Pi.single j (Complex.I : ℂ) : Cn n) j 0 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hk, pi_single_apply_ne_zero (Ne.symm hk) Complex.I]; simp
  have hz1 : (fun y : Cn n => fderiv ℝ η y (0 : Cn n)) = fun _ => 0 := by
    funext y; simp
  rw [Work.CR.Flat.dCoord, h1, h2, hupd1, hupd2, hv1, hv2, hz1]
  simp only [fiberPotAnn_zero_fun, mul_zero, zero_mul, add_zero, mul_one]
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

private lemma dbarCoord_fiberPotAnn_self {n : ℕ} {R : ℝ} {j : Fin n} {l : ℕ} {r s : Fin n → ℝ}
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i) (hsR : s j < R)
    {η : Cn n → ℂ} (hη : ContDiff ℝ 1 η) {z : Cn n}
    (hz : z ∈ Work.CR.Flat.polydisc (0 : Cn n) r) :
    Work.CR.Flat.dbarCoord j (fiberPotAnn j l (fiberAnnulus (s j) R) η) z = 0 := by
  have h1 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single j 1)
  have h2 := fderiv_fiberPotAnn_apply_polydisc (R := R) (j := j) (l := l) hr hrs hsR hη hz
    (Pi.single j Complex.I)
  have hv1 : (Pi.single j (1 : ℂ) : Cn n) j = 1 := pi_single_apply_self j 1
  have hv2 : (Pi.single j (Complex.I : ℂ) : Cn n) j = Complex.I :=
    pi_single_apply_self j Complex.I
  have hupd1 : Function.update (Pi.single j (1 : ℂ) : Cn n) j 0 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hk, pi_single_apply_ne_zero (Ne.symm hk) 1]; simp
  have hupd2 : Function.update (Pi.single j (Complex.I : ℂ) : Cn n) j 0 = 0 := by
    funext k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hk, pi_single_apply_ne_zero (Ne.symm hk) Complex.I]; simp
  have hz1 : (fun y : Cn n => fderiv ℝ η y (0 : Cn n)) = fun _ => 0 := by
    funext y; simp
  rw [Work.CR.Flat.dbarCoord, h1, h2, hupd1, hupd2, hv1, hv2, hz1]
  simp only [fiberPotAnn_zero_fun, mul_zero, zero_mul, add_zero, mul_one]
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- One step of the induction on the derivative order: the `C^{i+1,α}` norm of the annulus
potential `fiberPotAnn j l A η` (with `A = fiberAnnulus (s j) R`) on `polydisc 0 r` is bounded by
its `C^0` norm together with the `C^{i,α}` norms of the `2n` potentials obtained by replacing the
datum `η` by its Wirtinger derivatives `dCoord i' η`, `dbarCoord i' η` (`i' ≠ j`), plus the index
`l+1` potential applied to `η` itself (the fibre index `j` differentiates the kernel). -/
theorem holderNorm_succ_fiberPotAnn_le {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    (hsR : ∀ i, s i < R) (l i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : (Fin n → ℂ) → ℂ, ContDiff ℝ (i + 1 + l) η →
      Work.CR.Flat.holderNorm (i + 1) α
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
          (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C *
          (Work.CR.Flat.holderNorm 0 α
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
              (Work.CR.Flat.polydisc 0 r)
           + ∑ i' ∈ Finset.univ.erase j,
               (Work.CR.Flat.holderNorm i α
                  (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
                    (fun y => Work.CR.Flat.dCoord i' η y))
                  (Work.CR.Flat.polydisc 0 r)
                + Work.CR.Flat.holderNorm i α
                  (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
                    (fun y => Work.CR.Flat.dbarCoord i' η y))
                  (Work.CR.Flat.polydisc 0 r))
           + Work.CR.Flat.holderNorm i α
              (Work.NN.Core.fiberPotAnn j (l + 1) (Work.NN.Core.fiberAnnulus (s j) R) η)
              (Work.CR.Flat.polydisc 0 r)) := by
  have hsRj : s j < R := hsR j
  obtain ⟨K, hKpos, hK⟩ := Work.NN.Core.holderNorm_le_wirtinger_coord_on (n := n) i (α := α)
    (Ω := Work.CR.Flat.polydisc (0 : Cn n) r) (Work.CR.Flat.isOpen_polydisc (0 : Cn n) r)
  refine ⟨K * max 1 ((l : ℝ) + 1), by positivity, ?_⟩
  intro η hη
  have hη1 : ContDiff ℝ 1 η :=
    hη.of_le (by exact_mod_cast (show 1 ≤ i + 1 + l from by omega))
  have hsm : ContDiffOn ℝ (i + 1)
      (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
      (Work.CR.Flat.polydisc (0 : Cn n) r) :=
    Work.NN.Core.contDiffOn_fiberPotAnn hr hrs hsRj (i + 1) η
      (hη.of_le (by exact_mod_cast (show i + 1 ≤ i + 1 + l from by omega)))
  have hsm' : ContDiffOn ℝ (i : ℕ∞)
      (Work.NN.Core.fiberPotAnn j (l + 1) (Work.NN.Core.fiberAnnulus (s j) R) η)
      (Work.CR.Flat.polydisc (0 : Cn n) r) :=
    Work.NN.Core.contDiffOn_fiberPotAnn hr hrs hsRj i η
      (hη.of_le (by exact_mod_cast (show i ≤ i + 1 + l from by omega)))
  -- the target's three pieces
  set X0 : ℝ≥0∞ := Work.CR.Flat.holderNorm 0 α
      (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
      (Work.CR.Flat.polydisc 0 r) with hX0
  set Ssum : ℝ≥0∞ := ∑ i' ∈ Finset.univ.erase j,
      (Work.CR.Flat.holderNorm i α
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
            (fun y => Work.CR.Flat.dCoord i' η y))
          (Work.CR.Flat.polydisc 0 r)
        + Work.CR.Flat.holderNorm i α
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
            (fun y => Work.CR.Flat.dbarCoord i' η y))
          (Work.CR.Flat.polydisc 0 r)) with hSsum
  set E1 : ℝ≥0∞ := Work.CR.Flat.holderNorm i α
      (Work.NN.Core.fiberPotAnn j (l + 1) (Work.NN.Core.fiberAnnulus (s j) R) η)
      (Work.CR.Flat.polydisc 0 r) with hE1
  -- the sum produced by the Wirtinger estimate
  set W : ℝ≥0∞ := ∑ j' : Fin n,
      (Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dCoord j'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)
        + Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dbarCoord j'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)) with hW
  have hstep : Work.CR.Flat.holderNorm (i + 1) α
        (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc 0 r) ≤ ENNReal.ofReal K * (X0 + W) := hK _ hsm
  -- the transverse terms
  have hne : ∀ i' ∈ Finset.univ.erase j, i' ≠ j := fun i' hi' => (Finset.mem_erase.mp hi').1
  have hterm : ∀ i' ∈ Finset.univ.erase j,
      (Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dCoord i'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)
        + Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dbarCoord i'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r))
      ≤ (Work.CR.Flat.holderNorm i α
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
              (fun y => Work.CR.Flat.dCoord i' η y))
            (Work.CR.Flat.polydisc 0 r)
          + Work.CR.Flat.holderNorm i α
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
              (fun y => Work.CR.Flat.dbarCoord i' η y))
            (Work.CR.Flat.polydisc 0 r)) := by
    intro i' hi'
    have h1 : Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dCoord i'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)
        = Work.CR.Flat.holderNorm i α
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
              (fun y => Work.CR.Flat.dCoord i' η y))
            (Work.CR.Flat.polydisc 0 r) :=
      Work.NN.Core.holderNorm_congr (fun z hz =>
        dCoord_fiberPotAnn_of_ne hr hrs hsRj hη1 (hne i' hi') hz)
    have h2 : Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dbarCoord i'
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)
        = Work.CR.Flat.holderNorm i α
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R)
              (fun y => Work.CR.Flat.dbarCoord i' η y))
            (Work.CR.Flat.polydisc 0 r) :=
      Work.NN.Core.holderNorm_congr (fun z hz =>
        dbarCoord_fiberPotAnn_of_ne hr hrs hsRj hη1 (hne i' hi') hz)
    rw [h1, h2]
  -- the fibre term
  have hAj : Work.CR.Flat.holderNorm i α
        (fun z => Work.CR.Flat.dCoord j
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
        (Work.CR.Flat.polydisc 0 r)
      = ENNReal.ofReal ((l : ℝ) + 1) * E1 := by
    rw [Work.NN.Core.holderNorm_congr (fun z hz => dCoord_fiberPotAnn_self hr hrs hsRj hη1 hz)]
    rw [show (fun z : Cn n => (↑l + 1) *
          Work.NN.Core.fiberPotAnn j (l + 1) (Work.NN.Core.fiberAnnulus (s j) R) η z)
        = (↑l + 1 : ℂ) • Work.NN.Core.fiberPotAnn j (l + 1)
            (Work.NN.Core.fiberAnnulus (s j) R) η from rfl]
    rw [Work.CR.Flat.Holder.holderNorm_smul (↑l + 1 : ℂ) hsm'
      (Work.CR.Flat.isOpen_polydisc (0 : Cn n) r).uniqueDiffOn]
    rw [show ‖(↑l + 1 : ℂ)‖ = (l : ℝ) + 1 from by
      rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
      push_cast
      ring]
  have hBj : Work.CR.Flat.holderNorm i α
        (fun z => Work.CR.Flat.dbarCoord j
          (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
        (Work.CR.Flat.polydisc 0 r) = 0 := by
    rw [Work.NN.Core.holderNorm_congr (fun z hz => dbarCoord_fiberPotAnn_self hr hrs hsRj hη1 hz)]
    rw [show (fun z : Cn n => (0 : ℂ)) = (0 : Cn n → ℂ) from rfl]
    exact Work.CR.Flat.holderNorm_zero i α _
  -- the split of the sum over all coordinates
  have hsplit : W = (∑ i' ∈ Finset.univ.erase j,
        (Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dCoord i'
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r)
          + Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dbarCoord i'
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r)))
      + (Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dCoord j
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r)
          + Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dbarCoord j
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r)) := by
    rw [hW]
    exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)).symm
  have herase : (∑ i' ∈ Finset.univ.erase j,
        (Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dCoord i'
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r)
          + Work.CR.Flat.holderNorm i α
            (fun z => Work.CR.Flat.dbarCoord i'
              (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
            (Work.CR.Flat.polydisc 0 r))) ≤ Ssum :=
    Finset.sum_le_sum hterm
  have hfac : (Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dCoord j
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)
        + Work.CR.Flat.holderNorm i α
          (fun z => Work.CR.Flat.dbarCoord j
            (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
          (Work.CR.Flat.polydisc 0 r)) ≤ ENNReal.ofReal ((l : ℝ) + 1) * E1 := by
    rw [hAj, hBj, add_zero]
  -- assemble
  have hM1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) :=
    ENNReal.one_le_ofReal.mpr (le_max_left _ _)
  have hM2 : ENNReal.ofReal ((l : ℝ) + 1) ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hbound : X0 + W ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * (X0 + Ssum + E1) := by
    rw [hsplit]
    calc X0 + ((∑ i' ∈ Finset.univ.erase j,
            (Work.CR.Flat.holderNorm i α
                (fun z => Work.CR.Flat.dCoord i'
                  (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
                (Work.CR.Flat.polydisc 0 r)
              + Work.CR.Flat.holderNorm i α
                (fun z => Work.CR.Flat.dbarCoord i'
                  (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
                (Work.CR.Flat.polydisc 0 r)))
          + (Work.CR.Flat.holderNorm i α
              (fun z => Work.CR.Flat.dCoord j
                (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
              (Work.CR.Flat.polydisc 0 r)
            + Work.CR.Flat.holderNorm i α
              (fun z => Work.CR.Flat.dbarCoord j
                (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η) z)
              (Work.CR.Flat.polydisc 0 r)))
        ≤ X0 + (Ssum + ENNReal.ofReal ((l : ℝ) + 1) * E1) := by
          gcongr
      _ ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * (X0 + Ssum + E1) := by
          have h1 : X0 ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * X0 := by
            simpa only [one_mul] using mul_le_mul_left (b := (1 : ℝ≥0∞)) hM1 X0
          have h2 : Ssum ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * Ssum := by
            simpa only [one_mul] using mul_le_mul_left (b := (1 : ℝ≥0∞)) hM1 Ssum
          have h3 : ENNReal.ofReal ((l : ℝ) + 1) * E1
              ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * E1 :=
            mul_le_mul_left hM2 E1
          calc X0 + (Ssum + ENNReal.ofReal ((l : ℝ) + 1) * E1)
              ≤ ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * X0
                + (ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * Ssum
                  + ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * E1) := by
                exact add_le_add h1 (add_le_add h2 h3)
            _ = ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * (X0 + Ssum + E1) := by ring
  calc Work.CR.Flat.holderNorm (i + 1) α
        (Work.NN.Core.fiberPotAnn j l (Work.NN.Core.fiberAnnulus (s j) R) η)
        (Work.CR.Flat.polydisc 0 r)
      ≤ ENNReal.ofReal K * (X0 + W) := hstep
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (max 1 ((l : ℝ) + 1)) * (X0 + Ssum + E1)) :=
        mul_le_mul_right hbound _
    _ = ENNReal.ofReal (K * max 1 ((l : ℝ) + 1)) * (X0 + Ssum + E1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hKpos.le]


end Work.NN.Core
