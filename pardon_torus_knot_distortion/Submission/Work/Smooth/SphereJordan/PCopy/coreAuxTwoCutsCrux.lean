import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.plainAnnulusSetup
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.Twist
import Submission.Work.Smooth.SphereJordan.ballHomeo_of_circleHomeo
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.annulusSchoenflies_of_plain
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts
import Submission.Work.Smooth.SphereJordan.PCopy.SpanSetup
import Submission.Work.Smooth.SphereJordan.PCopy.radialTwoCutsPieces
import Submission.Work.Smooth.SphereJordan.PCopy.annulusTargetCurves
import Submission.Work.SphereJordan.argIncrement
import Submission.Work.SphereJordan.incrOn

/-!
# The crux of the two-pccuts construction, in a module importable from `pccoreAuxTwoCuts`

This is the file `Submission/Work/SphereJordan/pcpieceUpNePieceDown.lean` (the proof that the two
pieces of the cut pcannulus are distinct), copied into the dependency cone of
`Submission.Work.Smooth.SphereJordan.pccoreAuxTwoCuts`: the original imports that module, so it cannot
be imported by it.  The auxiliary lemmas `pcI_mul_cutDir_mem_annulusCut` and
`pcneg_I_mul_cutDir_mem_annulusCut` (used by the proof and originally declared in `pccoreAuxTwoCuts`)
are reproduced verbatim here, under their original names, and removed from `pccoreAuxTwoCuts`, which
now imports this module.

All declarations of the copied proof live in the namespace `Work.Smooth.SphereJordan.Crux` so that
they do not clash with the original file's declarations.
-/

namespace Work.Smooth.SphereJordan

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- **Dividing a point of a crosscut by `pccutDir S` gives a real number.** -/
theorem pccut_div_eq_ofReal (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} {z : ℂ}
    (hz : z ∈ Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂) :
    ∃ c : ℝ, z / pccutDir S = (c : ℂ) := by
  have h0 := pccutDir_ne_zero S
  have hb : (pcbase S : ℂ) / pccutDir S = ((‖(pcbase S : ℂ)‖ : ℝ) : ℂ) := by
    conv_lhs => rw [pcbase_eq_smul_cutDir S]
    rw [mul_div_cancel_right₀ _ h0]
  rcases hz with hz | hz
  · obtain ⟨σ, -, rfl⟩ := hz
    refine ⟨‖(pcbase S : ℂ)‖ + σ, ?_⟩
    rw [add_div, hb, mul_div_cancel_right₀ _ h0]
    push_cast
    ring
  · obtain ⟨σ, -, rfl⟩ := hz
    refine ⟨‖(pcbase S : ℂ)‖ - σ, ?_⟩
    rw [sub_div, hb, mul_div_cancel_right₀ _ h0]
    push_cast
    ring

/-- **`i · pccutDir S` is not on either crosscut.**  After dividing by `pccutDir S` a cut point becomes
a real number, whereas `i · pccutDir S` becomes `I`. -/
theorem pcI_mul_cutDir_notMem_cuts (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ} :
    Complex.I * pccutDir S ∉
      (Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂) := by
  intro hz
  obtain ⟨c, hc⟩ := pccut_div_eq_ofReal S hz
  have h1 : (Complex.I * pccutDir S) / pccutDir S = Complex.I := by
    rw [mul_div_assoc, div_self (pccutDir_ne_zero S), mul_one]
  rw [h1] at hc
  have h2 : (Complex.I : ℂ).im = ((c : ℝ) : ℂ).im := congrArg Complex.im hc
  simp only [Complex.I_im, Complex.ofReal_im] at h2
  norm_num at h2

/-- **(a): `i · pccutDir S` lies in the cut pcannulus.**  It has norm `1` (so it is in `pcannulus S`, as
`S.V` is contained in the *open* disc) and is on neither crosscut. -/
theorem pcI_mul_cutDir_mem_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} :
    Complex.I * pccutDir S ∈ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  refine ⟨⟨?_, ?_⟩, pcI_mul_cutDir_notMem_cuts S⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_I, one_mul,
      pcnorm_cutDir S]
  · intro hV
    have h1 : ‖Complex.I * pccutDir S‖ < 1 :=
      pcclosure_V_subset_openBall S hball (subset_closure hV)
    rw [norm_mul, Complex.norm_I, one_mul, pcnorm_cutDir S] at h1
    exact lt_irrefl 1 h1

/-- `-(I * pccutDir S)` lies in the cut pcannulus. -/
theorem pcneg_I_mul_cutDir_mem_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ : ℝ} :
    -Complex.I * Work.Smooth.SphereJordan.pccutDir S ∈
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  rw [neg_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Work.Smooth.SphereJordan.pcnorm_cutDir]
  · intro hV
    have h1 : ‖-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)‖ < 1 :=
      pcclosure_V_subset_openBall S hball (subset_closure hV)
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Work.Smooth.SphereJordan.pcnorm_cutDir] at h1
    exact lt_irrefl 1 h1
  · intro hcuts
    have h0 : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
      Work.Smooth.SphereJordan.pccutDir_ne_zero S
    have hb : (Work.Smooth.SphereJordan.pcbase S : ℂ) / Work.Smooth.SphereJordan.pccutDir S =
        ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) := by
      conv_lhs => rw [Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]
      rw [mul_div_cancel_right₀ _ h0]
    have hdiv : ∃ c : ℝ, (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)) /
        Work.Smooth.SphereJordan.pccutDir S = (c : ℂ) := by
      rcases hcuts with hz | hz
      · obtain ⟨σ, -, hσ⟩ := hz
        refine ⟨‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + σ, ?_⟩
        rw [hσ, add_div, hb, mul_div_cancel_right₀ _ h0]; push_cast; ring
      · obtain ⟨σ, -, hσ⟩ := hz
        refine ⟨‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - σ, ?_⟩
        rw [hσ, sub_div, hb, mul_div_cancel_right₀ _ h0]; push_cast; ring
    obtain ⟨c, hc⟩ := hdiv
    have h1 : (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)) /
        Work.Smooth.SphereJordan.pccutDir S = -Complex.I := by
      rw [neg_div, mul_div_assoc, div_self h0, mul_one]
    rw [h1] at hc
    have h2 := congrArg Complex.im hc
    simp only [Complex.neg_im, Complex.I_im, Complex.ofReal_im] at h2
    norm_num at h2


end Work.Smooth.SphereJordan

namespace Work.Smooth.SphereJordan.Crux



noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-- The outer radius of the auxiliary Jordan curve. -/
def pcRout : ℝ := 2

theorem pcRout_pos : 0 < pcRout := by norm_num [pcRout]

theorem pcone_lt_Rout : 1 < pcRout := by norm_num [pcRout]

/-- **The first arc.**  The radial segment on the ray `ℝ≥0 • pccutDir S` from `pcRout • pccutDir S`
down to the inner endpoint `a₁ = pcbase S + t₁ • pccutDir S` of the first crosscut. -/
def pczArcA (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) (y : ℝ) : ℂ :=
  (((pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S

/-- Clamp a real number into `[0,1]`. -/
def pczc (y : ℝ) : ℝ := max 0 (min 1 y)

theorem pczc_mem (y : ℝ) : pczc y ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem pczc_of_mem {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) : pczc y = y := by
  unfold pczc
  rw [min_eq_right hy.2, max_eq_right hy.1]

theorem pczc_continuous : Continuous pczc := by
  unfold pczc; fun_prop

theorem pczc_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : pczc y = 0 := by
  unfold pczc; rw [min_eq_right (by linarith), max_eq_left hy]

theorem pczc_eq_one_of_one_le {y : ℝ} (hy : 1 ≤ y) : pczc y = 1 := by
  unfold pczc; rw [min_eq_left hy, max_eq_right (by linarith)]

/-- The point of the model disc on the straight chord from `circlePoint θ₁` to `circlePoint θ₂`
at parameter `y` (clamped into `[0,1]`). -/
def pczChordPt (θ₁ θ₂ : ℝ) (y : ℝ) : Work.Smooth.Jordan.Disc :=
  ⟨((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
        ((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ)‖ ≤
        ‖((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ)‖ +
          ‖((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ)‖ := norm_add_le _ _
    have hn1 : ‖(Work.Smooth.Jordan.circlePoint θ₁ : ℂ)‖ = 1 := by
      rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    have hn2 : ‖(Work.Smooth.Jordan.circlePoint θ₂ : ℂ)‖ = 1 := by
      rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    have hle : (0:ℝ) ≤ pczc y := (pczc_mem y).1
    have hle1 : pczc y ≤ 1 := (pczc_mem y).2
    have hc1 : ‖((1 - pczc y : ℝ) : ℂ)‖ = 1 - pczc y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hc2 : ‖((pczc y : ℝ) : ℂ)‖ = pczc y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hle]
    calc _ ≤ ‖((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ)‖ +
          ‖((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ)‖ := h1
      _ = (1 - pczc y) * 1 + pczc y * 1 := by rw [norm_mul, norm_mul, hc1, hc2, hn1, hn2]
      _ = 1 := by ring⟩

/-- **The second arc.**  The image under the Schoenflies embedding `S.e` of the chord of the model
disc from `circlePoint θ₁` to `circlePoint θ₂`. -/
def pczArcB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ) (y : ℝ) : ℂ :=
  S.e (pczChordPt θ₁ θ₂ y)

/-- **The third arc.**  The radial segment on the ray `ℝ≥0 • pccutDir S` from the inner endpoint
`a₂ = pcbase S - t₂ • pccutDir S` of the second crosscut out to `-pcRout • pccutDir S`. -/
def pczArcC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ) (y : ℝ) : ℂ :=
  (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S

/-- **The fourth arc.**  The outer circular arc of radius `pcRout` from `-pcRout • pccutDir S` to
`pcRout • pccutDir S`, passing through `pcRout · (I · pccutDir S)`. -/
def pczArcD (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (y : ℝ) : ℂ :=
  pcRout * Work.Smooth.SphereJordan.pccutDir S *
    Complex.exp (((Real.pi * (1 - y) : ℝ) : ℂ) * Complex.I)


/-! ## Elementary properties of the four arcs -/

section Arcs

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)

theorem pczArcA_zero (t₁ : ℝ) : pczArcA S t₁ 0 = ((pcRout : ℝ) : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcA
  norm_num

theorem pczArcA_one (t₁ : ℝ) : pczArcA S t₁ 1 =
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcA
  have h : (pcRout + 1 * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ) =
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ := by ring
  rw [h]
  rw [show ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S =
      ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S +
        (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S from by push_cast; ring]
  rw [← Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]

theorem pczArcC_zero (t₂ : ℝ) : pczArcC S t₂ 0 =
    (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcC
  have h : (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - 0 *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ) =
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ := by ring
  rw [h]
  rw [show ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S =
      ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S -
        (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S from by push_cast; ring]
  rw [← Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]

theorem pccontinuous_zArcA (t₁ : ℝ) : Continuous (pczArcA S t₁) := by
  unfold pczArcA; fun_prop

theorem pccontinuous_zArcC (t₂ : ℝ) : Continuous (pczArcC S t₂) := by
  unfold pczArcC; fun_prop

theorem pccontinuous_zArcD : Continuous (pczArcD (γ := γ) S) := by
  unfold pczArcD; fun_prop

theorem pczArcC_one (t₂ : ℝ) : pczArcC S t₂ 1 = -(((pcRout : ℝ)) : ℂ) *
    Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcC
  have h : (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - 1 *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ) = -pcRout := by ring
  rw [h]
  push_cast
  ring

theorem pczArcD_zero : pczArcD S 0 = -(((pcRout : ℝ)) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  rw [show pczArcD S 0 = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp ((Real.pi : ℂ) * Complex.I) from by
    unfold pczArcD
    rw [show (Real.pi * (1 - 0) : ℝ) = Real.pi from by ring]
    try push_cast
    try ring]
  rw [Complex.exp_pi_mul_I]
  ring

theorem pczArcD_one : pczArcD S 1 = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  rw [show pczArcD S 1 = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp (0 : ℂ) from by
    unfold pczArcD
    rw [show (Real.pi * (1 - 1) : ℝ) = 0 from by ring]
    try push_cast
    try ring]
  rw [Complex.exp_zero, mul_one]

theorem pczArcD_half : pczArcD S (1/2) = ((pcRout : ℝ) : ℂ) * Complex.I *
    Work.Smooth.SphereJordan.pccutDir S := by
  rw [show pczArcD S (1/2) = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp (((Real.pi : ℂ) / 2) * Complex.I) from by
    unfold pczArcD
    rw [show (Real.pi * (1 - 1/2) : ℝ) = Real.pi / 2 from by ring]
    try push_cast
    try ring]
  rw [Complex.exp_pi_div_two_mul_I]
  ring

end Arcs

/-! ## The inner chord and its image -/

section Chord

theorem pczChordPt_zero (θ₁ θ₂ : ℝ) : pczChordPt θ₁ θ₂ 0 =
    Work.Smooth.Jordan.circlePoint θ₁ := by
  apply Subtype.ext
  show ((1 - pczc 0 : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc 0 : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) =
      ((Work.Smooth.Jordan.circlePoint θ₁ : Work.Smooth.Jordan.Disc) : ℂ)
  rw [pczc_eq_zero_of_nonpos (le_refl (0:ℝ))]
  try push_cast
  try ring

theorem pczChordPt_one (θ₁ θ₂ : ℝ) : pczChordPt θ₁ θ₂ 1 =
    Work.Smooth.Jordan.circlePoint θ₂ := by
  apply Subtype.ext
  show ((1 - pczc 1 : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc 1 : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) =
      ((Work.Smooth.Jordan.circlePoint θ₂ : Work.Smooth.Jordan.Disc) : ℂ)
  rw [pczc_eq_one_of_one_le (le_refl (1:ℝ))]
  try push_cast
  try ring

theorem pccontinuous_zChordPt (θ₁ θ₂ : ℝ) : Continuous (pczChordPt θ₁ θ₂) := by
  apply Continuous.subtype_mk
  · have h1 : Continuous (fun y : ℝ => ((1 - pczc y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.sub pczc_continuous)
    have h2 : Continuous (fun y : ℝ => ((pczc y : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp pczc_continuous
    exact (h1.mul continuous_const).add (h2.mul continuous_const)

theorem pccontinuous_zArcB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ) :
    Continuous (pczArcB (γ := γ) S θ₁ θ₂) :=
  S.e.continuous.comp (pccontinuous_zChordPt θ₁ θ₂)

end Chord


/-! ## The auxiliary Jordan curve `pcZbar` -/

section ZbarDef

/-- The unfolded auxiliary curve, read on the parameter `σ ∈ [0, 2π]`. -/
def pczBarUn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ) (σ : ℝ) : ℂ :=
  if σ ≤ Real.pi / 2 then pczArcA S t₁ (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then pczArcB S θ₁ θ₂ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then pczArcC S t₂ ((σ - Real.pi) / (Real.pi / 2))
  else pczArcD S ((σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-- The auxiliary Jordan curve: the periodic extension of `pczBarUn`. -/
def pcZbar (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ) (τ : ℝ) : ℂ :=
  pczBarUn S t₁ t₂ θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt τ)

theorem pcZbar_eq_unfold (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ)
    (τ : ℝ) : pcZbar S t₁ t₂ θ₁ θ₂ τ = pczBarUn S t₁ t₂ θ₁ θ₂
      (Work.Smooth.SphereJordan.pcperPt τ) := rfl

theorem pczBarUn_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ) :
    pczBarUn S t₁ t₂ θ₁ θ₂ 0 = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczBarUn
  rw [if_pos (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2), zero_div, pczArcA_zero]

theorem pczBarUn_two_pi (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ) :
    pczBarUn S t₁ t₂ θ₁ θ₂ (2 * Real.pi) = ((pcRout : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczBarUn
  rw [if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi / 2)),
    if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi)),
    if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ 3 * Real.pi / 2))]
  rw [show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 from by
    rw [div_eq_one_iff_eq (by positivity)]; ring]
  exact pczArcD_one S

theorem pcperPt_mem' (τ : ℝ) :
    Work.Smooth.SphereJordan.pcperPt τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) :=
  Work.SphereJordan.pcperPt_mem τ

theorem pcperPt_self' {τ : ℝ} (hτ : τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) :
    Work.Smooth.SphereJordan.pcperPt τ = τ :=
  Work.SphereJordan.pcperPt_self hτ

theorem pczBarUn_periodic_shift (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ)
    (θ₁ θ₂ : ℝ) :
    pczBarUn S t₁ t₂ θ₁ θ₂ 0 = pczBarUn S t₁ t₂ θ₁ θ₂ (2 * Real.pi) := by
  rw [pczBarUn_zero, pczBarUn_two_pi]

end ZbarDef


theorem pczArcB_zero' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ) :
    pczArcB S θ₁ θ₂ 0 = γ.γ θ₁ := by
  unfold pczArcB; rw [pczChordPt_zero, S.boundary]

theorem pczArcB_one' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ) :
    pczArcB S θ₁ θ₂ 1 = γ.γ θ₂ := by
  unfold pczArcB; rw [pczChordPt_one, S.boundary]

section ZbarCont

theorem pczBarUn_junction1 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ θ₁ θ₂ : ℝ)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pczBarUn S t₁ t₂ θ₁ θ₂ (Real.pi / 2) =
      pczArcB S θ₁ θ₂ ((Real.pi / 2 - Real.pi / 2) / (Real.pi / 2)) := by
  have h1 : (Real.pi / 2) / (Real.pi / 2) = (1 : ℝ) :=
    div_self (by positivity : Real.pi / 2 ≠ 0)
  have h2 : (Real.pi / 2 - Real.pi / 2) / (Real.pi / 2) = 0 := by rw [sub_self, zero_div]
  unfold pczBarUn
  rw [if_pos le_rfl, h1, h2, pczArcA_one S t₁, pczArcB_zero', hθ₁]

theorem pczBarUn_junction2 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ θ₁ θ₂ : ℝ)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pczBarUn S t₁ t₂ θ₁ θ₂ Real.pi =
      pczArcC S t₂ ((Real.pi - Real.pi) / (Real.pi / 2)) := by
  have h1 : (Real.pi - Real.pi / 2) / (Real.pi / 2) = (1 : ℝ) := by
    rw [div_eq_one_iff_eq (by positivity)]; ring
  have h2 : (Real.pi - Real.pi) / (Real.pi / 2) = 0 := by rw [sub_self, zero_div]
  unfold pczBarUn
  rw [if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)), if_pos le_rfl,
    h1, h2, pczArcB_one', hθ₂, pczArcC_zero]

theorem pczBarUn_junction3 (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ θ₁ θ₂ : ℝ) :
    pczBarUn S t₁ t₂ θ₁ θ₂ (3 * Real.pi / 2) =
      pczArcD S ((3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2)) := by
  have h1 : (3 * Real.pi / 2 - Real.pi) / (Real.pi / 2) = (1 : ℝ) := by
    rw [div_eq_one_iff_eq (by positivity)]; ring
  have h2 : (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2) = 0 := by rw [sub_self, zero_div]
  unfold pczBarUn
  rw [if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
    if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl,
    h1, h2, pczArcC_one, pczArcD_zero]

theorem pccontinuousOn_zBarUn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ)
    (θ₁ θ₂ : ℝ)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    ContinuousOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hA : Continuous (fun σ : ℝ => pczArcA S t₁ (σ / (Real.pi / 2))) :=
    (pccontinuous_zArcA S t₁).comp (by fun_prop)
  have hB : Continuous (fun σ : ℝ => pczArcB S θ₁ θ₂ ((σ - Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_zArcB S θ₁ θ₂).comp (by fun_prop)
  have hC : Continuous (fun σ : ℝ => pczArcC S t₂ ((σ - Real.pi) / (Real.pi / 2))) :=
    (pccontinuous_zArcC S t₂).comp (by fun_prop)
  have hD : Continuous (fun σ : ℝ => pczArcD S ((σ - 3 * Real.pi / 2) / (Real.pi / 2))) :=
    (pccontinuous_zArcD S).comp (by fun_prop)
  have h1 : ContinuousOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Icc 0 (Real.pi / 2)) :=
    hA.continuousOn.congr fun σ hσ => by
      unfold pczBarUn; rw [if_pos hσ.2]
  have h2 : ContinuousOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Icc (Real.pi / 2) Real.pi) :=
    hB.continuousOn.congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have hσeq : σ = Real.pi / 2 := le_antisymm hσa hσ.1
        subst hσeq
        exact pczBarUn_junction1 S t₁ t₂ θ₁ θ₂ hθ₁
      · unfold pczBarUn; rw [if_neg hσa, if_pos hσ.2]
  have h3 : ContinuousOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Icc Real.pi (3 * Real.pi / 2)) :=
    hC.continuousOn.congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : Real.pi ≤ Real.pi / 2 := le_trans hσ.1 hσa; linarith
      · by_cases hσb : σ ≤ Real.pi
        · have hσeq : σ = Real.pi := le_antisymm hσb hσ.1
          subst hσeq
          exact pczBarUn_junction2 S t₁ t₂ θ₁ θ₂ hθ₂
        · unfold pczBarUn; rw [if_neg hσa, if_neg hσb, if_pos hσ.2]
  have h4 : ContinuousOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :=
    hD.continuousOn.congr fun σ hσ => by
      by_cases hσa : σ ≤ Real.pi / 2
      · have : 3 * Real.pi / 2 ≤ Real.pi / 2 := le_trans hσ.1 hσa; linarith
      · by_cases hσb : σ ≤ Real.pi
        · have : 3 * Real.pi / 2 ≤ Real.pi := le_trans hσ.1 hσb; linarith
        · by_cases hσc : σ ≤ 3 * Real.pi / 2
          · have hσeq : σ = 3 * Real.pi / 2 := le_antisymm hσc hσ.1
            subst hσeq
            exact pczBarUn_junction3 S t₁ t₂ θ₁ θ₂
          · unfold pczBarUn; rw [if_neg hσa, if_neg hσb, if_neg hσc]
  have h12 := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rw [Set.Icc_union_Icc_eq_Icc (by linarith : (0:ℝ) ≤ Real.pi / 2)
    (by linarith : Real.pi / 2 ≤ Real.pi)] at h12
  have h34 := h3.union_of_isClosed h4 isClosed_Icc isClosed_Icc
  rw [Set.Icc_union_Icc_eq_Icc (by linarith : Real.pi ≤ 3 * Real.pi / 2)
    (by linarith : 3 * Real.pi / 2 ≤ 2 * Real.pi)] at h34
  have h1234 := h12.union_of_isClosed h34 isClosed_Icc isClosed_Icc
  rwa [Set.Icc_union_Icc_eq_Icc (by linarith : (0:ℝ) ≤ Real.pi)
    (by linarith : Real.pi ≤ 2 * Real.pi)] at h1234

end ZbarCont


section ZbarContinuous

theorem pcperPt_two_pi : Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) = 0 := by
  rw [show Work.Smooth.SphereJordan.pcperPt (2 * Real.pi) =
      2 * Real.pi - (⌊2 * Real.pi / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
  rw [div_self (by positivity : (2 : ℝ) * Real.pi ≠ 0),
    show ⌊(1 : ℝ)⌋ = 1 from Int.floor_one]
  norm_num

theorem pcZbar_periodic (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ) :
    Function.Periodic (pcZbar S t₁ t₂ θ₁ θ₂) (2 * Real.pi) := by
  intro σ
  rw [pcZbar, pcZbar, Work.Smooth.SphereJordan.pcperPt_shift]

section Copied

/-- **The exterior of a disc is preconnected.** -/
theorem pcisPreconnected_far' {R : ℝ} (hR : 0 < R) : IsPreconnected {w : ℂ | R < ‖w‖} := by
  have hpre0 : IsPreconnected {w : ℂ | (1:ℝ) < ‖w‖} :=
    Work.Smooth.Jordan.isPreconnected_exterior_unitBall
  have himg := hpre0.image (fun w : ℂ => R * w) ((continuous_const.mul continuous_id).continuousOn)
  have heq : (fun w : ℂ => R * w) '' {w : ℂ | (1:ℝ) < ‖w‖} = {w : ℂ | R < ‖w‖} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hnorm : ‖R * v‖ = R * ‖v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      rw [Set.mem_ofPred_eq, hnorm]
      simpa using mul_lt_mul_of_pos_left hv hR
    · intro hw
      refine ⟨R⁻¹ * w, ?_, ?_⟩
      · have hnorm : ‖R⁻¹ * w‖ = R⁻¹ * ‖w‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
        rw [Set.mem_ofPred_eq, hnorm, inv_mul_eq_div, one_lt_div hR]
        exact hw
      · have hRne : ((R : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
        show (fun w : ℂ => R * w) (R⁻¹ * w) = w
        push_cast
        field_simp
  rwa [heq] at himg

/-- **The winding number is locally constant off the trace of a plane curve.** -/
theorem pcwindNumber_eq_of_preconnected' (c : Work.Smooth.Jordan.PlaneCurve) {W : Set ℂ}
    (hW : IsPreconnected W) (hsub : W ⊆ c.traceᶜ) {p q : ℂ} (hp : p ∈ W) (hq : q ∈ W) :
    Work.Smooth.SphereJordan.windNumber c.γ c.cont p =
      Work.Smooth.SphereJordan.windNumber c.γ c.cont q := by
  haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp ⟨⟨p, hp⟩, hW⟩
  have hball' : ∀ {z : ℂ}, z ∈ W → ∃ ε > 0, Metric.ball z ε ⊆ c.traceᶜ := by
    intro z hz
    exact Metric.isOpen_iff.mp c.isOpen_compl_trace z (hsub hz)
  have hloc : IsLocallyConstant
      (fun z : W => Work.Smooth.SphereJordan.windNumber c.γ c.cont z.1) := by
    intro t
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hball⟩ := hball' z.2
    have hmem : Subtype.val ⁻¹' Metric.ball z.1 ε ∈ nhds z :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    have hyB : y.1 ∈ Metric.ball z.1 ε := hy
    have hzB : z.1 ∈ Metric.ball z.1 ε := Metric.mem_ball_self hε
    have hconst : Work.Smooth.SphereJordan.windNumber c.γ c.cont y.1 =
        Work.Smooth.SphereJordan.windNumber c.γ c.cont z.1 := by
      refine Work.Smooth.SphereJordan.windNumber_eq_of_segment c.cont c.periodic
        (fun t ht => ?_) (fun t ht => ?_) (fun t s hs => ?_)
      · exact hball hyB ⟨t, ht⟩
      · exact hball hzB ⟨t, ht⟩
      · have hconv : Convex ℝ (Metric.ball (z.1 : ℂ) ε) := convex_ball _ _
        have hmem : (1 - s) • (↑y : ℂ) + s • (↑z : ℂ) ∈ Metric.ball z.1 ε :=
          hconv hyB hzB (by linarith [hs.1, hs.2]) hs.1 (by ring)
        have hgoal : ((1 - s : ℝ) : ℂ) * (↑y) + (s : ℂ) * (↑z) ∈ Metric.ball z.1 ε := by
          simpa [Complex.real_smul] using hmem
        intro h
        exact hball hgoal ⟨t, by rw [h]; push_cast; ring⟩
    change Work.Smooth.SphereJordan.windNumber c.γ c.cont y.1 ∈ t
    rw [hconst]
    exact hz
  have hcont : Continuous (fun z : W => Work.Smooth.SphereJordan.windNumber c.γ c.cont z.1) :=
    hloc.continuous
  have hpre : IsPreconnected
      (Set.range (fun z : W => Work.Smooth.SphereJordan.windNumber c.γ c.cont z.1)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ hcont.continuousOn
  have hmem : Work.Smooth.SphereJordan.windNumber c.γ c.cont p ∈
      Set.range (fun z : W => Work.Smooth.SphereJordan.windNumber c.γ c.cont z.1) :=
    ⟨⟨p, hp⟩, rfl⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre)
    ({Work.Smooth.SphereJordan.windNumber c.γ c.cont p} : Set ℤ)
    ({Work.Smooth.SphereJordan.windNumber c.γ c.cont p}ᶜ) (isClosed_discrete _)
    (isClosed_discrete _)
    (fun x _ => by by_cases h : x = Work.Smooth.SphereJordan.windNumber c.γ c.cont p <;>
      simp [h]) (by simp) with h | h
  · exact (Set.mem_singleton_iff.mp (h ⟨⟨q, hq⟩, rfl⟩)).symm
  · exact absurd (h hmem) (by simp)

/-- **The winding number vanishes on the unbounded side** of a simple closed plane curve. -/
theorem pcwindNumber_eq_zero_of_mem_U' {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation c) {p : ℂ} (hp : p ∈ h.U) :
    Work.Smooth.SphereJordan.windNumber c.γ c.cont p = 0 := by
  obtain ⟨C, hC⟩ := c.isCompact_trace.isBounded.exists_norm_le
  obtain ⟨D, hD⟩ := h.bounded_V.exists_norm_le
  set R : ℝ := max C D + 1 with hRdef
  have hCR : C < R := by rw [hRdef]; exact lt_of_le_of_lt (le_max_left C D) (lt_add_one _)
  have hDR : D < R := by rw [hRdef]; exact lt_of_le_of_lt (le_max_right C D) (lt_add_one _)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (c.mem_trace 0))
  have hR0 : 0 < R := by rw [hRdef]; linarith [hC0, le_max_left C D]
  have hfarU : ∀ z : ℂ, R < ‖z‖ → z ∈ h.U := by
    intro z hz
    have hsub : {w : ℂ | R < ‖w‖} ⊆ c.traceᶜ := by
      intro w hw hwt
      obtain ⟨t, rfl⟩ := hwt
      have h1 : ‖c.γ t‖ ≤ C := hC _ (c.mem_trace t)
      exact absurd (lt_of_le_of_lt h1 hCR) (not_lt.mpr (le_of_lt hw))
    have hpre : IsPreconnected {w : ℂ | R < ‖w‖} := pcisPreconnected_far' hR0
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset h hpre hsub with hU | hV
    · exact hU hz
    · have h1 : ‖z‖ ≤ D := hD z (hV hz)
      linarith [hDR]
  set p₀ : ℂ := -(((R + 1 : ℝ)) : ℂ) with hp₀def
  have hp₀norm : ‖p₀‖ = R + 1 := by
    rw [hp₀def, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hR0])]
  have hp₀U : p₀ ∈ h.U := hfarU p₀ (by rw [hp₀norm]; exact lt_add_one R)
  have hp₀zero : Work.Smooth.SphereJordan.windNumber c.γ c.cont p₀ = 0 := by
    have hbdd : ∀ t : ℝ, ‖c.γ t‖ ≤ R := fun t =>
      le_of_lt (lt_of_le_of_lt (hC _ (c.mem_trace t)) hCR)
    exact Work.Smooth.SphereJordan.windNumber_eq_zero_of_norm_gt c.cont c.periodic hbdd
      (by rw [hp₀norm]; exact lt_add_one R)
  rw [pcwindNumber_eq_of_preconnected' c h.preconn_U
    (fun z hz => by rw [← h.union_eq]; exact Or.inl hz) hp hp₀U, hp₀zero]

/-- **A point off the trace with nonzero winding number lies on the bounded side.** -/
theorem pcmem_V_of_windNumber_ne_zero' {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {z : ℂ} (hz : z ∉ γ.trace)
    (h : Work.Smooth.SphereJordan.windNumber γ.γ γ.cont z ≠ 0) : z ∈ S.V := by
  by_contra hV
  have hU : z ∈ S.U := by
    have hmem : z ∈ S.U ∪ S.V := by
      rw [S.union_eq]; exact hz
    exact hmem.resolve_right hV
  exact h (pcwindNumber_eq_zero_of_mem_U' S.toPlaneSeparation hU)

/-- **Multiplying a path by a nonzero constant does not change its increment.** -/
theorem pcpathIncTot_const_mul' (u : ℂ) (hu : u ≠ 0) (p : C(unitInterval, ℂ)) :
    Work.SphereJordan.pathIncTot (ContinuousMap.const unitInterval u * p) =
      Work.SphereJordan.pathIncTot p := by
  by_cases hp : ∀ t, p t ≠ 0
  · have hup : ∀ t, (ContinuousMap.const unitInterval u * p) t ≠ 0 := fun t =>
      mul_ne_zero hu (hp t)
    obtain ⟨Λ, hΛ, -, -⟩ := Work.Smooth.SphereJordan.argChangeLift p hp
    have hΛu : ∀ t,
        Complex.exp ((ContinuousMap.const unitInterval (Complex.log u) + Λ) t) =
          (ContinuousMap.const unitInterval u * p) t := by
      intro t
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.mul_apply,
        Complex.exp_add, Complex.exp_log hu, hΛ t]
    rw [Work.SphereJordan.pathIncTot_eq_of_lift _ hup _ hΛu,
      Work.SphereJordan.pathIncTot_eq_of_lift p hp Λ hΛ]
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  · have hup : ¬ ∀ t, (ContinuousMap.const unitInterval u * p) t ≠ 0 := by
      intro h
      obtain ⟨t, ht⟩ := not_forall.mp hp
      have ht' : p t = 0 := by simpa using ht
      exact h t (by rw [ContinuousMap.mul_apply, ContinuousMap.const_apply, ht', mul_zero])
    unfold Work.SphereJordan.pathIncTot
    rw [dif_neg hup, dif_neg hp]

end Copied

theorem pcZbar_continuous_periodic (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ)
    (θ₁ θ₂ : ℝ)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Continuous (pcZbar S t₁ t₂ θ₁ θ₂) ∧
      Function.Periodic (pcZbar S t₁ t₂ θ₁ θ₂) (2 * Real.pi) := by
  have hG := pccontinuousOn_zBarUn S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂
  have hG0 : pczBarUn S t₁ t₂ θ₁ θ₂ 0 = pczBarUn S t₁ t₂ θ₁ θ₂ (2 * Real.pi) :=
    pczBarUn_periodic_shift S t₁ t₂ θ₁ θ₂
  have hper : Function.Periodic (pcZbar S t₁ t₂ θ₁ θ₂) (2 * Real.pi) :=
    pcZbar_periodic S t₁ t₂ θ₁ θ₂
  have hEq : Set.EqOn (pcZbar S t₁ t₂ θ₁ θ₂) (pczBarUn S t₁ t₂ θ₁ θ₂)
      (Set.Icc 0 (2 * Real.pi)) := by
    intro σ hσ
    rw [pcZbar]
    by_cases h : σ = 2 * Real.pi
    · subst h
      rw [pcperPt_two_pi, hG0]
    · rw [pcperPt_self' ⟨hσ.1, lt_of_le_of_ne hσ.2 h⟩]
  have hcont : ContinuousOn (pcZbar S t₁ t₂ θ₁ θ₂) (Set.Icc 0 (2 * Real.pi)) := hG.congr hEq
  have hcont' : ContinuousOn (pcZbar S t₁ t₂ θ₁ θ₂) (Set.Icc (-(2 * Real.pi)) (2 * Real.pi)) := by
    have hleft : ContinuousOn (pcZbar S t₁ t₂ θ₁ θ₂) (Set.Icc (-(2 * Real.pi)) 0) := by
      have hmap : Set.MapsTo (fun y : ℝ => y + 2 * Real.pi) (Set.Icc (-(2 * Real.pi)) 0)
          (Set.Icc 0 (2 * Real.pi)) := by
        intro y hy
        simp only [Set.mem_Icc] at hy ⊢
        exact ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩
      have hshift : ContinuousOn ((pcZbar S t₁ t₂ θ₁ θ₂) ∘ (fun y : ℝ => y + 2 * Real.pi))
          (Set.Icc (-(2 * Real.pi)) 0) :=
        ContinuousOn.comp hcont ((continuous_id.add continuous_const).continuousOn) hmap
      rwa [show ((pcZbar S t₁ t₂ θ₁ θ₂) ∘ (fun y : ℝ => y + 2 * Real.pi)) =
          (pcZbar S t₁ t₂ θ₁ θ₂) from funext fun y => hper y] at hshift
    have hjoin := hleft.union_of_isClosed hcont isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos] : (-(2 * Real.pi) : ℝ) ≤ 0)
      (by linarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi)] at hjoin
  refine ⟨?_, hper⟩
  rw [continuous_iff_continuousAt]
  intro τ
  have hmem := pcperPt_mem' τ
  have hc : ContinuousAt (pcZbar S t₁ t₂ θ₁ θ₂) (Work.Smooth.SphereJordan.pcperPt τ) := by
    rcases eq_or_ne (Work.Smooth.SphereJordan.pcperPt τ) 0 with h0 | h0
    · have hnb : Set.Icc (-(2 * Real.pi)) (2 * Real.pi) ∈
          nhds (Work.Smooth.SphereJordan.pcperPt τ) := by
        rw [h0]
        exact Filter.mem_of_superset
          (isOpen_Ioo.mem_nhds (by constructor <;> linarith [Real.pi_pos]))
          Set.Ioo_subset_Icc_self
      exact (hcont'.continuousWithinAt
        ⟨by linarith [hmem.1, Real.pi_pos], hmem.2.le⟩).continuousAt hnb
    · have hpos : 0 < Work.Smooth.SphereJordan.pcperPt τ :=
        lt_of_le_of_ne hmem.1 (Ne.symm h0)
      have hnb : Set.Icc 0 (2 * Real.pi) ∈ nhds (Work.Smooth.SphereJordan.pcperPt τ) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hpos, hmem.2⟩) Set.Ioo_subset_Icc_self
      exact (hcont.continuousWithinAt ⟨hmem.1, hmem.2.le⟩).continuousAt hnb
  have hdecomp : τ = Work.Smooth.SphereJordan.pcperPt τ +
      (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) := by
    rw [show Work.Smooth.SphereJordan.pcperPt τ =
      τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) from rfl]
    ring
  rw [hdecomp]
  have hX : Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
      ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi) =
      Work.Smooth.SphereJordan.pcperPt τ := by
    push_cast; ring
  have heq : (pcZbar S t₁ t₂ θ₁ θ₂) =
      ((pcZbar S t₁ t₂ θ₁ θ₂) ∘
        (fun z : ℝ => z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))) :=
    funext fun z => (hper.int_mul (-(⌊τ / (2 * Real.pi)⌋)) z).symm
  rw [heq]
  refine ContinuousAt.comp (f := fun z : ℝ =>
      z + ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    (x := Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)) ?_ ?_
  · change ContinuousAt (pcZbar S t₁ t₂ θ₁ θ₂)
      (Work.Smooth.SphereJordan.pcperPt τ + (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) +
        ((-(⌊τ / (2 * Real.pi)⌋) : ℤ) : ℝ) * (2 * Real.pi))
    rw [hX]
    exact hc
  · fun_prop

/-- The auxiliary plane curve. -/
def pczCurve (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ) (θ₁ θ₂ : ℝ)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := pcZbar S t₁ t₂ θ₁ θ₂
  cont := (pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1
  periodic := (pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).2

@[simp] theorem pczCurve_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ t₂ : ℝ)
    (θ₁ θ₂ : ℝ)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) (τ : ℝ) :
    (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).γ τ = pcZbar S t₁ t₂ θ₁ θ₂ τ := rfl

end ZbarContinuous


section Inj

theorem pczArcA_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) (y : ℝ) :
    pczArcA S t₁ y = (((pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := rfl

theorem pczArcC_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ) (y : ℝ) :
    pczArcC S t₂ y = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - y *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := rfl

theorem pczArcD_apply (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (y : ℝ) :
    pczArcD S y = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
      Complex.exp (((Real.pi * (1 - y) : ℝ) : ℂ) * Complex.I) := rfl

theorem pczArcA_coeff (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) (y : ℝ) :
    pczArcA S t₁ y = (((pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := rfl

theorem pcnorm_zArcD' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (y : ℝ) :
    ‖pczArcD S y‖ = pcRout := by
  rw [pczArcD_apply, norm_mul, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pcRout_pos,
    mul_one]

theorem pczArcA_slope_ne_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ)
    (h : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ < pcRout) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout ≠ 0 := by
  intro hc; linarith [h]

theorem pczArcC_slope_ne_zero (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ)
    (ht₂ : t₂ < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ ≠ 0 := by
  intro hc; linarith [ht₂]

theorem pczArcA_inj (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ)
    (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout ≠ 0) :
    Function.Injective (pczArcA S t₁) := by
  intro y₁ y₂ heq
  rw [pczArcA_apply, pczArcA_apply] at heq
  have h1 : (((pcRout + y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) =
      (((pcRout + y₂ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) :=
    mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) heq
  have h2 : pcRout + y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) =
      pcRout + y₂ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) :=
    Complex.ofReal_inj.mp h1
  have h4 : y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) =
      y₂ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) := by linarith
  exact mul_right_cancel₀ hne h4

theorem pczArcC_inj (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ)
    (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ ≠ 0) :
    Function.Injective (pczArcC S t₂) := by
  intro y₁ y₂ heq
  rw [pczArcC_apply, pczArcC_apply] at heq
  have h1 : (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - y₁ *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - y₂ *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) :=
    mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) heq
  have h2 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - y₁ *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) =
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - y₂ *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) := Complex.ofReal_inj.mp h1
  have h4 : y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) =
      y₂ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) := by linarith
  exact mul_right_cancel₀ hne h4

theorem pczChordPt_apply {θ₁ θ₂ : ℝ} {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1) :
    ((pczChordPt θ₁ θ₂ y : Work.Smooth.Jordan.Disc) : ℂ) =
      (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) + ((y : ℝ) : ℂ) *
        ((Work.Smooth.Jordan.circlePoint θ₂ : ℂ) - (Work.Smooth.Jordan.circlePoint θ₁ : ℂ)) := by
  show ((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) = _
  rw [pczc_of_mem hy]
  push_cast
  ring

theorem pczChordPt_inj {θ₁ θ₂ : ℝ} (hne : Work.Smooth.Jordan.circlePoint θ₁ ≠
    Work.Smooth.Jordan.circlePoint θ₂) :
    Set.InjOn (pczChordPt θ₁ θ₂) (Set.Icc (0:ℝ) 1) := by
  intro y₁ hy₁ y₂ hy₂ heq
  have h := congrArg (fun d : Work.Smooth.Jordan.Disc => (d : ℂ)) heq
  rw [pczChordPt_apply hy₁, pczChordPt_apply hy₂] at h
  have h2 : ((y₁ : ℝ) : ℂ) * ((Work.Smooth.Jordan.circlePoint θ₂ : ℂ) -
      (Work.Smooth.Jordan.circlePoint θ₁ : ℂ)) =
      ((y₂ : ℝ) : ℂ) * ((Work.Smooth.Jordan.circlePoint θ₂ : ℂ) -
        (Work.Smooth.Jordan.circlePoint θ₁ : ℂ)) := add_left_cancel h
  have hd : (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) -
      (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) ≠ 0 := by
    intro hc
    refine hne ?_
    apply Subtype.ext
    exact (sub_eq_zero.mp hc).symm
  have h3 : ((y₁ : ℝ) : ℂ) = ((y₂ : ℝ) : ℂ) := mul_right_cancel₀ hd h2
  exact Complex.ofReal_inj.mp h3

theorem pczArcB_inj (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ)
    (hne : Work.Smooth.Jordan.circlePoint θ₁ ≠ Work.Smooth.Jordan.circlePoint θ₂) :
    Set.InjOn (pczArcB S θ₁ θ₂) (Set.Icc (0:ℝ) 1) := by
  intro y₁ hy₁ y₂ hy₂ heq
  exact pczChordPt_inj hne hy₁ hy₂ (S.inj heq)

theorem pcnorm_zArcB_lt_one (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (y : ℝ) : ‖pczArcB S θ₁ θ₂ y‖ < 1 := by
  have hmem : pczArcB S θ₁ θ₂ y ∈ closure S.V := by
    have h2 : pczArcB S θ₁ θ₂ y ∈ Set.range S.e := Set.mem_range_self _
    rwa [S.range_e] at h2
  exact Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball hmem


theorem pczBarUn_q0 {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ t₂ θ₁ θ₂ σ : ℝ}
    (h : σ ≤ Real.pi / 2) :
    pczBarUn S t₁ t₂ θ₁ θ₂ σ = pczArcA S t₁ (σ / (Real.pi / 2)) := by
  unfold pczBarUn; rw [if_pos h]

theorem pczBarUn_q1 {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ t₂ θ₁ θ₂ σ : ℝ}
    (h0 : ¬ σ ≤ Real.pi / 2) (h1 : σ ≤ Real.pi) :
    pczBarUn S t₁ t₂ θ₁ θ₂ σ = pczArcB S θ₁ θ₂ ((σ - Real.pi / 2) / (Real.pi / 2)) := by
  unfold pczBarUn; rw [if_neg h0, if_pos h1]

theorem pczBarUn_q2 {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ t₂ θ₁ θ₂ σ : ℝ}
    (h0 : ¬ σ ≤ Real.pi / 2) (h1 : ¬ σ ≤ Real.pi) (h2 : σ ≤ 3 * Real.pi / 2) :
    pczBarUn S t₁ t₂ θ₁ θ₂ σ = pczArcC S t₂ ((σ - Real.pi) / (Real.pi / 2)) := by
  unfold pczBarUn; rw [if_neg h0, if_neg h1, if_pos h2]

theorem pczBarUn_q3 {S : Work.Smooth.Jordan.PlaneSchoenflies γ} {t₁ t₂ θ₁ θ₂ σ : ℝ}
    (h0 : ¬ σ ≤ Real.pi / 2) (h1 : ¬ σ ≤ Real.pi) (h2 : ¬ σ ≤ 3 * Real.pi / 2) :
    pczBarUn S t₁ t₂ θ₁ θ₂ σ = pczArcD S ((σ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
  unfold pczBarUn; rw [if_neg h0, if_neg h1, if_neg h2]

theorem pcdiv_cancel_half {y : ℝ} : y / (Real.pi / 2) * (Real.pi / 2) = y :=
  div_mul_cancel₀ y (by positivity : Real.pi / 2 ≠ 0)

theorem pchalf_pos : (0:ℝ) < Real.pi / 2 := by positivity

theorem pczChordPt_eq_one {θ₁ θ₂ : ℝ} {y : ℝ} (hy : y ≤ 0) :
    pczChordPt θ₁ θ₂ y = Work.Smooth.Jordan.circlePoint θ₁ := by
  apply Subtype.ext
  show ((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) =
      ((Work.Smooth.Jordan.circlePoint θ₁ : Work.Smooth.Jordan.Disc) : ℂ)
  rw [pczc_eq_zero_of_nonpos hy]
  push_cast
  ring

theorem pczChordPt_eq_two {θ₁ θ₂ : ℝ} {y : ℝ} (hy : 1 ≤ y) :
    pczChordPt θ₁ θ₂ y = Work.Smooth.Jordan.circlePoint θ₂ := by
  apply Subtype.ext
  show ((1 - pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      ((pczc y : ℝ) : ℂ) * (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) =
      ((Work.Smooth.Jordan.circlePoint θ₂ : Work.Smooth.Jordan.Disc) : ℂ)
  rw [pczc_eq_one_of_one_le hy]
  push_cast
  ring

theorem pccirclePoint_mem_closedBall' (θ : ℝ) :
    (Work.Smooth.Jordan.circlePoint θ : ℂ) ∈ Metric.closedBall (0:ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Work.Smooth.Jordan.circlePoint_coe,
    Complex.norm_exp_ofReal_mul_I]

theorem pczChordPt_norm_lt {θ₁ θ₂ : ℝ} (hne : Work.Smooth.Jordan.circlePoint θ₁ ≠
    Work.Smooth.Jordan.circlePoint θ₂) {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    ‖((pczChordPt θ₁ θ₂ y : Work.Smooth.Jordan.Disc) : ℂ)‖ < 1 := by
  have hne' : ((Work.Smooth.Jordan.circlePoint θ₁ : Work.Smooth.Jordan.Disc) : ℂ) ≠
      ((Work.Smooth.Jordan.circlePoint θ₂ : Work.Smooth.Jordan.Disc) : ℂ) :=
    fun h => hne (Subtype.ext h)
  have hcv : (1 - y) • (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) +
      y • (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) ∈
      interior (Metric.closedBall (0:ℂ) 1) :=
    (strictConvex_closedBall ℝ (0:ℂ) 1) (pccirclePoint_mem_closedBall' θ₁)
      (pccirclePoint_mem_closedBall' θ₂) hne' (by linarith) hy0 (by ring)
  rw [interior_closedBall (0:ℂ) (by norm_num : (1:ℝ) ≠ 0), Metric.mem_ball,
    dist_zero_right] at hcv
  rw [show ((pczChordPt θ₁ θ₂ y : Work.Smooth.Jordan.Disc) : ℂ) =
      (1 - y) • (Work.Smooth.Jordan.circlePoint θ₁ : ℂ) + y • (Work.Smooth.Jordan.circlePoint θ₂ : ℂ) from by
    show ((1 - pczc y : ℝ) : ℂ) * _ + ((pczc y : ℝ) : ℂ) * _ = _
    rw [pczc_of_mem ⟨hy0.le, hy1.le⟩, Complex.real_smul, Complex.real_smul]]
  exact hcv

theorem pczArcB_mem (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ)
    (hne : Work.Smooth.Jordan.circlePoint θ₁ ≠ Work.Smooth.Jordan.circlePoint θ₂) (y : ℝ) :
    pczArcB S θ₁ θ₂ y ∈ S.V ∪ {γ.γ θ₁, γ.γ θ₂} := by
  by_cases hy : y ≤ 0
  · right; left
    show pczArcB S θ₁ θ₂ y = γ.γ θ₁
    unfold pczArcB
    rw [pczChordPt_eq_one hy]
    exact S.boundary θ₁
  · rw [not_le] at hy
    by_cases hy1 : 1 ≤ y
    · right; right
      show pczArcB S θ₁ θ₂ y = γ.γ θ₂
      unfold pczArcB
      rw [pczChordPt_eq_two hy1]
      exact S.boundary θ₂
    · left
      rw [not_le] at hy1
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨pczChordPt θ₁ θ₂ y, pczChordPt_norm_lt hne hy hy1, rfl⟩

theorem pczArcD_inj (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Set.InjOn (pczArcD (γ := γ) S) (Set.Icc (0:ℝ) 1) := by
  intro y₁ hy₁ y₂ hy₂ heq
  have h1 : Complex.exp (((Real.pi * (1 - y₁) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * (1 - y₂) : ℝ) : ℂ) * Complex.I) := by
    rw [pczArcD_apply, pczArcD_apply] at heq
    exact mul_left_cancel₀ (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt pcRout_pos))
      (Work.Smooth.SphereJordan.pccutDir_ne_zero S)) heq
  have h2 : Complex.exp (((Real.pi * (1 - y₁) : ℝ) : ℂ) * Complex.I -
      ((Real.pi * (1 - y₂) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
  have h3 : ((Real.pi * (y₂ - y₁) : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have h4 : ((Real.pi * (1 - y₁) : ℝ) : ℂ) * Complex.I -
        ((Real.pi * (1 - y₂) : ℝ) : ℂ) * Complex.I =
        ((Real.pi * (y₂ - y₁) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h4] at hn
    have h5 : (n : ℂ) * (2 * Real.pi * Complex.I) =
        ((n : ℂ) * (2 * Real.pi)) * Complex.I := by ring
    rw [h5] at hn
    exact mul_right_cancel₀ Complex.I_ne_zero hn
  have h6 : Real.pi * (y₂ - y₁) = (n : ℝ) * (2 * Real.pi) := by
    have h7 : ((Real.pi * (y₂ - y₁) : ℝ) : ℂ) = ((n * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [h3]; push_cast; ring
    exact Complex.ofReal_inj.mp h7
  have h8 : y₂ - y₁ = (n : ℝ) * 2 := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    nlinarith [h6, Real.pi_pos]
  have h9 : (n : ℝ) = 0 := by
    have hb : |y₂ - y₁| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hy₁.2, hy₂.1], by linarith [hy₂.2, hy₁.1]⟩
    have h10 : |(n : ℝ) * 2| ≤ 1 := by rw [← h8]; exact hb
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))] at h10
    have h7 : |(n : ℝ)| < 1 := by linarith
    have hn0 : n = 0 := by
      have h11 := abs_lt.mp h7
      have h12 : (-1 : ℤ) < n := by exact_mod_cast h11.1
      have h13 : n < 1 := by exact_mod_cast h11.2
      omega
    rw [hn0]; norm_num
  rw [h9] at h8
  linarith

end Inj

section Main

theorem pcy0_mem {σ : ℝ} (h0 : 0 ≤ σ) (h : σ ≤ Real.pi / 2) :
    σ / (Real.pi / 2) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨div_nonneg h0 (le_of_lt pchalf_pos), (div_le_one (pchalf_pos)).mpr h⟩

theorem pcy1_mem {σ : ℝ} (h0 : Real.pi / 2 ≤ σ) (h : σ ≤ Real.pi) :
    (σ - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨div_nonneg (by linarith) (le_of_lt pchalf_pos),
    (div_le_one (pchalf_pos)).mpr (by linarith)⟩

theorem pcy2_mem {σ : ℝ} (h0 : Real.pi ≤ σ) (h : σ ≤ 3 * Real.pi / 2) :
    (σ - Real.pi) / (Real.pi / 2) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨div_nonneg (by linarith) (le_of_lt pchalf_pos),
    (div_le_one (pchalf_pos)).mpr (by linarith)⟩

theorem pcy3_mem {σ : ℝ} (h0 : 3 * Real.pi / 2 ≤ σ) (h : σ ≤ 2 * Real.pi) :
    (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0:ℝ) 1 :=
  ⟨div_nonneg (by linarith) (le_of_lt pchalf_pos),
    (div_le_one (pchalf_pos)).mpr (by linarith)⟩

/-- The first arc, written as a real multiple of `pccutDir S`. -/
theorem pczArcA_eq_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) (y : ℝ) :
    pczArcA S t₁ y = ((pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) •
      Work.Smooth.SphereJordan.pccutDir S := by
  rw [pczArcA_apply, Complex.real_smul]

/-- The third arc, written as a real multiple of `pccutDir S`. -/
theorem pczArcC_eq_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ) (y : ℝ) :
    pczArcC S t₂ y = ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) •
      Work.Smooth.SphereJordan.pccutDir S := by
  rw [pczArcC_apply, Complex.real_smul]

/-- The norm of a point of the first arc. -/
theorem pcnorm_zArcA' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) (y : ℝ) :
    ‖pczArcA S t₁ y‖ = |pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout)| := by
  rw [pczArcA_eq_smul, norm_smul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one, Real.norm_eq_abs]

/-- The norm of a point of the third arc. -/
theorem pcnorm_zArcC' (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ) (y : ℝ) :
    ‖pczArcC S t₂ y‖ = |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| := by
  rw [pczArcC_eq_smul, norm_smul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one, Real.norm_eq_abs]

/-- The fourth arc, written as a real multiple of the unit vector `pccutDir S * exp (i π (1-y))`. -/
theorem pczArcD_eq_smul (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (y : ℝ) :
    pczArcD S y = (pcRout : ℝ) •
      (Work.Smooth.SphereJordan.pccutDir S *
        Complex.exp (((Real.pi * (1 - y) : ℝ) : ℂ) * Complex.I)) := by
  rw [pczArcD_apply, Complex.real_smul]
  ring

section Injectivity

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)

/-- `‖pcbase S‖ + s₁ = 1` when the first crosscut ends at `pccutDir S`. -/
theorem pcbase_add_s₁ {s₁ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ = 1 := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have key : (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = (1 : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    have hb : (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ)) *
        Work.Smooth.SphereJordan.pccutDir S = (Work.Smooth.SphereJordan.pcbase S : ℂ) :=
      (Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S).symm
    rw [Complex.ofReal_add, add_mul, hb, one_mul]
    exact hout₁
  have h3 : ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    have h2 := mul_right_cancel₀ hu key
    rw [h2]; norm_num
  exact Complex.ofReal_inj.mp h3

/-- `‖pcbase S‖ - s₂ = -1` when the second crosscut ends at `-pccutDir S`. -/
theorem pcbase_sub_s₂ {s₂ : ℝ}
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ = -1 := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have key : (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = (-1 : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    have hb : (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ)) *
        Work.Smooth.SphereJordan.pccutDir S = (Work.Smooth.SphereJordan.pcbase S : ℂ) :=
      (Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S).symm
    rw [Complex.ofReal_sub, sub_mul, hb, neg_one_mul]
    exact hout₂
  have h3 : ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
    have h2 := mul_right_cancel₀ hu key
    rw [h2]; norm_num
  exact Complex.ofReal_inj.mp h3

/-- The inner endpoint of the first crosscut, as a real multiple of `pccutDir S`. -/
theorem pca₁_smul (t₁ : ℝ) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  conv_lhs => rw [Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]
  rw [← add_mul, Complex.ofReal_add]

/-- The inner endpoint of the second crosscut, as a real multiple of `pccutDir S`. -/
theorem pca₂_smul (t₂ : ℝ) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  conv_lhs => rw [Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]
  rw [← sub_mul, Complex.ofReal_sub]

/-- The coordinate `‖pcbase S‖ + t₁` of the first inner endpoint lies in `(0,1)`. -/
theorem pcbase_add_t₁_mem {t₁ θ₁ : ℝ} (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) (ht₁ : 0 < t₁) :
    0 < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ∧
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ < 1 := by
  have hval : γ.γ θ₁ = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by rw [hθ₁]; exact pca₁_smul S t₁
  have hnorm : ‖γ.γ θ₁‖ = |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁| := by
    rw [hval, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have h1 := hball θ₁
  rw [hnorm] at h1
  have hb := norm_nonneg (Work.Smooth.SphereJordan.pcbase S : ℂ)
  constructor
  · linarith
  · rcases abs_lt.mp h1 with ⟨h2, h3⟩; exact h3

/-- The coordinate `‖pcbase S‖ - t₂` of the second inner endpoint lies in `(-1,1)`. -/
theorem pcbase_sub_t₂_mem {t₂ θ₂ : ℝ} (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    -1 < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ ∧
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ < 1 := by
  have hval : γ.γ θ₂ = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by rw [hθ₂]; exact pca₂_smul S t₂
  have hnorm : ‖γ.γ θ₂‖ = |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂| := by
    rw [hval, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have h1 := hball θ₂
  rw [hnorm] at h1
  rcases abs_lt.mp h1 with ⟨h2, h3⟩
  exact ⟨h2, h3⟩

/-- The two inner endpoints are distinct. -/
theorem pctheta_ne_of_cuts {t₁ t₂ θ₁ θ₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.Smooth.Jordan.circlePoint θ₁ ≠ Work.Smooth.Jordan.circlePoint θ₂ := by
  intro h
  have h1 : γ.γ θ₁ = γ.γ θ₂ := by rw [← S.boundary θ₁, ← S.boundary θ₂, h]
  rw [hθ₁, hθ₂] at h1
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have h2 : (((t₁ : ℂ) + (t₂ : ℂ))) * Work.Smooth.SphereJordan.pccutDir S = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have h4 : t₁ + t₂ = 0 := Complex.ofReal_inj.mp (by push_cast; exact h3)
    linarith
  · exact hu h3

/-- The coefficient of the first arc lies in `[‖pcbase S‖+t₁, pcRout]`. -/
theorem pczArcA_coef_bounds {t₁ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤
        pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) ∧
      pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) ≤ pcRout := by
  constructor <;> nlinarith [hy.1, hy.2, hτ, pcRout_pos]

/-- The coefficient of the third arc lies in `[-pcRout, ‖pcbase S‖-t₂]`. -/
theorem pczArcC_coef_bounds {t₂ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂) :
    -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) ∧
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) ≤
          ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ := by
  constructor <;> nlinarith [hy.1, hy.2, hτ, pcRout_pos]

/-- The first arc attains the radius `pcRout` only at the parameter `0`. -/
theorem pczArcA_coef_eq_Rout {t₁ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≠ pcRout) (h : y ≠ 0) :
    pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) ≠ pcRout := by
  intro hcon
  apply h
  have : y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact h1
  · exact absurd h1 (sub_ne_zero.mpr hne)

/-- The third arc attains the radius `-pcRout` only at the parameter `1`. -/
theorem pczArcC_coef_eq_negRout {t₂ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ ≠ 0) (h : y ≠ 1) :
    ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) ≠ -pcRout := by
  intro hcon
  apply h
  have hC : y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) =
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ := by linarith
  have h1 : (y - 1) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) = 0 := by
    nlinarith [hC]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linarith
  · exact absurd h2 hne

/-- Writing a point of the `pccutDir S` axis with a coefficient. -/
theorem pccoeff_smul_eq (α : ℝ) :
    (α : ℂ) * Work.Smooth.SphereJordan.pccutDir S = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      ((α - ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  have h1 : (α : ℂ) = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ +
      (α - ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  rw [h1, Complex.ofReal_add, add_mul, ← Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]

/-- Writing a point of the `pccutDir S` axis with a subtracted coefficient. -/
theorem pccoeff_smul_eq_sub (α : ℝ) :
    (α : ℂ) * Work.Smooth.SphereJordan.pccutDir S = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - α : ℝ) : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S := by
  have h1 : (α : ℂ) = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ -
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - α) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_sub]
    ring
  rw [h1, Complex.ofReal_sub, sub_mul, ← Work.Smooth.SphereJordan.pcbase_eq_smul_cutDir S]

/-- `pczArcB` maps the open interval into `S.V`. -/
theorem pczArcB_mem_V_of_Ioo {θ₁ θ₂ y : ℝ}
    (hne : Work.Smooth.Jordan.circlePoint θ₁ ≠ Work.Smooth.Jordan.circlePoint θ₂)
    (hy : y ∈ Set.Ioo (0:ℝ) 1) : pczArcB S θ₁ θ₂ y ∈ S.V := by
  rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
  exact ⟨pczChordPt θ₁ θ₂ y, pczChordPt_norm_lt hne hy.1 hy.2, rfl⟩

/-- `pczArcB` at a parameter `≥ 1` is the second inner endpoint. -/
theorem pczArcB_eq_a₂' {θ₁ θ₂ t₂ : ℝ} {y : ℝ} (hy : 1 ≤ y)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pczArcB S θ₁ θ₂ y = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcB
  rw [pczChordPt_eq_two hy, S.boundary θ₂]
  exact hθ₂

/-- `pczArcB` at a parameter `≤ 0` is the first inner endpoint. -/
theorem pczArcB_eq_a₁' {θ₁ θ₂ t₁ : ℝ} {y : ℝ} (hy : y ≤ 0)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    pczArcB S θ₁ θ₂ y = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  unfold pczArcB
  rw [pczChordPt_eq_one hy, S.boundary θ₁]
  exact hθ₁

/-- No point of the first arc lies in `S.V`. -/
theorem pczArcA_notMem_V (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ θ₁ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout) :
    pczArcA S t₁ y ∉ S.V := by
  intro hmem
  obtain ⟨hb1, hb2⟩ := pczArcA_coef_bounds S (t₁ := t₁) hy hτ
  have hVball : S.V ⊆ {z : ℂ | ‖z‖ < 1} := fun z hz =>
    Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball (subset_closure hz)
  have hVNsub : S.V ⊆ γ.traceᶜ := by
    intro z hz
    have h : z ∈ S.U ∪ S.V := Or.inr hz
    rwa [S.union_eq] at h
  have hs₁ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ = 1 := pcbase_add_s₁ S hout₁
  rcases lt_or_ge (pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout)) 1 with
    hlt | hge
  · have hσ1 : t₁ ≤ pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) -
        ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ := by linarith
    have hσ2 : pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) -
        ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ < s₁ := by linarith
    have hdecomp : pczArcA S t₁ y = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
        ((pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) -
          ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) *
          Work.Smooth.SphereJordan.pccutDir S := by
      rw [pczArcA_apply]
      exact pccoeff_smul_eq S _
    rcases lt_or_eq_of_le hσ1 with hlt' | heq
    · have hseg := hseg₁ _ hlt' hσ2
      exact hseg.2 (by rw [hdecomp] at hmem; exact hmem)
    · have hz : pczArcA S t₁ y = γ.γ θ₁ := by
        have h2 : pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) -
            ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ = t₁ := heq.symm
        rw [hdecomp, hθ₁, h2]
      exact hVNsub (hz ▸ hmem) ⟨θ₁, rfl⟩
  · have hnorm : ‖pczArcA S t₁ y‖ =
        pcRout + y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) := by
      rw [pczArcA_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hb1])]
    have hthis := hVball hmem
    simp only [Set.mem_setOf_eq] at hthis
    rw [hnorm] at hthis
    linarith

/-- No point of the third arc lies in `S.V`. -/
theorem pczArcC_notMem_V (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₂ s₂ θ₂ : ℝ}
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    {y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂) :
    pczArcC S t₂ y ∉ S.V := by
  intro hmem
  obtain ⟨hb1, hb2⟩ := pczArcC_coef_bounds S (t₂ := t₂) hy hτ
  have hVball : S.V ⊆ {z : ℂ | ‖z‖ < 1} := fun z hz =>
    Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball (subset_closure hz)
  have hVNsub : S.V ⊆ γ.traceᶜ := by
    intro z hz
    have h : z ∈ S.U ∪ S.V := Or.inr hz
    rwa [S.union_eq] at h
  have hs₂ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ = -1 := pcbase_sub_s₂ S hout₂
  rcases lt_or_ge (-1) (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) with hgt | hle
  · have hσ1 : t₂ ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ -
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
          y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) := by linarith
    have hσ2 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ -
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
          y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) < s₂ := by linarith
    have hdecomp : pczArcC S t₂ y = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
        ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
          y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) : ℝ) : ℂ) *
          Work.Smooth.SphereJordan.pccutDir S := by
      rw [pczArcC_apply]
      exact pccoeff_smul_eq_sub S _
    rcases lt_or_eq_of_le hσ1 with hlt' | heq
    · have hseg := hseg₂ _ hlt' hσ2
      exact hseg.2 (by rw [hdecomp] at hmem; exact hmem)
    · have hz : pczArcC S t₂ y = γ.γ θ₂ := by
        have h2 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ -
            (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
              y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) = t₂ := heq.symm
        rw [hdecomp, hθ₂, h2]
      exact hVNsub (hz ▸ hmem) ⟨θ₂, rfl⟩
  · have hnorm : ‖pczArcC S t₂ y‖ = |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| := by
      rw [pczArcC_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
    have habs : |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| =
        -(‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
          y * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) :=
      abs_of_nonpos (by linarith)
    have hthis := hVball hmem
    simp only [Set.mem_setOf_eq] at hthis
    rw [hnorm, habs] at hthis
    linarith

/-- `pczArcA` and `pczArcC` have disjoint images. -/
theorem pczArcA_ne_zArcC {t₁ t₂ y₁ y₂ : ℝ} (h1 : y₁ ∈ Set.Icc (0:ℝ) 1)
    (h2 : y₂ ∈ Set.Icc (0:ℝ) 1)
    (hτ1 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout)
    (hτ2 : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂) (ht : 0 < t₁ + t₂) :
    pczArcA S t₁ y₁ ≠ pczArcC S t₂ y₂ := by
  intro h
  rw [pczArcA_apply, pczArcC_apply] at h
  have key : (((pcRout + y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y₂ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) :=
    mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) h
  have hcoef := Complex.ofReal_inj.mp key
  have hA := (pczArcA_coef_bounds S (t₁ := t₁) h1 hτ1).1
  have hC := (pczArcC_coef_bounds S (t₂ := t₂) h2 hτ2).2
  linarith

/-- `pczArcA` and `pczArcD` have disjoint images (on half-open parameter ranges). -/
theorem pczArcA_ne_zArcD {t₁ y₁ y₂ : ℝ} (h1 : y₁ ∈ Set.Icc (0:ℝ) 1)
    (h2 : y₂ ∈ Set.Icc (0:ℝ) 1) (hτ1 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout)
    (ht₁ : 0 < t₁) (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≠ pcRout) (hy₂ : y₂ < 1) :
    pczArcA S t₁ y₁ ≠ pczArcD S y₂ := by
  intro h
  have hb1 := (pczArcA_coef_bounds S (t₁ := t₁) h1 hτ1).1
  have hn1 : ‖pczArcA S t₁ y₁‖ = pcRout + y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) := by
    rw [pczArcA_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hb1, norm_nonneg (Work.Smooth.SphereJordan.pcbase S : ℂ), ht₁])]
  have hn2 : ‖pczArcD S y₂‖ = pcRout := pcnorm_zArcD' S y₂
  have hc : pcRout + y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) = pcRout := by
    rw [← hn1, h, hn2]
  have hy₁ : y₁ = 0 := by
    have h' : y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h2' | h2'
    · exact h2'
    · exact absurd (sub_eq_zero.mp h2') hne
  rw [hy₁, pczArcA_zero] at h
  have hz : pczArcD S y₂ = ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S := h.symm
  have h3 : y₂ = 1 := (pczArcD_inj S (by norm_num : (1:ℝ) ∈ Set.Icc (0:ℝ) 1) h2
    (by rw [pczArcD_one]; exact hz.symm)).symm
  linarith

/-- `pczArcC` and `pczArcD` have disjoint images (on half-open parameter ranges). -/
theorem pczArcC_ne_zArcD {t₂ y₁ y₂ : ℝ} (h1 : y₁ ∈ Set.Icc (0:ℝ) 1)
    (h2 : y₂ ∈ Set.Icc (0:ℝ) 1) (hτ2 : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂)
    (hτ2' : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ < pcRout)
    (hne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ ≠ 0) (hy₂ : 0 < y₂) :
    pczArcC S t₂ y₁ ≠ pczArcD S y₂ := by
  intro h
  have hb2 := (pczArcC_coef_bounds S (t₂ := t₂) h1 hτ2).2
  have hn1 : ‖pczArcC S t₂ y₁‖ =
      |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| := by
    rw [pczArcC_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖pczArcD S y₂‖ = pcRout := pcnorm_zArcD' S y₂
  have habs : |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| = pcRout := by
    rw [← hn1, h, hn2]
  have hc : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
      y₁ * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) = -pcRout := by
    rcases (abs_eq (le_of_lt pcRout_pos)).mp habs with h' | h'
    · exfalso; linarith
    · exact h'
  have hz : pczArcC S t₂ y₁ = pczArcC S t₂ 1 := by
    rw [pczArcC_one, pczArcC_apply, hc]
    push_cast
    ring
  have hy₁ : y₁ = 1 := pczArcC_inj S t₂ hne hz
  rw [hy₁] at h
  have hz2 : pczArcD S y₂ = pczArcD S 0 := by
    rw [pczArcD_zero, ← h, pczArcC_one]
  have h3 : y₂ = 0 := pczArcD_inj S h2 (by norm_num : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) hz2
  linarith

/-- `pczArcB` and `pczArcD` have disjoint images. -/
theorem pczArcB_ne_zArcD {θ₁ θ₂ y₁ y₂ : ℝ} (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (h1 : y₁ ∈ Set.Icc (0:ℝ) 1) (h2 : y₂ ∈ Set.Icc (0:ℝ) 1) :
    pczArcB S θ₁ θ₂ y₁ ≠ pczArcD S y₂ := by
  intro h
  have hlt := pcnorm_zArcB_lt_one S θ₁ θ₂ hball y₁
  rw [h, pcnorm_zArcD'] at hlt
  linarith [pcone_lt_Rout]

/-- No point of the first arc is the second inner endpoint. -/
theorem pczArcA_ne_a₂ {t₁ t₂ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ1 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout) (ht : 0 < t₁ + t₂) :
    pczArcA S t₁ y ≠ (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  intro h
  rw [pczArcA_apply, pca₂_smul S t₂] at h
  have key := mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) h
  have hcoef := Complex.ofReal_inj.mp key
  have hA := (pczArcA_coef_bounds S (t₁ := t₁) hy hτ1).1
  linarith

/-- No point of the third arc is the first inner endpoint. -/
theorem pczArcC_ne_a₁ {t₁ t₂ y : ℝ} (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hτ2 : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂) (ht : 0 < t₁ + t₂) :
    pczArcC S t₂ y ≠ (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
  intro h
  rw [pczArcC_apply, pca₁_smul S t₁] at h
  have key := mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) h
  have hcoef := Complex.ofReal_inj.mp key
  have hC := (pczArcC_coef_bounds S (t₂ := t₂) hy hτ2).2
  linarith

/-- Dividing out a common denominator `π/2`. -/
theorem pcdiv_slash {a b : ℝ} (h : a / (Real.pi / 2) = b / (Real.pi / 2)) : a = b := by
  have h2 : a / (Real.pi / 2) * (Real.pi / 2) = b / (Real.pi / 2) * (Real.pi / 2) := by rw [h]
  rwa [div_mul_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0),
    div_mul_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0)] at h2

theorem pcy0_lt_one {σ : ℝ} (h : σ < Real.pi / 2) : σ / (Real.pi / 2) < 1 := by
  rw [div_lt_one (by positivity : (0:ℝ) < Real.pi / 2)]; exact h

theorem pcy1_pos {σ : ℝ} (h : Real.pi / 2 < σ) :
    0 < (σ - Real.pi / 2) / (Real.pi / 2) :=
  div_pos (by linarith) (by positivity)

theorem pcy2_pos {σ : ℝ} (h : Real.pi < σ) : 0 < (σ - Real.pi) / (Real.pi / 2) :=
  div_pos (by linarith) (by positivity)

theorem pcy3_lt_one {σ : ℝ} (h : σ < 2 * Real.pi) :
    (σ - 3 * Real.pi / 2) / (Real.pi / 2) < 1 := by
  rw [div_lt_one (by positivity : (0:ℝ) < Real.pi / 2)]; linarith

theorem pcy3_pos {σ : ℝ} (h : 3 * Real.pi / 2 < σ) :
    0 < (σ - 3 * Real.pi / 2) / (Real.pi / 2) :=
  div_pos (by linarith) (by positivity)

/-- The auxiliary curve is injective on one period, in the strict parameter ordering. -/
theorem pczBarUn_ne_of_lt (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ∈ Set.Ico 0 (2 * Real.pi)) (hσ₂ : σ₂ ∈ Set.Ico 0 (2 * Real.pi))
    (hlt : σ₁ < σ₂) :
    pczBarUn S t₁ t₂ θ₁ θ₂ σ₁ ≠ pczBarUn S t₁ t₂ θ₁ θ₂ σ₂ := by
  have hτ1lt : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ < 1 :=
    (pcbase_add_t₁_mem S hball hθ₁ ht₁).2
  have hτ2gt : -1 < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ :=
    (pcbase_sub_t₂_mem S hball hθ₂).1
  have hτ2lt : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ < 1 :=
    (pcbase_sub_t₂_mem S hball hθ₂).2
  have hτ1R : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout := by
    linarith [hτ1lt, pcone_lt_Rout]
  have hτ2R : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ := by
    linarith [hτ2gt, pcone_lt_Rout]
  have hτ2R' : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ < pcRout := by
    linarith [hτ2lt, pcone_lt_Rout]
  have hτ1Rne : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≠ pcRout := by
    intro hc; linarith [hτ1lt, pcone_lt_Rout, hc]
  have hneA : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout ≠ 0 := by
    intro hc; linarith [hτ1R, hτ1lt, pcone_lt_Rout, hc]
  have hneC : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂ ≠ 0 := by
    intro hc; linarith [hτ2gt, pcone_lt_Rout, hc]
  have hneθ := pctheta_ne_of_cuts S ht₁ ht₂ hθ₁ hθ₂
  have hsum : 0 < t₁ + t₂ := by linarith
  have hy3mem : ∀ {σ : ℝ}, σ ∈ Set.Ico (0:ℝ) (2 * Real.pi) →
      3 * Real.pi / 2 < σ → (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0:ℝ) 1 :=
    fun hσ h => pcy3_mem (le_of_lt h) hσ.2.le
  by_cases h₁0 : σ₁ ≤ Real.pi / 2
  · have hy₁ := pcy0_mem hσ₁.1 h₁0
    by_cases h₂0 : σ₂ ≤ Real.pi / 2
    · -- Q0 vs Q0
      intro h
      rw [pczBarUn_q0 h₁0] at h
      rw [pczBarUn_q0 h₂0] at h
      exact absurd (pcdiv_slash (pczArcA_inj S t₁ hneA h)) (ne_of_lt hlt)
    · by_cases h₂1 : σ₂ ≤ Real.pi
      · -- Q0 vs Q1
        intro h
        rw [pczBarUn_q0 h₁0] at h
        rw [pczBarUn_q1 h₂0 h₂1] at h
        have hy₂' := pcy1_mem (le_of_lt (not_le.mp h₂0)) h₂1
        have hy₂pos := pcy1_pos (not_le.mp h₂0)
        by_cases hy₂lt : (σ₂ - Real.pi / 2) / (Real.pi / 2) < 1
        · have hB := pczArcB_mem_V_of_Ioo S hneθ ⟨hy₂pos, hy₂lt⟩
          exact pczArcA_notMem_V S hball hout₁ hθ₁ hseg₁ hy₁ hτ1R (by rw [h]; exact hB)
        · have hy₂eq : (σ₂ - Real.pi / 2) / (Real.pi / 2) = 1 :=
            le_antisymm hy₂'.2 (le_of_not_gt hy₂lt)
          have hB : pczArcB S θ₁ θ₂ ((σ₂ - Real.pi / 2) / (Real.pi / 2)) =
              (Work.Smooth.SphereJordan.pcbase S : ℂ) -
                (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
            rw [hy₂eq]; exact pczArcB_eq_a₂' S le_rfl hθ₂
          exact pczArcA_ne_a₂ S hy₁ hτ1R hsum (by rw [h, hB])
      · by_cases h₂2 : σ₂ ≤ 3 * Real.pi / 2
        · -- Q0 vs Q2
          intro h
          rw [pczBarUn_q0 h₁0] at h
          rw [pczBarUn_q2 h₂0 h₂1 h₂2] at h
          exact pczArcA_ne_zArcC S hy₁ (pcy2_mem (le_of_lt (not_le.mp h₂1)) h₂2)
            hτ1R hτ2R hsum h
        · -- Q0 vs Q3
          intro h
          rw [pczBarUn_q0 h₁0] at h
          rw [pczBarUn_q3 h₂0 h₂1 h₂2] at h
          exact pczArcA_ne_zArcD S hy₁ (hy3mem hσ₂ (not_le.mp h₂2)) hτ1R ht₁ hτ1Rne
            (pcy3_lt_one hσ₂.2) h
  · have h₁a : Real.pi / 2 < σ₁ := not_le.mp h₁0
    by_cases h₁1 : σ₁ ≤ Real.pi
    · have hy₁ := pcy1_mem (le_of_lt h₁a) h₁1
      have h₂0 : ¬ σ₂ ≤ Real.pi / 2 := by linarith
      by_cases h₂1 : σ₂ ≤ Real.pi
      · -- Q1 vs Q1
        intro h
        rw [pczBarUn_q1 h₁0 h₁1] at h
        rw [pczBarUn_q1 h₂0 h₂1] at h
        have hy₂ := pcy1_mem (le_of_lt (not_le.mp h₂0)) h₂1
        have h4 := pczArcB_inj S θ₁ θ₂ hneθ hy₁ hy₂ h
        exact absurd (by linarith [pcdiv_slash h4]) (ne_of_lt hlt)
      · by_cases h₂2 : σ₂ ≤ 3 * Real.pi / 2
        · -- Q1 vs Q2
          intro h
          rw [pczBarUn_q1 h₁0 h₁1] at h
          rw [pczBarUn_q2 h₂0 h₂1 h₂2] at h
          have hy₂ := pcy2_mem (le_of_lt (not_le.mp h₂1)) h₂2
          have hy₁pos := pcy1_pos h₁a
          by_cases hy₁lt : (σ₁ - Real.pi / 2) / (Real.pi / 2) < 1
          · have hB := pczArcB_mem_V_of_Ioo S hneθ ⟨hy₁pos, hy₁lt⟩
            exact pczArcC_notMem_V S hball hout₂ hθ₂ hseg₂ hy₂ hτ2R (by rw [← h]; exact hB)
          · have hy₁eq : (σ₁ - Real.pi / 2) / (Real.pi / 2) = 1 :=
              le_antisymm hy₁.2 (le_of_not_gt hy₁lt)
            have hB : pczArcB S θ₁ θ₂ ((σ₁ - Real.pi / 2) / (Real.pi / 2)) =
                (Work.Smooth.SphereJordan.pcbase S : ℂ) -
                  (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
              rw [hy₁eq]; exact pczArcB_eq_a₂' S le_rfl hθ₂
            have hz : pczArcC S t₂ ((σ₂ - Real.pi) / (Real.pi / 2)) = pczArcC S t₂ 0 := by
              rw [pczArcC_zero, ← h, hB]
            have hz0 : (σ₂ - Real.pi) / (Real.pi / 2) = 0 := pczArcC_inj S t₂ hneC hz
            rcases div_eq_zero_iff.mp hz0 with h5 | h5
            · exact h₂1 (by linarith)
            · exact absurd h5 (by positivity)
        · -- Q1 vs Q3
          intro h
          rw [pczBarUn_q1 h₁0 h₁1] at h
          rw [pczBarUn_q3 h₂0 h₂1 h₂2] at h
          exact pczArcB_ne_zArcD S hball hy₁ (hy3mem hσ₂ (not_le.mp h₂2)) h
    · have h₁b : Real.pi < σ₁ := not_le.mp h₁1
      by_cases h₁2 : σ₁ ≤ 3 * Real.pi / 2
      · have hy₁ := pcy2_mem (le_of_lt h₁b) h₁2
        have h₂0 : ¬ σ₂ ≤ Real.pi / 2 := by linarith
        have h₂1 : ¬ σ₂ ≤ Real.pi := by linarith
        by_cases h₂2 : σ₂ ≤ 3 * Real.pi / 2
        · -- Q2 vs Q2
          intro h
          rw [pczBarUn_q2 h₁0 h₁1 h₁2] at h
          rw [pczBarUn_q2 h₂0 h₂1 h₂2] at h
          have hy₂ := pcy2_mem (le_of_lt (not_le.mp h₂1)) h₂2
          have h4 := pczArcC_inj S t₂ hneC h
          exact absurd (by linarith [pcdiv_slash h4]) (ne_of_lt hlt)
        · -- Q2 vs Q3
          intro h
          rw [pczBarUn_q2 h₁0 h₁1 h₁2] at h
          rw [pczBarUn_q3 h₂0 h₂1 h₂2] at h
          exact pczArcC_ne_zArcD S hy₁ (hy3mem hσ₂ (not_le.mp h₂2)) hτ2R hτ2R' hneC
            (pcy3_pos (not_le.mp h₂2)) h
      · -- Q3 vs Q3
        have h₁c : 3 * Real.pi / 2 < σ₁ := not_le.mp h₁2
        have h₂0 : ¬ σ₂ ≤ Real.pi / 2 := by linarith
        have h₂1 : ¬ σ₂ ≤ Real.pi := by linarith
        have h₂2 : ¬ σ₂ ≤ 3 * Real.pi / 2 := by linarith
        intro h
        rw [pczBarUn_q3 h₁0 h₁1 h₁2] at h
        rw [pczBarUn_q3 h₂0 h₂1 h₂2] at h
        have h4 := pczArcD_inj S (hy3mem hσ₁ h₁c) (hy3mem hσ₂ (not_le.mp h₂2)) h
        exact absurd (by linarith [pcdiv_slash h4]) (ne_of_lt hlt)

/-- The auxiliary curve is injective on one period. -/
theorem pczBarUn_injOn (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V) :
    Set.InjOn (pczBarUn S t₁ t₂ θ₁ θ₂) (Set.Ico 0 (2 * Real.pi)) := by
  intro σ₁ hσ₁ σ₂ hσ₂ heq
  rcases lt_trichotomy σ₁ σ₂ with h | h | h
  · exact absurd heq (pczBarUn_ne_of_lt S hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂ hts₂
      hseg₁ hseg₂ hσ₁ hσ₂ h)
  · exact h
  · exact absurd heq.symm (pczBarUn_ne_of_lt S hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂ hts₂
      hseg₁ hseg₂ hσ₂ hσ₁ h)

end Injectivity

/-- The auxiliary curve is a simple closed curve. -/
theorem pczCurve_isSimple (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V) :
    (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).IsSimple := by
  have hinj := pczBarUn_injOn S hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂ hts₂ hseg₁ hseg₂
  intro σ₁ hσ₁ σ₂ hσ₂ heq
  have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt σ₁) =
      pczBarUn S t₁ t₂ θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt σ₂) := heq
  rw [pcperPt_self' hσ₁, pcperPt_self' hσ₂] at h2
  exact hinj hσ₁ hσ₂ h2

/-- The auxiliary curve never meets the cut pcannulus. -/
theorem pcZbar_notMem_annulusCut' (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) *
        Work.Smooth.SphereJordan.pccutDir S ∈ Metric.ball (0 : ℂ) 1 \ S.V) :
    ∀ τ : ℝ, pcZbar S t₁ t₂ θ₁ θ₂ τ ∉
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := by
  have hτ1lt : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ < 1 :=
    (pcbase_add_t₁_mem S hball hθ₁ ht₁).2
  have hτ2gt : -1 < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ :=
    (pcbase_sub_t₂_mem S hball hθ₂).1
  have hτ1R : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ ≤ pcRout := by
    linarith [hτ1lt, pcone_lt_Rout]
  have hτ2R : -pcRout ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ := by
    linarith [hτ2gt, pcone_lt_Rout]
  have hs₁ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ = 1 := pcbase_add_s₁ S hout₁
  have hs₂ : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ = -1 := pcbase_sub_s₂ S hout₂
  have hneθ := pctheta_ne_of_cuts S ht₁ ht₂ hθ₁ hθ₂
  intro τ
  show pczBarUn S t₁ t₂ θ₁ θ₂ (Work.Smooth.SphereJordan.pcperPt τ) ∉
    Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂
  have hσ := Work.SphereJordan.pcperPt_mem τ
  by_cases h0 : Work.Smooth.SphereJordan.pcperPt τ ≤ Real.pi / 2
  · -- first arc
    rw [pczBarUn_q0 h0]
    intro hmem
    have hy := pcy0_mem hσ.1 h0
    have hcoef := (pczArcA_coef_bounds S (t₁ := t₁) hy hτ1R)
    by_cases hα : pcRout + (Work.Smooth.SphereJordan.pcperPt τ / (Real.pi / 2)) *
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) ≤ 1
    · have hcut : pczArcA S t₁ (Work.Smooth.SphereJordan.pcperPt τ / (Real.pi / 2)) ∈
          Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ := by
        refine ⟨pcRout + (Work.Smooth.SphereJordan.pcperPt τ / (Real.pi / 2)) *
          (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) -
            ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖, ⟨?_, ?_⟩, ?_⟩
        · linarith [hcoef.1]
        · linarith [hα, hs₁]
        · rw [pczArcA_apply]
          exact pccoeff_smul_eq S _
      exact hmem.2 (Or.inl hcut)
    · rw [not_le] at hα
      have hnorm : ‖pczArcA S t₁ (Work.Smooth.SphereJordan.pcperPt τ / (Real.pi / 2))‖ =
          pcRout + (Work.Smooth.SphereJordan.pcperPt τ / (Real.pi / 2)) *
            (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) := by
        rw [pczArcA_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hcoef.1])]
      have hb := hmem.1.1
      rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hb
      linarith
  · by_cases h1 : Work.Smooth.SphereJordan.pcperPt τ ≤ Real.pi
    · -- second arc
      rw [pczBarUn_q1 h0 h1]
      intro hmem
      have hB := pczArcB_mem S θ₁ θ₂ hneθ
        ((Work.Smooth.SphereJordan.pcperPt τ - Real.pi / 2) / (Real.pi / 2))
      rw [Set.mem_union] at hB
      rcases hB with hSV | hB
      · exact hmem.1.2 hSV
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
        rcases hB with hB | hB
        · exact hmem.2 (Or.inl ⟨t₁, ⟨le_rfl, hts₁.le⟩, by rw [hB, hθ₁]⟩)
        · exact hmem.2 (Or.inr ⟨t₂, ⟨le_rfl, hts₂.le⟩, by rw [hB, hθ₂]⟩)
    · by_cases h2 : Work.Smooth.SphereJordan.pcperPt τ ≤ 3 * Real.pi / 2
      · -- third arc
        rw [pczBarUn_q2 h0 h1 h2]
        intro hmem
        have hy := pcy2_mem (le_of_lt (not_le.mp h1)) h2
        have hcoef := (pczArcC_coef_bounds S (t₂ := t₂) hy hτ2R)
        by_cases hα : -1 ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
            (Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2) *
              (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)
        · have hcut : pczArcC S t₂ ((Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2)) ∈
              Work.Smooth.SphereJordan.pccut₂ S t₂ s₂ := by
            refine ⟨‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ -
              (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
                (Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2) *
                  (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)), ⟨?_, ?_⟩, ?_⟩
            · linarith [hcoef.2]
            · linarith [hα, hs₂]
            · rw [pczArcC_apply]
              exact pccoeff_smul_eq_sub S _
          exact hmem.2 (Or.inr hcut)
        · rw [not_le] at hα
          have hnorm : ‖pczArcC S t₂ ((Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2))‖ =
              |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
                (Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2) *
                  (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| := by
            rw [pczArcC_apply, norm_mul, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one,
              Complex.norm_real, Real.norm_eq_abs]
          have habs : |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
              (Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2) *
                (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)| =
              -(‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
                (Work.Smooth.SphereJordan.pcperPt τ - Real.pi) / (Real.pi / 2) *
                  (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂)) :=
            abs_of_neg (by linarith)
          have hb := hmem.1.1
          rw [Metric.mem_closedBall, dist_zero_right, hnorm, habs] at hb
          linarith
      · -- fourth arc
        rw [pczBarUn_q3 h0 h1 h2]
        intro hmem
        have hb := hmem.1.1
        rw [Metric.mem_closedBall, dist_zero_right, pcnorm_zArcD'] at hb
        linarith [pcone_lt_Rout]

theorem pcZbar_notMem_annulusCut (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ)
    (θ₁ θ₂ : ℝ) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hout₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S)
    (hout₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (τ : ℝ) : pcZbar S t₁ t₂ θ₁ θ₂ τ ∉ Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂ := pcZbar_notMem_annulusCut' S hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂ hts₂ hseg₁ hseg₂ τ

section WindQ

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
variable {t₁ t₂ θ₁ θ₂ : ℝ}

/-- The auxiliary curve, divided by the unit direction `pccutDir S`. -/
theorem pcZbar_div_self (σ : ℝ) : pcZbar S t₁ t₂ θ₁ θ₂ σ =
    Work.Smooth.SphereJordan.pccutDir S *
      (pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S) := by
  rw [mul_div_cancel₀]
  exact Work.Smooth.SphereJordan.pccutDir_ne_zero S

/-- The first quarter in the frame of `pccutDir S`. -/
theorem pcZbar_q0 {σ : ℝ} (hσ : σ ∈ Set.Icc (0:ℝ) (Real.pi / 2)) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S =
      (((pcRout + (σ / (Real.pi / 2)) *
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) := by
  have h2π : σ < 2 * Real.pi := by linarith [hσ.2, Real.pi_pos]
  rw [pcZbar, pcperPt_self' ⟨hσ.1, h2π⟩, pczBarUn_q0 hσ.2, pczArcA_apply]
  exact mul_div_cancel_right₀ _ (Work.Smooth.SphereJordan.pccutDir_ne_zero S)

/-- The second quarter in the frame of `pccutDir S`. -/
theorem pcZbar_q1 (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (Real.pi / 2) Real.pi) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S =
      pczArcB S θ₁ θ₂ ((σ - Real.pi / 2) / (Real.pi / 2)) /
        Work.Smooth.SphereJordan.pccutDir S := by
  have h2π : σ < 2 * Real.pi := by linarith [hσ.2, Real.pi_pos]
  rcases eq_or_lt_of_le hσ.1 with h | h
  · subst h
    rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      pczBarUn_junction1 S t₁ t₂ θ₁ θ₂ hθ₁]
  · rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], h2π⟩,
      pczBarUn_q1 (not_le.mpr h) hσ.2]

/-- The third quarter in the frame of `pccutDir S`. -/
theorem pcZbar_q2 (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    {σ : ℝ} (hσ : σ ∈ Set.Icc Real.pi (3 * Real.pi / 2)) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        (σ - Real.pi) / (Real.pi / 2) *
          (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) := by
  have h2π : σ < 2 * Real.pi := by linarith [hσ.2, Real.pi_pos]
  rcases eq_or_lt_of_le hσ.1 with h | h
  · subst h
    rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      pczBarUn_junction2 S t₁ t₂ θ₁ θ₂ hθ₂, pczArcC_apply]
    exact mul_div_cancel_right₀ _ (Work.Smooth.SphereJordan.pccutDir_ne_zero S)
  · rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], h2π⟩, pczBarUn_q2 (by linarith [Real.pi_pos])
      (not_le.mpr h) hσ.2, pczArcC_apply]
    exact mul_div_cancel_right₀ _ (Work.Smooth.SphereJordan.pccutDir_ne_zero S)

/-- The fourth quarter in the frame of `pccutDir S`. -/
theorem pcZbar_q3 {σ : ℝ} (hσ : σ ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S =
      ((pcRout : ℝ) : ℂ) * Complex.exp
        (((Real.pi * (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) * Complex.I) := by
  rcases eq_or_lt_of_le hσ.1 with h | h
  · subst h
    rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      pczBarUn_junction3 S t₁ t₂ θ₁ θ₂]
    rw [show (3 * Real.pi / 2 - 3 * Real.pi / 2) / (Real.pi / 2) = 0 from by norm_num,
      show (1 - 0 : ℝ) = 1 from by ring, show (Real.pi * 1 : ℝ) = Real.pi from by ring,
      pczArcD_zero, Complex.exp_pi_mul_I]
    rw [div_eq_iff (Work.Smooth.SphereJordan.pccutDir_ne_zero S)]
    ring
  · rcases eq_or_lt_of_le hσ.2 with h2 | h2
    · subst h2
      rw [pcZbar, pcperPt_two_pi, pczBarUn_zero,
        show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 from by
          rw [div_eq_one_iff_eq (by positivity)]; ring,
        show (1 - 1 : ℝ) = 0 from by ring, show (Real.pi * 0 : ℝ) = 0 from by ring,
        show (((0:ℝ):ℂ) * Complex.I) = 0 from by simp, Complex.exp_zero, mul_one]
      exact mul_div_cancel_right₀ _ (Work.Smooth.SphereJordan.pccutDir_ne_zero S)
    · rw [pcZbar, pcperPt_self' ⟨by linarith [Real.pi_pos], h2⟩,
        pczBarUn_q3 (not_le.mpr (by linarith [h, Real.pi_pos] : Real.pi / 2 < σ))
          (not_le.mpr (by linarith [h, Real.pi_pos] : Real.pi < σ)) (not_le.mpr h), pczArcD_apply]
      rw [show ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
          Complex.exp (((Real.pi * (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
            Complex.I) = (((pcRout : ℝ) : ℂ) * Complex.exp
              (((Real.pi * (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
                Complex.I)) * Work.Smooth.SphereJordan.pccutDir S from by ring,
        mul_div_cancel_right₀ _ (Work.Smooth.SphereJordan.pccutDir_ne_zero S)]

end WindQ

/-- The explicit first-quarter path in the `pccutDir S` frame. -/
noncomputable def pcpA (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => (((pcRout + (t : ℝ) *
    (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I, by fun_prop⟩

/-- The explicit second-quarter path. -/
noncomputable def pcpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (θ₁ θ₂ : ℝ) :
    C(unitInterval, ℂ) :=
  ⟨fun t => pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S - Complex.I,
    ((pccontinuous_zArcB S θ₁ θ₂).comp continuous_subtype_val).div_const _ |>.sub continuous_const⟩

/-- The explicit third-quarter path. -/
noncomputable def pcpC (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
    (t : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) - Complex.I,
      by fun_prop⟩

/-- The explicit fourth-quarter path. -/
noncomputable def pcpD (S : Work.Smooth.Jordan.PlaneSchoenflies γ) : C(unitInterval, ℂ) :=
  ⟨fun t => ((pcRout : ℝ) : ℂ) *
    Complex.exp (((Real.pi * (1 - (t : ℝ)) : ℝ) : ℂ) * Complex.I) - Complex.I, by fun_prop⟩

section WindInc

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
variable {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}

/-- The `pccutDir S`-frame path of the first quarter is `pcpA`. -/
theorem pcZbar_path_q0
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    (⟨fun t : unitInterval => pcZbar S t₁ t₂ θ₁ θ₂ (0 + (t : ℝ) * (Real.pi / 2 - 0)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S,
      ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1.comp (by fun_prop)).sub
        continuous_const⟩ : C(unitInterval, ℂ)) =
    ContinuousMap.const unitInterval (Work.Smooth.SphereJordan.pccutDir S) * pcpA S t₁ := by
  ext t
  show (pcZbar S t₁ t₂ θ₁ θ₂ (0 + (t : ℝ) * (Real.pi / 2 - 0)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S) =
    Work.Smooth.SphereJordan.pccutDir S *
      ((((pcRout + (t : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) -
        Complex.I)
  rw [pcZbar_div_self S, show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = (t : ℝ) * (Real.pi / 2) from by ring]
  rw [pcZbar_q0 S (show (t : ℝ) * (Real.pi / 2) ∈ Set.Icc (0:ℝ) (Real.pi / 2) from
      ⟨mul_nonneg t.2.1 (by positivity), by nlinarith [t.2.2, Real.pi_pos]⟩),
    show (t : ℝ) * (Real.pi / 2) / (Real.pi / 2) = (t : ℝ) from by
      rw [mul_div_assoc, div_self (by positivity), mul_one]]
  ring

/-- The `pccutDir S`-frame path of the second quarter is `pcpB`. -/
theorem pcZbar_path_q1
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    (⟨fun t : unitInterval => pcZbar S t₁ t₂ θ₁ θ₂
        (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S,
      ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1.comp (by fun_prop)).sub
        continuous_const⟩ : C(unitInterval, ℂ)) =
    ContinuousMap.const unitInterval (Work.Smooth.SphereJordan.pccutDir S) * pcpB S θ₁ θ₂ := by
  ext t
  show (pcZbar S t₁ t₂ θ₁ θ₂ (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S) =
    Work.Smooth.SphereJordan.pccutDir S *
      (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S - Complex.I)
  rw [pcZbar_div_self S, pcZbar_q1 S hθ₁ (show Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) ∈
      Set.Icc (Real.pi / 2) Real.pi from
      ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
    show (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) - Real.pi / 2) / (Real.pi / 2) =
      (t : ℝ) from by
        rw [add_sub_cancel_left, show (Real.pi - Real.pi / 2) = Real.pi / 2 from by ring,
          mul_div_assoc, div_self (by positivity), mul_one]]
  ring

/-- The `pccutDir S`-frame path of the third quarter is `pcpC`. -/
theorem pcZbar_path_q2
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    (⟨fun t : unitInterval => pcZbar S t₁ t₂ θ₁ θ₂
        (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S,
      ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1.comp (by fun_prop)).sub
        continuous_const⟩ : C(unitInterval, ℂ)) =
    ContinuousMap.const unitInterval (Work.Smooth.SphereJordan.pccutDir S) * pcpC S t₂ := by
  ext t
  show (pcZbar S t₁ t₂ θ₁ θ₂ (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S) =
    Work.Smooth.SphereJordan.pccutDir S *
      ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        (t : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) - Complex.I)
  rw [pcZbar_div_self S, pcZbar_q2 S hθ₂ (show Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) ∈
      Set.Icc Real.pi (3 * Real.pi / 2) from
      ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
    show (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) - Real.pi) / (Real.pi / 2) =
      (t : ℝ) from by
        rw [add_sub_cancel_left, show (3 * Real.pi / 2 - Real.pi) = Real.pi / 2 from by ring,
          mul_div_assoc, div_self (by positivity), mul_one]]
  ring

/-- The `pccutDir S`-frame path of the fourth quarter is `pcpD`. -/
theorem pcZbar_path_q3
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    (⟨fun t : unitInterval => pcZbar S t₁ t₂ θ₁ θ₂
        (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S,
      ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1.comp (by fun_prop)).sub
        continuous_const⟩ : C(unitInterval, ℂ)) =
    ContinuousMap.const unitInterval (Work.Smooth.SphereJordan.pccutDir S) * pcpD S := by
  ext t
  show (pcZbar S t₁ t₂ θ₁ θ₂ (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2)) -
      Complex.I * Work.Smooth.SphereJordan.pccutDir S) =
    Work.Smooth.SphereJordan.pccutDir S *
      (((pcRout : ℝ) : ℂ) * Complex.exp (((Real.pi * (1 - (t : ℝ)) : ℝ) : ℂ) * Complex.I) -
        Complex.I)
  rw [pcZbar_div_self S, pcZbar_q3 S (show 3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) ∈
      Set.Icc (3 * Real.pi / 2) (2 * Real.pi) from
      ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
    show (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) - 3 * Real.pi / 2) /
      (Real.pi / 2) = (t : ℝ) from by
        rw [add_sub_cancel_left, show (2 * Real.pi - 3 * Real.pi / 2) = Real.pi / 2 from by ring,
          mul_div_assoc, div_self (by positivity), mul_one]]
  ring

end WindInc

section WindInc2

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
variable {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}

/-! ## Non-vanishing and slit-plane membership of the four explicit paths -/

theorem pcpA_ne (t : unitInterval) : pcpA S t₁ t ≠ 0 := by
  intro hcon
  have h1 : (pcpA S t₁ t).im = 0 := by rw [hcon]; simp
  have h2 : ((((pcRout + (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I).im = 0 := h1
  rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at h2
  norm_num at h2

theorem pcpA_slit (t : unitInterval) : pcpA S t₁ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  intro hcon
  have h1 : (pcpA S t₁ t).im = 0 := hcon
  have h2 : ((((pcRout + (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I).im = 0 := h1
  rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at h2
  norm_num at h2

theorem pcpB_ne (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ₁ θ₂ : ℝ) (t : unitInterval) :
    pcpB S θ₁ θ₂ t ≠ 0 := by
  intro hcon
  have h1 : (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S - Complex.I).im = 0 :=
    (show (pcpB S θ₁ θ₂ t).im = 0 from by rw [hcon]; simp)
  rw [Complex.sub_im, Complex.I_im] at h1
  have hw : (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).im = 1 := by linarith
  have hlt : ‖pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S‖ < 1 := by
    rw [norm_div, Work.Smooth.SphereJordan.pcnorm_cutDir, div_one]
    exact pcnorm_zArcB_lt_one S θ₁ θ₂ hball (t : ℝ)
  have hsq : ‖pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S‖^2 =
      (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).re^2 +
        (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hw] at hsq
  nlinarith [hsq, hlt, norm_nonneg (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S),
    sq_nonneg (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).re]

theorem pcpB_slit (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (θ₁ θ₂ : ℝ) (t : unitInterval) :
    pcpB S θ₁ θ₂ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  intro hcon
  have h1 : (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S - Complex.I).im = 0 := hcon
  rw [Complex.sub_im, Complex.I_im] at h1
  have hw : (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).im = 1 := by linarith
  have hlt : ‖pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S‖ < 1 := by
    rw [norm_div, Work.Smooth.SphereJordan.pcnorm_cutDir, div_one]
    exact pcnorm_zArcB_lt_one S θ₁ θ₂ hball (t : ℝ)
  have hsq : ‖pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S‖^2 =
      (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).re^2 +
        (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hw] at hsq
  nlinarith [hsq, hlt, norm_nonneg (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S),
    sq_nonneg (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S).re]

theorem pcpC_ne (t : unitInterval) : pcpC S t₂ t ≠ 0 := by
  intro hcon
  have h1 : (pcpC S t₂ t).im = 0 := by rw [hcon]; simp
  have h2 : ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) -
        Complex.I).im = 0 := h1
  rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at h2
  norm_num at h2

theorem pcpC_slit (t : unitInterval) : pcpC S t₂ t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  intro hcon
  have h1 : (pcpC S t₂ t).im = 0 := hcon
  have h2 : ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) -
        Complex.I).im = 0 := h1
  rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at h2
  norm_num at h2

theorem pcpD_ne (t : unitInterval) : pcpD S t ≠ 0 := by
  intro hcon
  have h0 : (((pcRout : ℝ) : ℂ) * Complex.exp (((Real.pi * (1 - (t : ℝ)) : ℝ) : ℂ) * Complex.I) -
      Complex.I) = 0 := hcon
  have h1 : (((pcRout : ℝ) : ℂ) * Complex.exp (((Real.pi * (1 - (t : ℝ)) : ℝ) : ℂ) * Complex.I)) =
      Complex.I := sub_eq_zero.mp h0
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pcRout_pos,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_I] at h2
  linarith [pcone_lt_Rout]

end WindInc2

section WindLog

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
variable {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}

/-- `log (-x) = log x - πi` for `x` in the upper half plane. -/
theorem pclog_neg_of_im_pos' {x : ℂ} (hx : 0 < x.im) :
    Complex.log (-x) = Complex.log x - (Real.pi : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp only [Complex.sub_re, Complex.log_re, norm_neg, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  · simp only [Complex.sub_im, Complex.log_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_mul]
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hx]

/-- The logarithm of `-pcRout - i` in terms of `pcRout + i`. -/
theorem pclog_neg_Rout' :
    Complex.log (((-pcRout : ℝ) : ℂ) - Complex.I) =
      Complex.log (((pcRout : ℝ) : ℂ) + Complex.I) - (Real.pi : ℂ) * Complex.I := by
  rw [show ((-pcRout : ℝ) : ℂ) - Complex.I = -(((pcRout : ℝ) : ℂ) + Complex.I) from by
    push_cast; ring]
  exact pclog_neg_of_im_pos' (by
    rw [Complex.add_im, Complex.ofReal_im, Complex.I_im]; norm_num)

/-- Splitting the fourth-quarter logarithm. -/
theorem pclog_half_sub' :
    Complex.log (1 - Complex.I / ((pcRout : ℝ) : ℂ)) -
        Complex.log (1 + Complex.I / ((pcRout : ℝ) : ℂ)) =
      Complex.log (((pcRout : ℝ) : ℂ) - Complex.I) -
        Complex.log (((pcRout : ℝ) : ℂ) + Complex.I) := by
  have hR : (0 : ℝ) < 1 / pcRout := by
    rw [one_div]; exact inv_pos.mpr pcRout_pos
  have hRne : (((pcRout : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt pcRout_pos)
  have h1 : (1 : ℂ) - Complex.I / ((pcRout : ℝ) : ℂ) =
      (((pcRout : ℝ) : ℂ) - Complex.I) * (((1 / pcRout : ℝ)) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp
  have h2 : (1 : ℂ) + Complex.I / ((pcRout : ℝ) : ℂ) =
      (((pcRout : ℝ) : ℂ) + Complex.I) * (((1 / pcRout : ℝ)) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp
  have hne1 : (((pcRout : ℝ) : ℂ) - Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at this; norm_num at this
  have hne2 : (((pcRout : ℝ) : ℂ) + Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h
    rw [Complex.add_im, Complex.ofReal_im, Complex.I_im] at this; norm_num at this
  rw [h1, h2, Complex.log_mul_ofReal _ hR _ hne1, Complex.log_mul_ofReal _ hR _ hne2]
  ring

end WindLog

section WindMain

variable (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
variable {t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ}

/-- The point `i·pccutDir S` is never on the auxiliary curve. -/
theorem pcZbar_ne_I (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (σ : ℝ) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ ≠ Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
  intro h
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have h1 : pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S = Complex.I := by
    rw [h, mul_div_cancel_right₀ _ hu]
  rw [pcZbar] at h1
  set τ := Work.Smooth.SphereJordan.pcperPt σ with hτdef
  rcases lt_or_ge (Real.pi / 2) τ with hc | hc
  · rcases lt_or_ge Real.pi τ with hc' | hc'
    · rcases lt_or_ge (3 * Real.pi / 2) τ with hc'' | hc''
      · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
            ((pcRout : ℝ) : ℂ) * Complex.exp
              (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
                Complex.I) := by
          rw [pczBarUn_q3 (not_le.mpr hc) (not_le.mpr hc') (not_le.mpr hc''), pczArcD_apply,
            show ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
                Complex.exp (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) :
                  ℂ) * Complex.I) = (((pcRout : ℝ) : ℂ) * Complex.exp
                    (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
                      Complex.I)) * Work.Smooth.SphereJordan.pccutDir S from by ring,
            mul_div_cancel_right₀ _ hu]
        rw [h2] at h1
        have h3 := congrArg norm h1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pcRout_pos,
          Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_I] at h3
        linarith [pcone_lt_Rout]
      · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
            (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
              (τ - Real.pi) / (Real.pi / 2) *
                (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) := by
          rw [pczBarUn_q2 (not_le.mpr hc) (not_le.mpr hc') hc'', pczArcC_apply,
            mul_div_cancel_right₀ _ hu]
        rw [h2] at h1
        have h3 := congrArg Complex.im h1
        rw [Complex.ofReal_im, Complex.I_im] at h3
        norm_num at h3
    · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
          pczArcB S θ₁ θ₂ ((τ - Real.pi / 2) / (Real.pi / 2)) /
            Work.Smooth.SphereJordan.pccutDir S := by
        rw [pczBarUn_q1 (not_le.mpr hc) hc']
      rw [h2] at h1
      have h3 := congrArg norm h1
      rw [norm_div, Complex.norm_I, Work.Smooth.SphereJordan.pcnorm_cutDir, div_one] at h3
      have h4 := pcnorm_zArcB_lt_one S θ₁ θ₂ hball ((τ - Real.pi / 2) / (Real.pi / 2))
      linarith
  · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
        (((pcRout + τ / (Real.pi / 2) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) :
          ℝ)) : ℂ) := by
      rw [pczBarUn_q0 hc, pczArcA_apply, mul_div_cancel_right₀ _ hu]
    rw [h2] at h1
    have h3 := congrArg Complex.im h1
    rw [Complex.ofReal_im, Complex.I_im] at h3
    norm_num at h3

/-- The argument increment of the first quarter of `pcZbar` about `i·pccutDir S`. -/
theorem pcincOn_Zbar_q0
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.SphereJordan.incOn (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) 0 (Real.pi / 2) =
      Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ)) : ℂ) - Complex.I) -
        Complex.log ((((pcRout : ℝ)) : ℂ) - Complex.I) := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have hne : ∀ t : unitInterval, ((((pcRout + (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I) ≠ 0 := by
    intro t hcon
    have := congrArg Complex.im hcon
    rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at this
    norm_num at this
  have hcont : Continuous (fun t : unitInterval =>
      Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log
        ((((pcRout + (t : ℝ) *
          (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I)) := by
    refine continuous_const.add ?_
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.clog ?_ ?_
    · fun_prop
    · rw [Complex.mem_slitPlane_iff]; right
      rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im]; norm_num
  have hLift : ∀ t : unitInterval, Complex.exp (Complex.log
      (Work.Smooth.SphereJordan.pccutDir S) + Complex.log ((((pcRout + (t : ℝ) *
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) - Complex.I)) =
      pcZbar S t₁ t₂ θ₁ θ₂ (0 + (t : ℝ) * (Real.pi / 2 - 0)) -
        Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t
    rw [Complex.exp_add, Complex.exp_log hu, Complex.exp_log (hne t), pcZbar_div_self S,
      show (0 : ℝ) + (t : ℝ) * (Real.pi / 2 - 0) = (t : ℝ) * (Real.pi / 2) from by ring,
      pcZbar_q0 S (show (t : ℝ) * (Real.pi / 2) ∈ Set.Icc (0:ℝ) (Real.pi / 2) from
        ⟨mul_nonneg t.2.1 (by positivity), by nlinarith [t.2.2, Real.pi_pos]⟩),
      show (t : ℝ) * (Real.pi / 2) / (Real.pi / 2) = (t : ℝ) from by
        rw [mul_div_assoc, div_self (by positivity), mul_one]]
    ring
  have hav : ∀ t ∈ Set.Icc (0:ℝ) (Real.pi / 2), pcZbar S t₁ t₂ θ₁ θ₂ t ≠
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t ht hcon
    have h1 : pcZbar S t₁ t₂ θ₁ θ₂ t / Work.Smooth.SphereJordan.pccutDir S = Complex.I := by
      rw [hcon, mul_div_cancel_right₀ _ hu]
    rw [pcZbar_q0 S ht] at h1
    have h3 := congrArg Complex.im h1
    rw [Complex.ofReal_im, Complex.I_im] at h3
    norm_num at h3
  have hinc := Work.SphereJordan.incOn_eq_of_lift (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1) (z := Complex.I *
      Work.Smooth.SphereJordan.pccutDir S)
    (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2) hav
    ⟨fun t : unitInterval => Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log
      ((((pcRout + (t : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ)) : ℂ) -
        Complex.I), hcont⟩ hLift
  rw [hinc]
  show (Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log
      ((((pcRout + ((1 : unitInterval) : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ -
        pcRout) : ℝ)) : ℂ) - Complex.I)) -
      (Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log
      ((((pcRout + ((0 : unitInterval) : ℝ) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ -
        pcRout) : ℝ)) : ℂ) - Complex.I)) = _
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, show ((0 : unitInterval) : ℝ) = 0 from rfl,
    one_mul, zero_mul, add_zero,
    show (pcRout + (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) : ℝ) =
      ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ from by ring]
  ring

/-- The argument increment of the second quarter of `pcZbar` about `i·pccutDir S`. -/
theorem pcincOn_Zbar_q1 (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.SphereJordan.incOn (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) (Real.pi / 2) Real.pi =
      Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) - Complex.I) -
        Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ)) : ℂ) - Complex.I) := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  set Λ : unitInterval → ℂ := fun t => Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
    Complex.log (pczArcB S θ₁ θ₂ (t : ℝ) / Work.Smooth.SphereJordan.pccutDir S - Complex.I)
    with hΛdef
  have hne : ∀ t : unitInterval, pczArcB S θ₁ θ₂ (t : ℝ) /
      Work.Smooth.SphereJordan.pccutDir S - Complex.I ≠ 0 := fun t => pcpB_ne S hball θ₁ θ₂ t
  have hcont : Continuous Λ := by
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.add continuousAt_const ?_
    refine ContinuousAt.clog ?_ ?_
    · exact ((pccontinuous_zArcB S θ₁ θ₂).comp continuous_subtype_val).div_const _ |>.sub
        continuous_const |>.continuousAt
    · exact pcpB_slit S hball θ₁ θ₂ t
  have hLift : ∀ t : unitInterval, Complex.exp (Λ t) =
      pcZbar S t₁ t₂ θ₁ θ₂ (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2)) -
        Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t
    rw [hΛdef]
    simp only
    rw [Complex.exp_add, Complex.exp_log hu, Complex.exp_log (hne t), pcZbar_div_self S,
      pcZbar_q1 S hθ₁ (show Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) ∈
        Set.Icc (Real.pi / 2) Real.pi from
        ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
      show (Real.pi / 2 + (t : ℝ) * (Real.pi - Real.pi / 2) - Real.pi / 2) / (Real.pi / 2) =
        (t : ℝ) from by
          rw [add_sub_cancel_left, show (Real.pi - Real.pi / 2) = Real.pi / 2 from by ring,
            mul_div_assoc, div_self (by positivity), mul_one]]
    ring
  have hav : ∀ t ∈ Set.Icc (Real.pi / 2) Real.pi, pcZbar S t₁ t₂ θ₁ θ₂ t ≠
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t ht hcon
    have h1 : pcZbar S t₁ t₂ θ₁ θ₂ t / Work.Smooth.SphereJordan.pccutDir S = Complex.I := by
      rw [hcon, mul_div_cancel_right₀ _ hu]
    rw [pcZbar_q1 S hθ₁ ht] at h1
    have h3 := congrArg norm h1
    rw [norm_div, Complex.norm_I, Work.Smooth.SphereJordan.pcnorm_cutDir, div_one] at h3
    have h4 := pcnorm_zArcB_lt_one S θ₁ θ₂ hball ((t - Real.pi / 2) / (Real.pi / 2))
    linarith
  have hinc := Work.SphereJordan.incOn_eq_of_lift (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1) (z := Complex.I *
      Work.Smooth.SphereJordan.pccutDir S)
    (by linarith [Real.pi_pos] : (Real.pi / 2) ≤ Real.pi) hav ⟨Λ, hcont⟩ hLift
  rw [hinc]
  have e1 : Λ 1 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) - Complex.I) := by
    rw [hΛdef]
    simp only
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, pczArcB_one', hθ₂, pca₂_smul S t₂,
      mul_div_cancel_right₀ _ hu]
  have e0 : Λ 0 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ : ℝ)) : ℂ) - Complex.I) := by
    rw [hΛdef]
    simp only
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, pczArcB_zero', hθ₁, pca₁_smul S t₁,
      mul_div_cancel_right₀ _ hu]
  rw [show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 1 = Λ 1 from rfl,
    show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 0 = Λ 0 from rfl, e1, e0]
  ring

/-- The argument increment of the third quarter of `pcZbar` about `i·pccutDir S`. -/
theorem pcincOn_Zbar_q2
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.SphereJordan.incOn (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) Real.pi (3 * Real.pi / 2) =
      Complex.log (((-pcRout : ℝ) : ℂ) - Complex.I) -
        Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) - Complex.I) := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  set Λ : unitInterval → ℂ := fun t => Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
    Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) - Complex.I)
    with hΛdef
  have hne : ∀ t : unitInterval, ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ - (t : ℝ) *
      (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) - Complex.I) ≠ 0 := by
    intro t hcon
    have := congrArg Complex.im hcon
    rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im] at this
    norm_num at this
  have hcont : Continuous Λ := by
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.add continuousAt_const ?_
    refine ContinuousAt.clog ?_ ?_
    · fun_prop
    · rw [Complex.mem_slitPlane_iff]; right
      rw [Complex.sub_im, Complex.ofReal_im, Complex.I_im]; norm_num
  have hLift : ∀ t : unitInterval, Complex.exp (Λ t) =
      pcZbar S t₁ t₂ θ₁ θ₂ (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi)) -
        Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t
    rw [hΛdef]
    simp only
    rw [Complex.exp_add, Complex.exp_log hu, Complex.exp_log (hne t), pcZbar_div_self S,
      pcZbar_q2 S hθ₂ (show Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) ∈
        Set.Icc Real.pi (3 * Real.pi / 2) from
        ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
      show (Real.pi + (t : ℝ) * (3 * Real.pi / 2 - Real.pi) - Real.pi) / (Real.pi / 2) =
        (t : ℝ) from by
          rw [add_sub_cancel_left, show (3 * Real.pi / 2 - Real.pi) = Real.pi / 2 from by ring,
            mul_div_assoc, div_self (by positivity), mul_one]]
    ring
  have hav : ∀ t ∈ Set.Icc Real.pi (3 * Real.pi / 2), pcZbar S t₁ t₂ θ₁ θ₂ t ≠
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t ht hcon
    have h1 : pcZbar S t₁ t₂ θ₁ θ₂ t / Work.Smooth.SphereJordan.pccutDir S = Complex.I := by
      rw [hcon, mul_div_cancel_right₀ _ hu]
    rw [pcZbar_q2 S hθ₂ ht] at h1
    have h3 := congrArg Complex.im h1
    rw [Complex.ofReal_im, Complex.I_im] at h3
    norm_num at h3
  have hinc := Work.SphereJordan.incOn_eq_of_lift (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1) (z := Complex.I *
      Work.Smooth.SphereJordan.pccutDir S)
    (by linarith [Real.pi_pos] : Real.pi ≤ 3 * Real.pi / 2) hav ⟨Λ, hcont⟩ hLift
  rw [hinc]
  have e1 : Λ 1 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      Complex.log (((-pcRout : ℝ) : ℂ) - Complex.I) := by
    rw [hΛdef]
    simp only
    rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul,
      show (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
        (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ) = -pcRout from by ring]
  have e0 : Λ 0 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) +
      Complex.log ((((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ : ℝ)) : ℂ) - Complex.I) := by
    rw [hΛdef]
    simp only
    rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, sub_zero]
  rw [show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 1 = Λ 1 from rfl,
    show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 0 = Λ 0 from rfl, e1, e0]
  ring

/-- The argument increment of the fourth quarter of `pcZbar` about `i·pccutDir S`. -/
theorem pcincOn_Zbar_q3
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.SphereJordan.incOn (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) (3 * Real.pi / 2) (2 * Real.pi) =
      Complex.log (1 - Complex.I / ((pcRout : ℝ) : ℂ)) -
        Complex.log (1 + Complex.I / ((pcRout : ℝ) : ℂ)) - Complex.I * Real.pi := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have huR : ((pcRout : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt pcRout_pos)
  have hY : ∀ t : unitInterval, ‖Complex.I / ((pcRout : ℝ) : ℂ) * Complex.exp
      (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I))‖ = 1 / pcRout := by
    intro t
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos pcRout_pos,
      show -((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I) =
        (((-(Real.pi * (1 - (t : ℝ))) : ℝ)) : ℂ) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    ring
  have hre : ∀ t : unitInterval, 0 < (1 - Complex.I / ((pcRout : ℝ) : ℂ) * Complex.exp
      (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I))).re := by
    intro t
    have hle := Complex.re_le_norm (Complex.I / ((pcRout : ℝ) : ℂ) * Complex.exp
      (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I)))
    rw [hY t] at hle
    rw [Complex.sub_re, Complex.one_re]
    have hlt : (1 : ℝ) / pcRout < 1 := by rw [div_lt_one pcRout_pos]; exact pcone_lt_Rout
    linarith
  have hW : ∀ t : unitInterval, 1 - Complex.I / ((pcRout : ℝ) : ℂ) * Complex.exp
      (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I)) ≠ 0 := by
    intro t h0
    have h1 := hre t
    rw [h0] at h1
    simp at h1
  set Λ : unitInterval → ℂ := fun t =>
    Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log ((pcRout : ℝ) : ℂ) +
      (((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I +
      Complex.log (1 - Complex.I / ((pcRout : ℝ) : ℂ) *
        Complex.exp (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I)))
    with hΛdef
  have hcont : Continuous Λ := by
    rw [continuous_iff_continuousAt]
    intro t
    refine ContinuousAt.add (ContinuousAt.add (ContinuousAt.add continuousAt_const
      continuousAt_const) ?_) ?_
    · fun_prop
    · refine ContinuousAt.clog ?_ ?_
      · fun_prop
      · rw [Complex.mem_slitPlane_iff]; left; exact hre t
  have hLift : ∀ t : unitInterval, Complex.exp (Λ t) =
      pcZbar S t₁ t₂ θ₁ θ₂ (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2)) -
        Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t
    have hEE : Complex.exp ((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I) *
        Complex.exp (-((((Real.pi * (1 - (t : ℝ)) : ℝ)) : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [hΛdef]
    simp only
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_log hu,
      Complex.exp_log huR, Complex.exp_log (hW t), pcZbar_div_self S,
      pcZbar_q3 S (show 3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) ∈
        Set.Icc (3 * Real.pi / 2) (2 * Real.pi) from
        ⟨by nlinarith [t.2.1, Real.pi_pos], by nlinarith [t.2.2, Real.pi_pos]⟩),
      show (3 * Real.pi / 2 + (t : ℝ) * (2 * Real.pi - 3 * Real.pi / 2) - 3 * Real.pi / 2) /
        (Real.pi / 2) = (t : ℝ) from by
        rw [add_sub_cancel_left, show (2 * Real.pi - 3 * Real.pi / 2) = Real.pi / 2 from by ring,
          mul_div_assoc, div_self (by positivity), mul_one]]
    field_simp
    linear_combination (-Complex.I) * hEE
  have hav : ∀ t ∈ Set.Icc (3 * Real.pi / 2) (2 * Real.pi), pcZbar S t₁ t₂ θ₁ θ₂ t ≠
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := by
    intro t ht hcon
    have h1 : pcZbar S t₁ t₂ θ₁ θ₂ t / Work.Smooth.SphereJordan.pccutDir S = Complex.I := by
      rw [hcon, mul_div_cancel_right₀ _ hu]
    rw [pcZbar_q3 S ht] at h1
    have h3 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pcRout_pos,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_I] at h3
    linarith [pcone_lt_Rout]
  have hinc := Work.SphereJordan.incOn_eq_of_lift (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1) (z := Complex.I *
      Work.Smooth.SphereJordan.pccutDir S)
    (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi) hav ⟨Λ, hcont⟩ hLift
  rw [hinc]
  have e1 : Λ 1 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log ((pcRout : ℝ) : ℂ) +
      Complex.log (1 - Complex.I / ((pcRout : ℝ) : ℂ)) := by
    have hpt : ((Real.pi * (1 - ((1 : unitInterval) : ℝ)) : ℝ)) = 0 := by
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]; ring
    rw [hΛdef]
    simp only
    rw [hpt, show ((((0 : ℝ)) : ℂ) * Complex.I) = 0 from by simp,
      show -((0 : ℂ)) = 0 from by ring, Complex.exp_zero, mul_one, add_zero]
    try ring
  have e0 : Λ 0 = Complex.log (Work.Smooth.SphereJordan.pccutDir S) + Complex.log ((pcRout : ℝ) : ℂ) +
      Complex.I * Real.pi + Complex.log (1 + Complex.I / ((pcRout : ℝ) : ℂ)) := by
    have hpt : ((Real.pi * (1 - ((0 : unitInterval) : ℝ)) : ℝ)) = Real.pi := by
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]; ring
    rw [hΛdef]
    simp only
    rw [hpt, Complex.exp_neg, Complex.exp_pi_mul_I,
      show ((-1 : ℂ))⁻¹ = -1 from by norm_num, mul_neg, mul_one,
      show (1 : ℂ) - -(Complex.I / ((pcRout : ℝ) : ℂ)) =
        1 + Complex.I / ((pcRout : ℝ) : ℂ) from by ring,
      show (Real.pi : ℂ) * Complex.I = Complex.I * Real.pi from by ring]
    try ring
  rw [show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 1 = Λ 1 from rfl,
    show (⟨Λ, hcont⟩ : C(unitInterval, ℂ)) 0 = Λ 0 from rfl, e1, e0]
  ring

/-- The argument increment of `pcZbar` over one period about `i·pccutDir S`. -/
theorem pcincOn_Zbar_total (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.SphereJordan.incOn (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) 0 (2 * Real.pi) =
      -(2 * (Real.pi : ℂ) * Complex.I) := by
  have hav : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), pcZbar S t₁ t₂ θ₁ θ₂ t ≠
      Complex.I * Work.Smooth.SphereJordan.pccutDir S := fun t _ => pcZbar_ne_I S hball t
  have h1 := Work.SphereJordan.incOn_add (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
    (z := Complex.I * Work.Smooth.SphereJordan.pccutDir S)
    (show (0:ℝ) ≤ Real.pi by linarith [Real.pi_pos])
    (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos])
    (fun t _ => pcZbar_ne_I S hball t)
  have h2 := Work.SphereJordan.incOn_add (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
    (z := Complex.I * Work.Smooth.SphereJordan.pccutDir S)
    (show (0:ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos])
    (show Real.pi / 2 ≤ Real.pi by linarith [Real.pi_pos])
    (fun t _ => pcZbar_ne_I S hball t)
  have h3 := Work.SphereJordan.incOn_add (γ := pcZbar S t₁ t₂ θ₁ θ₂)
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
    (z := Complex.I * Work.Smooth.SphereJordan.pccutDir S)
    (show Real.pi ≤ 3 * Real.pi / 2 by linarith [Real.pi_pos])
    (show 3 * Real.pi / 2 ≤ 2 * Real.pi by linarith [Real.pi_pos])
    (fun t _ => pcZbar_ne_I S hball t)
  rw [h1, h2, h3,
    pcincOn_Zbar_q0 S hθ₁ hθ₂, pcincOn_Zbar_q1 S hball hθ₁ hθ₂, pcincOn_Zbar_q2 S hθ₁ hθ₂,
    pcincOn_Zbar_q3 S hθ₁ hθ₂, pclog_half_sub', pclog_neg_Rout']
  ring

/-- The winding number of `pcZbar` about `i·pccutDir S` is `-1`. -/
theorem pcwindNumber_Zbar_I (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (hθ₁ : γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)
    (hθ₂ : γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) :
    Work.Smooth.SphereJordan.windNumber (pcZbar S t₁ t₂ θ₁ θ₂)
      ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
      (Complex.I * Work.Smooth.SphereJordan.pccutDir S) = -1 := by
  have hper := Work.SphereJordan.incOn_period
    ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
    (pcZbar_periodic S t₁ t₂ θ₁ θ₂) (Complex.I * Work.Smooth.SphereJordan.pccutDir S)
    (pcZbar_ne_I S hball) 0
  rw [zero_add] at hper
  rw [pcincOn_Zbar_total S hball hθ₁ hθ₂] at hper
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))) Complex.I_ne_zero
  have h3 : (Work.Smooth.SphereJordan.windNumber (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I) = (-1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hper]; ring
  have h4 : (Work.Smooth.SphereJordan.windNumber (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) : ℂ) = (-1 : ℂ) :=
    mul_right_cancel₀ hne h3
  exact_mod_cast h4


/-- The ray in the direction `-i·pccutDir S` misses the auxiliary curve. -/
theorem pcZbar_ne_ray (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (σ : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    pcZbar S t₁ t₂ θ₁ θ₂ σ ≠ (s : ℂ) * (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)) := by
  intro h
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have h1 : pcZbar S t₁ t₂ θ₁ θ₂ σ / Work.Smooth.SphereJordan.pccutDir S =
      -((s : ℂ) * Complex.I) := by
    rw [h]
    rw [show (s : ℂ) * (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)) /
        Work.Smooth.SphereJordan.pccutDir S = -((s : ℂ) * Complex.I) from by
      rw [mul_div_assoc, show -(Complex.I * Work.Smooth.SphereJordan.pccutDir S) /
        Work.Smooth.SphereJordan.pccutDir S = -Complex.I from by
          rw [neg_div, mul_div_cancel_right₀ _ hu]]
      ring]
  rw [pcZbar] at h1
  set τ := Work.Smooth.SphereJordan.pcperPt σ with hτdef
  have hτlt : τ < 2 * Real.pi := (Work.SphereJordan.pcperPt_mem σ).2
  have hnorm : ‖-((s : ℂ) * Complex.I)‖ = s := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), Complex.norm_I, mul_one]
  rcases lt_or_ge (Real.pi / 2) τ with hc | hc
  · rcases lt_or_ge Real.pi τ with hc' | hc'
    · rcases lt_or_ge (3 * Real.pi / 2) τ with hc'' | hc''
      · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
            ((pcRout : ℝ) : ℂ) * Complex.exp
              (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) * Complex.I) := by
          rw [pczBarUn_q3 (not_le.mpr hc) (not_le.mpr hc') (not_le.mpr hc''), pczArcD_apply,
            show ((pcRout : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S *
                Complex.exp (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
                  Complex.I) = (((pcRout : ℝ) : ℂ) * Complex.exp
                    (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) *
                      Complex.I)) * Work.Smooth.SphereJordan.pccutDir S from by ring,
            mul_div_cancel_right₀ _ hu]
        rw [h2] at h1
        have h3 := congrArg Complex.im h1
        rw [show (((pcRout : ℝ) : ℂ) * Complex.exp
            (((Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2)) : ℝ) : ℂ) * Complex.I)).im =
            pcRout * Real.sin (Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2))) from by
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
            zero_mul, add_zero],
          show (-((s : ℂ) * Complex.I)).im = -s from by
            rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
              Complex.I_re, mul_one, mul_zero, add_zero]] at h3
        have hy1 : (τ - 3 * Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [hτlt]
        have hy0 : 0 ≤ (τ - 3 * Real.pi / 2) / (Real.pi / 2) :=
          div_nonneg (by linarith) (by positivity)
        have hsin : 0 ≤ Real.sin (Real.pi * (1 - (τ - 3 * Real.pi / 2) / (Real.pi / 2))) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
        nlinarith [h3, hsin, pcRout_pos, hs]
      · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
            (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - t₂ -
              (τ - Real.pi) / (Real.pi / 2) *
                (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + pcRout - t₂) : ℝ)) : ℂ) := by
          rw [pczBarUn_q2 (not_le.mpr hc) (not_le.mpr hc') hc'', pczArcC_apply,
            mul_div_cancel_right₀ _ hu]
        rw [h2] at h1
        have h3 := congrArg Complex.im h1
        rw [Complex.ofReal_im,
          show (-((s : ℂ) * Complex.I)).im = -s from by
            rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
              Complex.I_re, mul_one, mul_zero, add_zero]] at h3
        linarith
    · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
          pczArcB S θ₁ θ₂ ((τ - Real.pi / 2) / (Real.pi / 2)) /
            Work.Smooth.SphereJordan.pccutDir S := by
        rw [pczBarUn_q1 (not_le.mpr hc) hc']
      rw [h2] at h1
      have h3 := congrArg norm h1
      rw [norm_div, Work.Smooth.SphereJordan.pcnorm_cutDir, div_one, hnorm] at h3
      have h4 := pcnorm_zArcB_lt_one S θ₁ θ₂ hball ((τ - Real.pi / 2) / (Real.pi / 2))
      linarith
  · have h2 : pczBarUn S t₁ t₂ θ₁ θ₂ τ / Work.Smooth.SphereJordan.pccutDir S =
        (((pcRout + τ / (Real.pi / 2) * (‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + t₁ - pcRout) :
          ℝ)) : ℂ) := by
      rw [pczBarUn_q0 hc, pczArcA_apply, mul_div_cancel_right₀ _ hu]
    rw [h2] at h1
    have h3 := congrArg Complex.im h1
    rw [Complex.ofReal_im,
      show (-((s : ℂ) * Complex.I)).im = -s from by
        rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
          Complex.I_re, mul_one, mul_zero, add_zero]] at h3
    linarith

end WindMain


/-- **The two pieces of the cut pcannulus are different.** -/
theorem pcpieceUpNePieceDown (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ t₂ s₂ : ℝ}
    (ht₁ : 0 < t₁) (hts₁ : t₁ < s₁) (ht₂ : 0 < t₂) (hts₂ : t₂ < s₂)
    (hsph₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (hsph₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (ha₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (ha₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace)
    (hseg₁ : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hseg₂ : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V)
    (hb₁ : ∀ σ : ℝ, t₁ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V)
    (hb₂ : ∀ σ : ℝ, t₂ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V) :
    Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂ ≠
      Work.Smooth.SphereJordan.pcpieceDown S t₁ s₁ t₂ s₂ := by
  obtain ⟨θ₁, hθ₁⟩ := ha₁
  obtain ⟨θ₂, hθ₂⟩ := ha₂
  obtain ⟨hout₁, hout₂⟩ := Work.Smooth.SphereJordan.pccut_outer_eq S hball
    (by linarith) (by linarith) hsph₁ hsph₂
  have hsimple := pczCurve_isSimple S hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂ hts₂ hseg₁ hseg₂
  obtain ⟨S'⟩ := h (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂) hsimple
  have hV : Complex.I * Work.Smooth.SphereJordan.pccutDir S ∈ S'.V := by
    refine pcmem_V_of_windNumber_ne_zero' S' ?_ ?_
    · intro hmem
      obtain ⟨σ, hσ⟩ := hmem
      exact pcZbar_ne_I S hball σ hσ
    · change Work.Smooth.SphereJordan.windNumber (pcZbar S t₁ t₂ θ₁ θ₂)
        ((pcZbar_continuous_periodic S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).1)
        (Complex.I * Work.Smooth.SphereJordan.pccutDir S) ≠ 0
      rw [pcwindNumber_Zbar_I S hball hθ₁ hθ₂]
      norm_num
  have hU : -(Complex.I * Work.Smooth.SphereJordan.pccutDir S) ∈ S'.U := by
    set W : Set ℂ := {z | ∃ s : ℝ, 1 ≤ s ∧
      z = (s : ℂ) * (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S))} with hWdef
    have hpre : IsPreconnected W := by
      have hWeq : W = (fun s : ℝ => (s : ℂ) *
          (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S))) '' Set.Ici (1:ℝ) := by
        ext z
        constructor
        · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
        · rintro ⟨s, hs, rfl⟩; exact ⟨s, hs, rfl⟩
      rw [hWeq]
      exact isPreconnected_Ici.image _ (by fun_prop : Continuous (fun s : ℝ => (s : ℂ) *
        (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)))).continuousOn
    have hsub : W ⊆ (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).traceᶜ := by
      rintro z ⟨s, hs, rfl⟩ hmem
      obtain ⟨σ, hσ⟩ := hmem
      exact pcZbar_ne_ray S hball σ hs hσ
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S'.toPlaneSeparation
      hpre hsub with hU' | hV'
    · exact hU' ⟨1, le_refl 1, by simp⟩
    · obtain ⟨D, hD⟩ := S'.bounded_V.exists_norm_le
      obtain ⟨x₀, hx₀⟩ := S'.nonempty_V
      have hD0 : 0 ≤ D := le_trans (norm_nonneg x₀) (hD x₀ hx₀)
      have hmem := hV' ⟨D + 1, by linarith, rfl⟩
      have h1 : ‖-(Complex.I * Work.Smooth.SphereJordan.pccutDir S)‖ = 1 := by
        rw [norm_neg, norm_mul, Complex.norm_I, Work.Smooth.SphereJordan.pcnorm_cutDir, one_mul]
      have hnorm : ‖((D + 1 : ℝ) : ℂ) *
          (-(Complex.I * Work.Smooth.SphereJordan.pccutDir S))‖ = D + 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), h1, mul_one]
      have hle := hD _ hmem
      rw [hnorm] at hle
      linarith
  have hsubUp : Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂ ⊆
      (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).traceᶜ := by
    intro z hz hztrace
    obtain ⟨σ, hσ⟩ := hztrace
    refine pcZbar_notMem_annulusCut S t₁ s₁ t₂ s₂ θ₁ θ₂ hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂
      hts₂ hseg₁ hseg₂ σ ?_
    change (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).γ σ ∈
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂
    rw [hσ]
    exact connectedComponentIn_subset (Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂)
      _ hz
  have hsubDn : Work.Smooth.SphereJordan.pcpieceDown S t₁ s₁ t₂ s₂ ⊆
      (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).traceᶜ := by
    intro z hz hztrace
    obtain ⟨σ, hσ⟩ := hztrace
    refine pcZbar_notMem_annulusCut S t₁ s₁ t₂ s₂ θ₁ θ₂ hball hout₁ hout₂ hθ₁ hθ₂ ht₁ hts₁ ht₂
      hts₂ hseg₁ hseg₂ σ ?_
    change (pczCurve S t₁ t₂ θ₁ θ₂ hθ₁ hθ₂).γ σ ∈
      Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂
    rw [hσ]
    exact connectedComponentIn_subset (Work.Smooth.SphereJordan.pcannulusCut S t₁ s₁ t₂ s₂)
      _ hz
  have hUpV : Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂ ⊆ S'.V := by
    have hpre : IsPreconnected (Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂) :=
      isPreconnected_connectedComponentIn
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S'.toPlaneSeparation
      hpre hsubUp with h1 | h2
    · exfalso
      exact Set.disjoint_left.mp S'.disjoint_UV
        (h1 (mem_connectedComponentIn (Work.Smooth.SphereJordan.pcI_mul_cutDir_mem_annulusCut S hball))) hV
    · exact h2
  have hDnU : Work.Smooth.SphereJordan.pcpieceDown S t₁ s₁ t₂ s₂ ⊆ S'.U := by
    have hpre : IsPreconnected (Work.Smooth.SphereJordan.pcpieceDown S t₁ s₁ t₂ s₂) :=
      isPreconnected_connectedComponentIn
    have hU' : (-Complex.I) * Work.Smooth.SphereJordan.pccutDir S ∈ S'.U := by
      rw [neg_mul]; exact hU
    rcases Work.Smooth.Jordan.plane_separation_preconnected_subset S'.toPlaneSeparation
      hpre hsubDn with h1 | h2
    · exact h1
    · exfalso
      exact Set.disjoint_left.mp S'.disjoint_UV hU'
        (h2 (mem_connectedComponentIn (Work.Smooth.SphereJordan.pcneg_I_mul_cutDir_mem_annulusCut S hball)))
  intro heq
  have hmem : Complex.I * Work.Smooth.SphereJordan.pccutDir S ∈ S'.U := by
    have h1 : Complex.I * Work.Smooth.SphereJordan.pccutDir S ∈
        Work.Smooth.SphereJordan.pcpieceUp S t₁ s₁ t₂ s₂ :=
      mem_connectedComponentIn (Work.Smooth.SphereJordan.pcI_mul_cutDir_mem_annulusCut S hball)
    rw [heq] at h1
    exact hDnU h1
  exact Set.disjoint_left.mp S'.disjoint_UV hmem hV

end Main

end


end Work.Smooth.SphereJordan.Crux
