import Mathlib
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.uniformBoundsC1

/-!
# The chord frame of a sweep loop

The sweep of a band arc produces, at each parameter `σ`, a loop made of two pieces: the *retained
arc* `ξ ↦ r (ta σ + ξ * w σ)` of the knot together with the straight *chord* from `r (ta σ)` to
`r (tb σ)`.  This module sets up the coordinates of the chord frame — the coordinate along the
chord and the component orthogonal to it — and proves the two elementary geometric facts that the
low end of the sweep consumes:

* `Work.Drive.arcCoord_strictMono`: for a *short* retained arc the chord coordinate is *strictly
  increasing*, so that the projection of the arc along the chord direction is injective (the arc is
  a graph over the chord).  The estimate is the mean value theorem plus the two global bounds of an
  analytic knot (a positive lower bound on the speed and a Lipschitz constant for the velocity);
* `Work.Drive.arcPerp_ne_zero`: consequently a point of the retained arc lying on the chord *line*
  lies on the chord *segment*, which the `O`-avoidance forbids.  Hence the transverse part of the
  retained arc never vanishes in the interior: the arc meets the chord only at its two endpoints —
  the geometric form of the avoidance hypothesis used by the low end.

Both statements are unconditional (no genericity): the only input is that the retained arc is
shorter than a threshold depending on the knot alone.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-! ## 1. The chord frame of two points -/

/-- The unit vector in the direction of the chord from `A` to `B` (zero when `A = B`). -/
def chordDir (A B : Space) : Space := ‖B - A‖⁻¹ • (B - A)

/-- The signed coordinate of `P` from `A` along the chord direction. -/
def chordCoord (A B P : Space) : ℝ := inner ℝ (P - A) (chordDir A B)

/-- The component of `P - A` orthogonal to the chord direction. -/
def chordPerp (A B P : Space) : Space := P - A - chordCoord A B P • chordDir A B

lemma chordDir_norm_le (A B : Space) : ‖chordDir A B‖ ≤ 1 := by
  rw [chordDir, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases h : ‖B - A‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

lemma chordDir_norm (A B : Space) (h : A ≠ B) : ‖chordDir A B‖ = 1 := by
  have hne : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
  rw [chordDir, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hne]

lemma chordDir_smul (A B : Space) (h : A ≠ B) : ‖B - A‖ • chordDir A B = B - A := by
  have hne : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
  rw [chordDir, smul_smul, mul_inv_cancel₀ hne, one_smul]

lemma chordCoord_self (A B : Space) : chordCoord A B A = 0 := by
  simp [chordCoord]

lemma chordCoord_other (A B : Space) (h : A ≠ B) : chordCoord A B B = ‖B - A‖ := by
  show inner ℝ (B - A) (chordDir A B) = ‖B - A‖
  conv_lhs => rw [← chordDir_smul A B h]
  rw [inner_smul_left, real_inner_self_eq_norm_sq, chordDir_norm A B h, RCLike.conj_to_real]
  ring

lemma abs_chordCoord_le (A B P : Space) : |chordCoord A B P| ≤ ‖P - A‖ := by
  calc |chordCoord A B P| = |inner ℝ (P - A) (chordDir A B)| := rfl
    _ ≤ ‖P - A‖ * ‖chordDir A B‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖P - A‖ * 1 := mul_le_mul_of_nonneg_left (chordDir_norm_le A B) (norm_nonneg _)
    _ = ‖P - A‖ := mul_one _

lemma chordPerp_eq_zero_iff (A B P : Space) :
    chordPerp A B P = 0 ↔ P - A = chordCoord A B P • chordDir A B := by
  rw [chordPerp, sub_eq_zero]

/-- **A point of the chord line strictly between `A` and `B` lies on the open segment.** -/
lemma mem_openSegment_of_chordPerp_eq_zero {A B P : Space} (hAB : A ≠ B)
    (h0 : 0 < chordCoord A B P) (h1 : chordCoord A B P < ‖B - A‖)
    (hperp : chordPerp A B P = 0) : P ∈ openSegment ℝ A B := by
  have hL : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hAB))
  have hdec : P - A = chordCoord A B P • chordDir A B := (chordPerp_eq_zero_iff A B P).mp hperp
  rw [openSegment_eq_image]
  refine ⟨chordCoord A B P / ‖B - A‖, ⟨div_pos h0 hL, (div_lt_one hL).mpr h1⟩, ?_⟩
  show (1 - chordCoord A B P / ‖B - A‖) • A + (chordCoord A B P / ‖B - A‖) • B = P
  have hθ : chordCoord A B P / ‖B - A‖ * ‖B - A‖ = chordCoord A B P :=
    div_mul_cancel₀ _ (ne_of_gt hL)
  have hred : (1 - chordCoord A B P / ‖B - A‖) • A + (chordCoord A B P / ‖B - A‖) • B
      = A + chordCoord A B P • chordDir A B := by
    rw [smul_add_smul_eq_add_smul_sub (s := 1 - chordCoord A B P / ‖B - A‖)
      (t := chordCoord A B P / ‖B - A‖) (by ring)]
    congr 1
    calc (chordCoord A B P / ‖B - A‖) • (B - A)
        = (chordCoord A B P / ‖B - A‖) • (‖B - A‖ • chordDir A B) := by
          congr 1
          exact (chordDir_smul A B hAB).symm
      _ = ((chordCoord A B P / ‖B - A‖) * ‖B - A‖) • chordDir A B := by rw [smul_smul]
      _ = chordCoord A B P • chordDir A B := by rw [hθ]
  rw [hred, ← hdec]
  abel

/-! ## 2. The chord frame of a retained arc -/

/-- The chord coordinate of the point at fraction `ξ` of the retained arc at parameter `σ`. -/
def arcCoord (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (τ : I) (ξ : ℝ) : ℝ :=
  chordCoord (r (D.ta τ)) (r (D.tb τ)) (sweepArc r D τ ξ)

/-- The transverse component of that point. -/
def arcPerp (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (τ : I) (ξ : ℝ) : Space :=
  chordPerp (r (D.ta τ)) (r (D.tb τ)) (sweepArc r D τ ξ)

lemma arcCoord_eq (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (τ : I) (ξ : ℝ) :
    arcCoord r D τ ξ = inner ℝ (r (D.ta τ + ξ * sweepW D τ) - r (D.ta τ))
      (chordDir (r (D.ta τ)) (r (D.tb τ))) := rfl

lemma arcPerp_eq (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (τ : I) (ξ : ℝ) :
    arcPerp r D τ ξ = sweepArc r D τ ξ - r (D.ta τ)
      - arcCoord r D τ ξ • chordDir (r (D.ta τ)) (r (D.tb τ)) := rfl

/-! ## 3. Global bounds of an analytic knot -/

/-- **Speed bounds and a Lipschitz constant for the velocity of an analytic knot.** -/
theorem exists_knot_c2_bounds {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ m M C : ℝ, 0 < m ∧ 0 < M ∧ 0 < C ∧
      (∀ t : ℝ, m ≤ ‖velocity r t‖) ∧ (∀ t : ℝ, ‖velocity r t‖ ≤ M) ∧
      (∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|) := by
  have hp : 0 < period := period_pos
  have hvcont : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hvper : Function.Periodic (velocity r) period := by
    intro t
    have h1 : (fun y : ℝ => r (y + period)) = r := funext fun y => hr.periodic y
    have h2 : deriv (fun y : ℝ => r (y + period)) t = deriv r (t + period) :=
      deriv_comp_add_const r period t
    rw [h1] at h2
    exact h2.symm
  have hne : (Set.Icc (0 : ℝ) period).Nonempty := ⟨0, le_rfl, hp.le⟩
  obtain ⟨t₀, _, hmin₀⟩ := isCompact_Icc.exists_isMinOn hne hvcont.norm.continuousOn
  obtain ⟨t₁, _, hmax₀⟩ := isCompact_Icc.exists_isMaxOn hne hvcont.norm.continuousOn
  have hmpos : 0 < ‖velocity r t₀‖ := norm_pos_iff.mpr (hr.regular t₀)
  have hMpos : 0 < ‖velocity r t₁‖ + 1 := by positivity
  have hderivCin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
  have hd2cont : Continuous (fun t : ℝ => deriv (deriv r) t) :=
    hderivCin.continuous_deriv (by simp)
  have hd2per : Function.Periodic (fun t : ℝ => deriv (deriv r) t) period := by
    intro t
    have h1 : (fun y : ℝ => deriv r (y + period)) = deriv r := funext fun y => hvper y
    have h2 : deriv (fun y : ℝ => deriv r (y + period)) t = deriv (deriv r) (t + period) :=
      deriv_comp_add_const (deriv r) period t
    rw [h1] at h2
    exact h2.symm
  obtain ⟨t₂, _, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hd2cont.norm.continuousOn
  set C : ℝ := ‖deriv (deriv r) t₂‖ + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCbound : ∀ t : ℝ, ‖deriv (deriv r) t‖ ≤ C := by
    intro t
    obtain ⟨y, hy, hty⟩ := hd2per.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖deriv (deriv r) t‖ = ‖deriv (deriv r) y‖ := by rw [hty]
      _ ≤ ‖deriv (deriv r) t₂‖ := hmax₂ hy'
      _ ≤ C := by rw [hCdef]; linarith
  have hveldiff : Differentiable ℝ (velocity r) := hderivCin.differentiable (by simp)
  have hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t| := by
    intro t t'
    rcases le_total t t' with hle | hle
    · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := velocity r)
        (f' := fun x : ℝ => deriv (deriv r) x) (a := t) (b := t') (C := C)
        (fun x _ => (hveldiff x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t' ⟨hle, le_rfl⟩
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t' - t), norm_sub_rev]
      exact h
    · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := velocity r)
        (f' := fun x : ℝ => deriv (deriv r) x) (a := t') (b := t) (C := C)
        (fun x _ => (hveldiff x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hCbound x) t ⟨hle, le_rfl⟩
      rw [abs_of_nonpos (by linarith : t' - t ≤ 0), neg_sub]
      exact h
  refine ⟨‖velocity r t₀‖, ‖velocity r t₁‖ + 1, C, hmpos, hMpos, hCpos, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖velocity r t₀‖ ≤ ‖velocity r y‖ := hmin₀ hy'
      _ = ‖velocity r t‖ := by rw [hty]
  · intro t
    obtain ⟨y, hy, hty⟩ := hvper.exists_mem_Ico hp t 0
    have hy' : y ∈ Set.Icc (0 : ℝ) period := Set.Ico_subset_Icc_self (by simpa using hy)
    calc ‖velocity r t‖ = ‖velocity r y‖ := by rw [hty]
      _ ≤ ‖velocity r t₁‖ := hmax₀ hy'
      _ ≤ ‖velocity r t₁‖ + 1 := by linarith
  · exact hlip

/-! ## 4. The retained arc is a graph over its chord -/

lemma deriv_arcCoord {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    (τ : I) (ξ : ℝ) :
    deriv (arcCoord r D τ) ξ
      = sweepW D τ * inner ℝ (velocity r (D.ta τ + ξ * sweepW D τ))
          (chordDir (r (D.ta τ)) (r (D.tb τ))) := by
  set w := sweepW D τ with hw
  set u := chordDir (r (D.ta τ)) (r (D.tb τ)) with hu
  have hfun : arcCoord r D τ = fun s : ℝ =>
      inner ℝ (r (D.ta τ + s * w)) u - inner ℝ (r (D.ta τ)) u := by
    funext s
    rw [arcCoord, chordCoord, sweepArc, inner_sub_left]
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => r (D.ta τ + s * w)) ξ := by
    have hlin : DifferentiableAt ℝ (fun s : ℝ => D.ta τ + s * w) ξ := by fun_prop
    exact (hr.smooth.differentiable (by simp)).differentiableAt.comp ξ hlin
  have hderiv_comp : deriv (fun s : ℝ => r (D.ta τ + s * w)) ξ
      = w • velocity r (D.ta τ + ξ * w) := by
    have hlin : DifferentiableAt ℝ (fun s : ℝ => D.ta τ + s * w) ξ := by fun_prop
    have hdiffr : DifferentiableAt ℝ r (D.ta τ + ξ * w) :=
      (hr.smooth.differentiable (by simp)).differentiableAt
    have hcomp := deriv.scomp ξ hdiffr hlin
    have hlin_deriv : deriv (fun s : ℝ => D.ta τ + s * w) ξ = w := by
      have h : HasDerivAt (fun s : ℝ => D.ta τ + s * w) w ξ := by
        simpa using ((hasDerivAt_id ξ).mul_const w).const_add (D.ta τ)
      exact h.deriv
    have hfun : (fun s : ℝ => r (D.ta τ + s * w))
        = (fun y : ℝ => r y) ∘ (fun s : ℝ => D.ta τ + s * w) := rfl
    rw [hfun, hcomp, hlin_deriv]
    rfl
  have hderiv_inner : deriv (fun s : ℝ => inner ℝ (r (D.ta τ + s * w)) u) ξ
      = inner ℝ (w • velocity r (D.ta τ + ξ * w)) u := by
    have h := deriv_inner_apply (𝕜 := ℝ) hdiff (differentiableAt_const u)
    rw [hderiv_comp] at h
    simpa using h
  rw [hfun, deriv_sub_const, hderiv_inner, inner_smul_left, RCLike.conj_to_real]

/-- **The derivative of the chord coordinate of a retained arc is positive in the interior.**
This is the pointwise form of `Work.Drive.arcCoord_strictMono` (same hypotheses): the mean-value
estimate that makes the along-coordinate strictly increasing in fact gives a strictly positive
derivative at every interior point.  It is the hypothesis `deriv x > 0` of
`Work.Drive.lensConcaveInChordCoord`, hence the brick that turns the sign of the acceleration of
the knot into the concavity of the profile in the chord coordinate. -/
theorem arcCoord_deriv_pos {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (τ : I) {m δ M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 < C)
    (hmin : ∀ t : ℝ, m ≤ ‖velocity r t‖)
    (hchord : ∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖)
    (hmax : ∀ t : ℝ, ‖velocity r t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    (hW0 : 0 < sweepW D τ) (hWδ : sweepW D τ ≤ δ)
    (hsmall : sweepW D τ < m ^ 2 / (2 * M * C)) :
    ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv (arcCoord r D τ) ξ := by
  set w := sweepW D τ with hw
  set ta := D.ta τ with hta
  set tb := D.tb τ with htb
  set u := chordDir (r ta) (r tb) with hu
  have hwtb : w = tb - ta := rfl
  have hlt : ta < tb := by rw [hwtb] at hW0; linarith
  have habs : |tb - ta| = w := by rw [abs_of_pos (by linarith : (0:ℝ) < tb - ta), hwtb]
  have hLpos : 0 < ‖r tb - r ta‖ := by
    have h1 : (m / 2) * w ≤ ‖r ta - r tb‖ := by
      have h := hchord ta tb (by rw [habs]; exact hWδ)
      rwa [habs] at h
    have h2 : 0 < (m / 2) * w := mul_pos (by linarith) hW0
    rw [norm_sub_rev] at h1
    linarith
  have hAB : r ta ≠ r tb := by
    intro h
    rw [h, sub_self, norm_zero] at hLpos
    exact lt_irrefl _ hLpos
  have hpow : 0 < m ^ 2 - M * (C * w) := by
    have hpos : 0 < 2 * M * C := by positivity
    have hw2 : w * (2 * M * C) < m ^ 2 := (lt_div_iff₀ hpos).mp hsmall
    nlinarith [hw2, hW0]
  have hpos_inner : ∀ t ∈ Set.Icc ta tb, 0 < inner ℝ (velocity r t) u := by
    intro t ht
    have hcont : ContinuousOn (fun s : ℝ => inner ℝ (velocity r t) (r s)) (Set.Icc ta tb) :=
      continuous_const.continuousOn.inner
        ((hr.smooth.continuous.comp continuous_id).continuousOn)
    have hdiff : DifferentiableOn ℝ (fun s : ℝ => inner ℝ (velocity r t) (r s)) (Set.Ioo ta tb) := by
      intro s _
      exact ((differentiableAt_const (c := velocity r t) (x := s)).inner (𝕜 := ℝ)
        ((hr.smooth.differentiable (by simp)).differentiableAt)).differentiableWithinAt
    obtain ⟨s₀, hs₀, hs₀eq⟩ :=
      exists_deriv_eq_slope (fun s : ℝ => inner ℝ (velocity r t) (r s)) hlt hcont hdiff
    have hderiv : deriv (fun s : ℝ => inner ℝ (velocity r t) (r s)) s₀
        = inner ℝ (velocity r t) (velocity r s₀) := by
      have h := deriv_inner_apply (𝕜 := ℝ) (f := fun _ : ℝ => velocity r t) (g := r)
        (x := s₀) (differentiableAt_const (c := velocity r t) (x := s₀))
        (((hr.smooth.differentiable (by simp)).differentiableAt :
          DifferentiableAt ℝ r s₀))
      simpa [velocity] using h
    have hslope : inner ℝ (velocity r t) (r tb) - inner ℝ (velocity r t) (r ta)
        = (tb - ta) * inner ℝ (velocity r t) (velocity r s₀) := by
      have h2 := hs₀eq
      rw [hderiv] at h2
      have hne : (tb - ta) ≠ 0 := ne_of_gt (by linarith)
      rw [eq_div_iff hne] at h2
      rw [mul_comm (tb - ta) (inner ℝ (velocity r t) (velocity r s₀))]
      exact h2.symm
    have hlaw : ‖r tb - r ta‖ * inner ℝ (velocity r t) u
        = w * inner ℝ (velocity r t) (velocity r s₀) := by
      have h1 : inner ℝ (velocity r t) (r tb - r ta)
          = ‖r tb - r ta‖ * inner ℝ (velocity r t) u := by
        have h0 : r tb - r ta = ‖r tb - r ta‖ • u := (chordDir_smul (r ta) (r tb) hAB).symm
        conv_lhs => rw [h0]
        rw [inner_smul_right]
      have h2 : inner ℝ (velocity r t) (r tb - r ta)
          = (tb - ta) * inner ℝ (velocity r t) (velocity r s₀) := by
        rw [inner_sub_right, hslope]
      rw [← h1, h2, hwtb]
    have hsdist : |s₀ - t| ≤ w := by
      rw [abs_le]
      constructor
      · rw [hwtb]; linarith [hs₀.1, ht.1, ht.2]
      · rw [hwtb]; linarith [hs₀.2, ht.1, ht.2]
    have hvel : m ^ 2 - M * (C * w) ≤ inner ℝ (velocity r t) (velocity r s₀) := by
      have hsplit : inner ℝ (velocity r t) (velocity r s₀)
          = ‖velocity r t‖ ^ 2 - inner ℝ (velocity r t) (velocity r t - velocity r s₀) := by
        have h1 : velocity r s₀ = velocity r t - (velocity r t - velocity r s₀) := by abel
        conv_lhs => rw [h1]
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      rw [hsplit]
      have hb1 : inner ℝ (velocity r t) (velocity r t - velocity r s₀) ≤ M * (C * w) := by
        have h4 := abs_real_inner_le_norm (velocity r t) (velocity r t - velocity r s₀)
        have h5 : inner ℝ (velocity r t) (velocity r t - velocity r s₀)
            ≤ ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖ := le_trans (le_abs_self _) h4
        have h6 : ‖velocity r t - velocity r s₀‖ ≤ C * w := by
          calc ‖velocity r t - velocity r s₀‖ ≤ C * |s₀ - t| := hlip t s₀
            _ ≤ C * w := by gcongr
        calc inner ℝ (velocity r t) (velocity r t - velocity r s₀)
            ≤ ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖ := h5
          _ ≤ M * (C * w) := by
              have h7 : ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖
                  ≤ M * ‖velocity r t - velocity r s₀‖ :=
                mul_le_mul_of_nonneg_right (hmax t) (norm_nonneg _)
              have h8 : M * ‖velocity r t - velocity r s₀‖ ≤ M * (C * w) :=
                mul_le_mul_of_nonneg_left h6 hM.le
              linarith
      have hspd : m ^ 2 ≤ ‖velocity r t‖ ^ 2 := by nlinarith [hmin t, hm]
      linarith
    have hprod : 0 < ‖r tb - r ta‖ * inner ℝ (velocity r t) u := by
      rw [hlaw]
      exact mul_pos hW0 (lt_of_lt_of_le hpow hvel)
    rw [mul_comm (‖r tb - r ta‖) (inner ℝ (velocity r t) u)] at hprod
    exact pos_of_mul_pos_left hprod (norm_nonneg _)
  intro ξ hξ
  rw [deriv_arcCoord hr D τ ξ]
  refine mul_pos hW0 (hpos_inner _ ?_)
  have h1 : w = sweepW D τ := hw
  have h2 : ta = D.ta τ := hta
  have h3 : tb = D.tb τ := htb
  have hmem : D.ta τ + ξ * sweepW D τ ∈ Set.Icc (D.ta τ) (D.tb τ) := by
    constructor
    · have h4 : sweepW D τ = D.tb τ - D.ta τ := rfl
      rw [h4]; nlinarith [hξ.1, hW0, h4]
    · have h4 : sweepW D τ = D.tb τ - D.ta τ := rfl
      rw [h4]; nlinarith [hξ.2, hW0, h4]
  simpa only [← h1, ← h2, ← h3] using hmem

/-- **The chord coordinate of a short retained arc is strictly increasing.** -/

theorem arcCoord_strictMono {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (τ : I) {m δ M C : ℝ} (hm : 0 < m) (hM : 0 < M) (hC : 0 < C)
    (hmin : ∀ t : ℝ, m ≤ ‖velocity r t‖)
    (hchord : ∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖)
    (hmax : ∀ t : ℝ, ‖velocity r t‖ ≤ M)
    (hlip : ∀ t t' : ℝ, ‖velocity r t - velocity r t'‖ ≤ C * |t' - t|)
    (hW0 : 0 < sweepW D τ) (hWδ : sweepW D τ ≤ δ)
    (hsmall : sweepW D τ < m ^ 2 / (2 * M * C)) :
    StrictMonoOn (arcCoord r D τ) (Set.Icc (0 : ℝ) 1) := by
  set w := sweepW D τ with hw
  set ta := D.ta τ with hta
  set tb := D.tb τ with htb
  set u := chordDir (r ta) (r tb) with hu
  have hwtb : w = tb - ta := rfl
  have hlt : ta < tb := by rw [hwtb] at hW0; linarith
  have habs : |tb - ta| = w := by rw [abs_of_pos (by linarith : (0:ℝ) < tb - ta), hwtb]
  have hLpos : 0 < ‖r tb - r ta‖ := by
    have h1 : (m / 2) * w ≤ ‖r ta - r tb‖ := by
      have h := hchord ta tb (by rw [habs]; exact hWδ)
      rwa [habs] at h
    have h2 : 0 < (m / 2) * w := mul_pos (by linarith) hW0
    rw [norm_sub_rev] at h1
    linarith
  have hAB : r ta ≠ r tb := by
    intro h
    rw [h, sub_self, norm_zero] at hLpos
    exact lt_irrefl _ hLpos
  have hpow : 0 < m ^ 2 - M * (C * w) := by
    have hpos : 0 < 2 * M * C := by positivity
    have hw2 : w * (2 * M * C) < m ^ 2 := (lt_div_iff₀ hpos).mp hsmall
    nlinarith [hw2, hW0]
  have hpos_inner : ∀ t ∈ Set.Icc ta tb, 0 < inner ℝ (velocity r t) u := by
    intro t ht
    have hcont : ContinuousOn (fun s : ℝ => inner ℝ (velocity r t) (r s)) (Set.Icc ta tb) :=
      continuous_const.continuousOn.inner
        ((hr.smooth.continuous.comp continuous_id).continuousOn)
    have hdiff : DifferentiableOn ℝ (fun s : ℝ => inner ℝ (velocity r t) (r s)) (Set.Ioo ta tb) := by
      intro s _
      exact ((differentiableAt_const (c := velocity r t) (x := s)).inner (𝕜 := ℝ)
        ((hr.smooth.differentiable (by simp)).differentiableAt)).differentiableWithinAt
    obtain ⟨s₀, hs₀, hs₀eq⟩ :=
      exists_deriv_eq_slope (fun s : ℝ => inner ℝ (velocity r t) (r s)) hlt hcont hdiff
    have hderiv : deriv (fun s : ℝ => inner ℝ (velocity r t) (r s)) s₀
        = inner ℝ (velocity r t) (velocity r s₀) := by
      have h := deriv_inner_apply (𝕜 := ℝ) (f := fun _ : ℝ => velocity r t) (g := r)
        (x := s₀) (differentiableAt_const (c := velocity r t) (x := s₀))
        (((hr.smooth.differentiable (by simp)).differentiableAt :
          DifferentiableAt ℝ r s₀))
      simpa [velocity] using h
    have hslope : inner ℝ (velocity r t) (r tb) - inner ℝ (velocity r t) (r ta)
        = (tb - ta) * inner ℝ (velocity r t) (velocity r s₀) := by
      have h2 := hs₀eq
      rw [hderiv] at h2
      have hne : (tb - ta) ≠ 0 := ne_of_gt (by linarith)
      rw [eq_div_iff hne] at h2
      rw [mul_comm (tb - ta) (inner ℝ (velocity r t) (velocity r s₀))]
      exact h2.symm
    have hlaw : ‖r tb - r ta‖ * inner ℝ (velocity r t) u
        = w * inner ℝ (velocity r t) (velocity r s₀) := by
      have h1 : inner ℝ (velocity r t) (r tb - r ta)
          = ‖r tb - r ta‖ * inner ℝ (velocity r t) u := by
        have h0 : r tb - r ta = ‖r tb - r ta‖ • u := (chordDir_smul (r ta) (r tb) hAB).symm
        conv_lhs => rw [h0]
        rw [inner_smul_right]
      have h2 : inner ℝ (velocity r t) (r tb - r ta)
          = (tb - ta) * inner ℝ (velocity r t) (velocity r s₀) := by
        rw [inner_sub_right, hslope]
      rw [← h1, h2, hwtb]
    have hsdist : |s₀ - t| ≤ w := by
      rw [abs_le]
      constructor
      · rw [hwtb]; linarith [hs₀.1, ht.1, ht.2]
      · rw [hwtb]; linarith [hs₀.2, ht.1, ht.2]
    have hvel : m ^ 2 - M * (C * w) ≤ inner ℝ (velocity r t) (velocity r s₀) := by
      have hsplit : inner ℝ (velocity r t) (velocity r s₀)
          = ‖velocity r t‖ ^ 2 - inner ℝ (velocity r t) (velocity r t - velocity r s₀) := by
        have h1 : velocity r s₀ = velocity r t - (velocity r t - velocity r s₀) := by abel
        conv_lhs => rw [h1]
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      rw [hsplit]
      have hb1 : inner ℝ (velocity r t) (velocity r t - velocity r s₀) ≤ M * (C * w) := by
        have h4 := abs_real_inner_le_norm (velocity r t) (velocity r t - velocity r s₀)
        have h5 : inner ℝ (velocity r t) (velocity r t - velocity r s₀)
            ≤ ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖ := le_trans (le_abs_self _) h4
        have h6 : ‖velocity r t - velocity r s₀‖ ≤ C * w := by
          calc ‖velocity r t - velocity r s₀‖ ≤ C * |s₀ - t| := hlip t s₀
            _ ≤ C * w := by gcongr
        calc inner ℝ (velocity r t) (velocity r t - velocity r s₀)
            ≤ ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖ := h5
          _ ≤ M * (C * w) := by
              have h7 : ‖velocity r t‖ * ‖velocity r t - velocity r s₀‖
                  ≤ M * ‖velocity r t - velocity r s₀‖ :=
                mul_le_mul_of_nonneg_right (hmax t) (norm_nonneg _)
              have h8 : M * ‖velocity r t - velocity r s₀‖ ≤ M * (C * w) :=
                mul_le_mul_of_nonneg_left h6 hM.le
              linarith
      have hspd : m ^ 2 ≤ ‖velocity r t‖ ^ 2 := by nlinarith [hmin t, hm]
      linarith
    have hprod : 0 < ‖r tb - r ta‖ * inner ℝ (velocity r t) u := by
      rw [hlaw]
      exact mul_pos hW0 (lt_of_lt_of_le hpow hvel)
    rw [mul_comm (‖r tb - r ta‖) (inner ℝ (velocity r t) u)] at hprod
    exact pos_of_mul_pos_left hprod (norm_nonneg _)
  have hcont : ContinuousOn (arcCoord r D τ) (Set.Icc (0 : ℝ) 1) := by
    have h1 : Continuous (fun ξ : ℝ => r (D.ta τ + ξ * sweepW D τ)) :=
      hr.smooth.continuous.comp (by fun_prop)
    have h2 : Continuous (fun ξ : ℝ =>
        inner ℝ (r (D.ta τ + ξ * sweepW D τ) - r (D.ta τ))
          (chordDir (r (D.ta τ)) (r (D.tb τ)))) :=
      (h1.sub continuous_const).inner continuous_const
    exact h2.continuousOn
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont ?_
  intro ξ hξ
  rw [interior_Icc] at hξ
  rw [deriv_arcCoord hr D τ ξ]
  have hmem : D.ta τ + ξ * sweepW D τ ∈ Set.Icc (D.ta τ) (D.tb τ) := by
    constructor
    · have h1 : sweepW D τ = D.tb τ - D.ta τ := rfl
      rw [h1]; nlinarith [hξ.1, hW0, h1]
    · have h1 : sweepW D τ = D.tb τ - D.ta τ := rfl
      rw [h1]; nlinarith [hξ.2, hW0, h1]
  exact mul_pos hW0 (hpos_inner _ (by simpa [hta, htb] using hmem))

/-- The two local bounds of `Work.Drive.exists_curve_bounds`, proved here (via the uniform family
bounds `Work.Drive.uniformBoundsC1`) so that this module does not depend on the in-flux
`sweepToNeedleFamily`. -/
private theorem exists_curve_bounds_local {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ (∀ t : ℝ, m ≤ ‖velocity r t‖) ∧
      (∀ t t' : ℝ, |t' - t| ≤ δ → (m / 2) * |t' - t| ≤ ‖r t - r t'‖) := by
  have hF : ContDiff ℝ 1 (fam (fun t (_ : ℝ) => r t)) := by
    have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => r p.1) :=
      ((hr.smooth.of_le le_top).of_le (WithTop.coe_le_coe.mpr le_top)).comp contDiff_fst
    exact h1
  have hsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => (fun t (_ : ℝ) => r t) t s) :=
    fun s _ => IsSmoothKnot.toCInf hr
  obtain ⟨m, δ, sep, hm, hδ, -, hsep, hb⟩ := uniformBoundsC1 hF hsl
  exact ⟨m, δ, hm, hδ, (hb 0 (by norm_num)).1, (hb 0 (by norm_num)).2.1⟩

/-- **A short retained arc is a graph over its chord.**  There is a threshold `w₀ > 0`, depending
only on the knot, such that the chord coordinate of the retained arc is strictly increasing
whenever `0 < sweepW D τ ≤ w₀`. -/
theorem exists_arcCoord_strictMono {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ {d : BandArcData} (D : SweepData d) (τ : I),
      0 < sweepW D τ → sweepW D τ ≤ w₀ →
      StrictMonoOn (arcCoord r D τ) (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨m₁, M, C, hm₁, hM, hC, hmin₁, hmax, hlip⟩ := exists_knot_c2_bounds hr
  obtain ⟨m₂, δ, hm₂, hδ, hmin₂, hchord₂⟩ := exists_curve_bounds_local hr
  set mm : ℝ := min m₁ m₂ with hmm
  have hmmpos : 0 < mm := lt_min hm₁ hm₂
  have hMC : 0 < 2 * M * C := by positivity
  refine ⟨min δ (mm ^ 2 / (2 * M * C)) / 2, by positivity, ?_⟩
  intro d D τ hW0 hW
  have hwδ : sweepW D τ ≤ δ := by
    have h1 : min δ (mm ^ 2 / (2 * M * C)) / 2 ≤ δ := by
      have h2 : min δ (mm ^ 2 / (2 * M * C)) ≤ δ := min_le_left _ _
      linarith
    exact le_trans hW h1
  have hwsmall : sweepW D τ < mm ^ 2 / (2 * M * C) := by
    have h1 : min δ (mm ^ 2 / (2 * M * C)) / 2 < mm ^ 2 / (2 * M * C) := by
      have h2 : min δ (mm ^ 2 / (2 * M * C)) ≤ mm ^ 2 / (2 * M * C) := min_le_right _ _
      linarith
    exact lt_of_le_of_lt hW h1
  refine arcCoord_strictMono hr D τ hmmpos hM hC ?_ ?_ hmax hlip hW0 hwδ ?_
  · intro t
    exact le_trans (min_le_left _ _) (hmin₁ t)
  · intro t t' ht
    have h1 : (m₂ / 2) * |t' - t| ≤ ‖r t - r t'‖ := hchord₂ t t' ht
    have h2 : (mm / 2) * |t' - t| ≤ (m₂ / 2) * |t' - t| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have h3 : mm ≤ m₂ := min_le_right _ _
      linarith
    linarith
  · exact hwsmall

/-- **The transverse part of a short retained arc never vanishes in the interior.**  If the arc
avoids the chord (the `O`-avoidance hypothesis) and its chord coordinate is strictly increasing,
then no interior point of the arc lies on the chord's line. -/
theorem arcPerp_ne_zero {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r)
    {τ : Set.Icc (0 : ℝ) 1} (hτ0 : (τ : ℝ) ≠ 0) (hτ1 : (τ : ℝ) ≠ 1)
    (hmono : StrictMonoOn (arcCoord r D τ) (Set.Icc (0 : ℝ) 1))
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    arcPerp r D τ ξ ≠ 0 := by
  have hAB : r (D.ta τ) ≠ r (D.tb τ) := sweepChord_endpoints_ne hr D hτ0 hτ1
  have h0val : arcCoord r D τ 0 = 0 := by
    rw [arcCoord, sweepArc_zero, chordCoord_self]
  have h1val : arcCoord r D τ 1 = ‖r (D.tb τ) - r (D.ta τ)‖ := by
    rw [arcCoord, sweepArc_one, chordCoord_other _ _ hAB]
  have hx0 : 0 < arcCoord r D τ ξ := by
    have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
      (Set.mem_Icc.mpr ⟨hξ.1.le, hξ.2.le⟩) hξ.1
    rwa [h0val] at h
  have hx1 : arcCoord r D τ ξ < ‖r (D.tb τ) - r (D.ta τ)‖ := by
    have h := hmono (Set.mem_Icc.mpr ⟨hξ.1.le, hξ.2.le⟩)
      (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) hξ.2
    rwa [h1val] at h
  intro hperp
  have hmem : sweepArc r D τ ξ ∈ openSegment ℝ (r (D.ta τ)) (r (D.tb τ)) :=
    mem_openSegment_of_chordPerp_eq_zero hAB hx0 hx1 hperp
  rw [openSegment_eq_image] at hmem
  obtain ⟨η, hη, hηeq⟩ := hmem
  exact sweepArc_ne_sweepChord hr D havoid hτ0 hτ1
    (Set.mem_Icc.mpr ⟨hξ.1.le, hξ.2.le⟩) hη (by rw [sweepChord]; exact hηeq.symm)

end Work.Drive
