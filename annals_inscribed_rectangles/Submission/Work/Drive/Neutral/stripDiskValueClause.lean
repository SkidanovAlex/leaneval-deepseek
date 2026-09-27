import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.StripDiskValues
import Submission.Work.Drive.Neutral.stripTauChart
import Submission.Work.Drive.Neutral.exists_contMDiff_planeCross
import Submission.Work.Drive.exists_contMDiffAt_stripChart_closed

/-!
# The value clause of the strip disk presentation

The disk presentation of the capped plane evaluates the chord data of `StripDiskAux` at the points of
the unit complex circle `x = e^{iσ}` with openings `s ∈ (0, π/2]`.  On that range the *clamping* of
the chord opening is inactive (`sClamp s = s`, `sKappa s = 1`, `muX k x = 1`), so the clamped data
`dataD, dataR, dataRboOf, dataVbOf` coincide with the symmetric chord data `symmD, symmR, symmWC` of
`stripTauData`, and the plane point `Work.Drive.planePt` of that data is the strip chart
`Work.Drive.stripChart` of the chord `(σ+s, σ-s)`.

This is the `value` half of `Work.Drive.exists_contMDiff_stripDiskPresentation`; the smoothness half
is `Work.Drive.exists_contMDiff_planeBand` / `Work.Drive.Neutral.exists_contMDiff_stripPlane`.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## Elementary reductions -/

/-- **The clamped disk coordinate at `x = e^{iσ}` is the symmetric one.**  For openings in
`(0, π/2]` the clamping is inactive, so the divided difference (hence the disk coordinate) of the
clamped clamped chord data is that of `symmD`. -/
lemma dataD_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    dataD γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmD γ σ s := by
  rw [dataD, dataMid_exp_eq γ σ s hs hs2, dataR_exp_eq γ σ s hs hs2, symmD, symmC_symmMid_eq]

/-- **The blend weight is one on the unit circle**: `muX k x = 1` for `‖x‖ = 1`, `k ≥ 1`. -/
lemma muX_exp_eq_one (k : ℕ) (hk : 1 ≤ k) (σ : ℝ) :
    muX k (Complex.exp ((σ : ℂ) * Complex.I)) = 1 := by
  have hns : Complex.normSq (Complex.exp ((σ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have hre : (((σ : ℂ) * Complex.I).re) = 0 := by simp
    rw [hre, Real.exp_zero]
    norm_num
  rw [muX, hns]
  refine Real.smoothTransition.one_of_one_le ?_
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

/-- **Normalisation is invariant under a positive real scaling**: `(c z)/‖c z‖ = z/‖z‖` for
`c > 0`. -/
lemma div_norm_ofReal_mul_const (c : ℝ) (hc : 0 < c) (z : ℂ) :
    ((c : ℂ) * z) / ((‖(c : ℂ) * z‖ : ℝ) : ℂ) = z / ((‖z‖ : ℝ) : ℂ) := by
  have hnorm : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [hnorm, Complex.ofReal_mul]
  exact mul_div_mul_left z ((‖z‖ : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hc))

/-- The clamped chord at `x = e^{iσ}` is `2 s` times the divided difference. -/
lemma dataChord_exp_eq_two_smul (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    dataChord γ (Complex.exp ((σ : ℂ) * Complex.I)) s
      = ((2 * s : ℝ) : ℂ) * symmWC γ σ s := by
  rw [dataChord_exp_eq γ σ s hs hs2, symmChordC_eq_smul_symmWC hγ σ s]

/-- **The unit normalisation of a halving of the chord is the unit normalisation of `symmWC`.** -/
lemma halving_div_norm_eq (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (W : ℂ × ℝ → ℂ) {σ s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2)
    (hch : dataChord γ (Complex.exp ((σ : ℂ) * Complex.I)) s
      = s • W (Complex.exp ((σ : ℂ) * Complex.I), s)) :
    W (Complex.exp ((σ : ℂ) * Complex.I), s)
        / ((‖W (Complex.exp ((σ : ℂ) * Complex.I), s)‖ : ℝ) : ℂ)
      = symmWC γ σ s / ((‖symmWC γ σ s‖ : ℝ) : ℂ) := by
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hWs : ((s : ℝ) : ℂ) * W (Complex.exp ((σ : ℂ) * Complex.I), s)
      = ((s : ℝ) : ℂ) * ((2 : ℂ) * symmWC γ σ s) := by
    rw [← Complex.real_smul, ← hch, dataChord_exp_eq_two_smul hγ σ s hs hs2]
    push_cast
    ring
  have hW : W (Complex.exp ((σ : ℂ) * Complex.I), s) = (2 : ℂ) * symmWC γ σ s :=
    mul_left_cancel₀ hsC hWs
  rw [hW]
  exact div_norm_ofReal_mul_const 2 (by norm_num) (symmWC γ σ s)

/-! ## The two blended clauses -/

/-- **The blended radius at `x = e^{iσ}` is the symmetric radius** (for `k ≥ 1`). -/
lemma dataRbOf_exp_eq (γ : Circle → ℝ × ℝ) (k : ℕ) (hk : 1 ≤ k) {σ s : ℝ} (hs : 0 < s)
    (hs2 : s ≤ Real.pi / 2) :
    dataRbOf γ k (Complex.exp ((σ : ℂ) * Complex.I)) s = symmR γ σ s := by
  rw [dataRbOf, muX_exp_eq_one k hk σ, dataR_exp_eq γ σ s hs hs2]
  ring

/-- **The blended physical vector at `x = e^{iσ}` is the projective class of the symmetric data**
(for `k ≥ 1`, any halving `W` of the clamped chord). -/
lemma dataVbOf_exp_eq (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (W : ℂ × ℝ → ℂ) (k : ℕ) (hk : 1 ≤ k) {σ s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2)
    (hch : dataChord γ (Complex.exp ((σ : ℂ) * Complex.I)) s
      = s • W (Complex.exp ((σ : ℂ) * Complex.I), s)) :
    dataVbOf γ k W (Complex.exp ((σ : ℂ) * Complex.I)) s
      = confProjVecOf (symmWC γ σ s / ((‖symmWC γ σ s‖ : ℝ) : ℂ)) (symmD γ σ s) := by
  rw [dataVbOf, muX_exp_eq_one k hk σ, dataVOf, dataD_exp_eq γ σ s hs hs2,
    halving_div_norm_eq hγ W hs hs2 hch]
  simp

/-! ## The value of the plane point -/

/-- **The plane point of the symmetric chord data is the strip chart.**  For `0 < s ≤ π/2` and the
unit halving `u = symmWC/‖symmWC‖` of the chord `(σ+s, σ-s)`, the plane point of the symmetric
capping data is the configuration class of that chord, i.e. `stripChart γ hγne 0` at the parameter
pair. -/
lemma planePt_symmD_eq_stripChart
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {σ s : ℝ} (hs : 0 < s) (hs2 : s ≤ Real.pi / 2)
    {u : ℂ} (hu : u = symmWC γ σ s / ((‖symmWC γ σ s‖ : ℝ) : ℂ))
    (hr : 0 < symmR γ σ s) (hu1 : ‖u‖ = 1)
    (hv : confProjVecOf u (symmD γ σ s) ≠ 0) :
    planePt u (symmR γ σ s) hr (symmD γ σ s) hu1 hv
      = stripChart γ hγne 0 (mk2 (σ + s) (σ - s)) := by
  have hd_le : ‖symmD γ σ s‖ ≤ 1 := symmD_norm_le_one γ σ s
  have hwc : symmWC γ σ s ≠ 0 := by
    intro h0
    have hzero : u = 0 := by rw [hu, h0, norm_zero, Complex.ofReal_zero, div_zero]
    rw [hzero, norm_zero] at hu1
    norm_num at hu1
  have hsne : s ≠ 0 := ne_of_gt hs
  have hne : Circle.exp (σ + s) ≠ Circle.exp (σ - s) :=
    circle_exp_add_ne_sub hs (by linarith [Real.pi_pos, hs2])
  have hchain : u ^ 2 = (stripHalf γ (mk2 (σ + s) (σ - s))) ^ 2 := by
    have h1 : u ^ 2 = symmE γ σ s := by
      rw [hu]
      exact (symmData_norm_identities' hγ σ s).2.2
    have h2 : symmE γ σ s = (chordUnitDir γ (σ + s, σ - s)) ^ 2 :=
      symmE_eq_chordUnitDir_sq hγ σ s hsne hwc
    have h3 : stripHalf γ (mk2 (σ + s) (σ - s)) = chordUnitDir γ (σ + s, σ - s) := by
      have h4 := stripHalf_of_ne (γ := γ) (w := mk2 (σ + s) (σ - s)) hne
      rwa [mk2_apply_zero, mk2_apply_one] at h4
    rw [h1, h2, h3]
  have htriple : (symmR γ σ s, symmD γ σ s, circOf (u ^ 2) (by rw [norm_pow, hu1]; norm_num))
      = ((stripData γ (mk2 (σ + s) (σ - s))).1, (stripData γ (mk2 (σ + s) (σ - s))).2.1,
          (stripData γ (mk2 (σ + s) (σ - s))).2.2 + 0) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · rw [symmR_eq_stripR, stripData_fst]
    · rw [symmD_eq_stripD, stripData_snd]
    · rw [add_zero, ← circOf_stripHalf_sq hγ (mk2 (σ + s) (σ - s))]
      exact circOf_congr (by rw [norm_pow, hu1]; norm_num)
        (by rw [norm_pow, stripHalf_norm hγ (mk2 (σ + s) (σ - s))]; norm_num) hchain
  rw [← planePt_congr_hv hr hu1 hv (confProjVecOf_ne_zero hu1 hd_le),
    planePt_eq_confPiece hr hd_le hu1, stripChart_eq_mk]
  exact Quotient.sound (Or.inl (congrArg Sum.inl (Subtype.ext htriple)))

/-! ## The clause -/

theorem stripDiskValueClause (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    (∀ σ s : ℝ, ‖Work.Drive.Neutral.symmD γ σ s‖ ≤ 1) ∧
    (∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 →
        Work.Drive.Neutral.dataD γ (Complex.exp ((σ : ℂ) * Complex.I)) s = Work.Drive.Neutral.symmD γ σ s) ∧
    (∀ (W : ℂ × ℝ → ℂ) (k : ℕ), 1 ≤ k →
        (∀ x s, x ≠ 0 → Work.Drive.Neutral.dataChord γ x s = s • W (x, s)) →
        (∀ x s, x ≠ 0 → W (x, s) ≠ 0) →
        ∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 →
          Work.Drive.Neutral.dataRbOf γ k (Complex.exp ((σ : ℂ) * Complex.I)) s = Work.Drive.Neutral.symmR γ σ s ∧
          Work.Drive.Neutral.dataVbOf γ k W (Complex.exp ((σ : ℂ) * Complex.I)) s
            = Work.Drive.confProjVecOf
                (Work.Drive.Neutral.symmWC γ σ s / ((‖Work.Drive.Neutral.symmWC γ σ s‖ : ℝ) : ℂ))
                (Work.Drive.Neutral.symmD γ σ s)) ∧
    (∀ σ s : ℝ, 0 < s → s ≤ Real.pi / 2 → ∀ u : ℂ,
        u = Work.Drive.Neutral.symmWC γ σ s / ((‖Work.Drive.Neutral.symmWC γ σ s‖ : ℝ) : ℂ) →
        ∀ (hr : 0 < Work.Drive.Neutral.symmR γ σ s) (hu1 : ‖u‖ = 1)
          (hv : Work.Drive.confProjVecOf u (Work.Drive.Neutral.symmD γ σ s) ≠ 0),
          Work.Drive.planePt u (Work.Drive.Neutral.symmR γ σ s) hr (Work.Drive.Neutral.symmD γ σ s) hu1 hv
            = Work.Drive.stripChart γ hγne 0 (Work.Drive.mk2 (σ + s) (σ - s))) := by
  refine ⟨fun σ s => symmD_norm_le_one γ σ s, fun σ s hs hs2 => dataD_exp_eq γ σ s hs hs2, ?_, ?_⟩
  · intro W k hk hch _ σ s hs hs2
    exact ⟨dataRbOf_exp_eq γ k hk hs hs2, dataVbOf_exp_eq hγ W k hk hs hs2 (hch _ _ (Complex.exp_ne_zero _))⟩
  · intro σ s hs hs2 u hu hr hu1 hv
    exact planePt_symmD_eq_stripChart hγ hγne hs hs2 hu hr hu1 hv

end

end Work.Drive.Neutral
