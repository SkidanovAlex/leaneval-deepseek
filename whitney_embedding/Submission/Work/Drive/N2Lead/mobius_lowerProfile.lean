import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology

noncomputable section

/-!
# The polar radial profile of the Möbius saddle packet

This file constructs, by an explicit formula, the planar radial profile `r` demanded by
`Work.Drive.N2Lead.mobius_lowerProfile` (the corrected form of §4 `D2d.4` of
`NOTES_LEAD_mobiusSaddle.md`; see §1 of `NOTES_H8_mobiusNote_gap_and_relaxedCrossRow.md`).

The profile is a function of `c = cos (2 φ)` alone, which makes it automatically `π`-periodic and
even in `φ`.  On the arcs it is the hyperbola branch `c ↦ √(η / (-c))`; on the bridges it is blended
to the outer radius `R` by the smooth transition
`q c = (1 - τ c) * (-c) + τ c * (η / R²)`, `τ c = smoothTransition ((c - c₁) / (c₂ - c₁))`,
where `c₁ = cos (2 φE) = -η/√(η²+m²)` and `c₂ = -η/R²`.
-/

noncomputable def leadProfileC1 (η m : ℝ) : ℝ := -η / Real.sqrt (η ^ 2 + m ^ 2)

/-- The right end `-η / R²` of the transition zone of the radial profile. -/
noncomputable def leadProfileC2 (η R : ℝ) : ℝ := -η / R ^ 2

/-- The smooth transition of the radial profile. -/
noncomputable def leadProfileTau (η m R : ℝ) (c : ℝ) : ℝ :=
  Real.smoothTransition ((c - leadProfileC1 η m) / (leadProfileC2 η R - leadProfileC1 η m))

/-- The quantity `r² = η / q` of the radial profile, as a function of `c = cos (2 φ)`. -/
noncomputable def leadProfileQ (η m R : ℝ) (c : ℝ) : ℝ :=
  (1 - leadProfileTau η m R c) * (-c) + leadProfileTau η m R c * (η / R ^ 2)

/-- The radial profile as a function of `c = cos (2 φ)`. -/
noncomputable def leadProfileF (η m R : ℝ) (c : ℝ) : ℝ :=
  Real.sqrt (η / leadProfileQ η m R c)

/-- **The polar radial profile** `φ ↦ r φ` of `mobius_lowerProfile`. -/
noncomputable def leadProfileR (η m R : ℝ) (φ : ℝ) : ℝ :=
  leadProfileF η m R (Real.cos (2 * φ))

/-! ## The analytic core: `cos (2 φE) = -η / √(η² + m²)` -/

/-- **The analytic core of the profile.** For the endpoint `E₁ = √(-η + i m)` (`η, m > 0`):
`cos (2 φE) = -η/√(η²+m²)`, and `φE` lies in the first quadrant. -/
theorem leadProfile_phiE {η m : ℝ} (hη : 0 < η) (hm : 0 < m) :
    Real.cos (2 * mobiusPhiE η m) = leadProfileC1 η m ∧
      0 < mobiusPhiE η m ∧ mobiusPhiE η m < Real.pi / 2 := by
  set z : ℂ := (-η : ℂ) + (m : ℂ) * Complex.I with hz
  set ζ : ℂ := Complex.sqrt z with hζ
  have hzre : z.re = -η := by simp [z]
  have hzim : z.im = m := by simp [z]
  have hznorm : ‖z‖ = Real.sqrt (η ^ 2 + m ^ 2) := by
    have h : ‖z‖ ^ 2 = η ^ 2 + m ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]; ring
    rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg z)]
    exact h.symm
  have hzge : η < ‖z‖ := by
    have h2 : (η : ℝ) ^ 2 + m ^ 2 = ‖z‖ ^ 2 := by
      rw [hznorm, Real.sq_sqrt (by positivity)]
    nlinarith [norm_nonneg z, hη.le, hm]
  have hζre : ζ.re = Real.sqrt ((‖z‖ - η) / 2) := by
    rw [hζ, Complex.sqrt, Complex.cpow_inv_two_re, hzre]; ring_nf
  have hζim : ζ.im = Real.sqrt ((‖z‖ + η) / 2) := by
    rw [hζ, Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt (by rw [hzim]; exact hm.le), hzre]
    ring_nf
  have hζresq : ζ.re ^ 2 = (‖z‖ - η) / 2 := by
    rw [hζre, Real.sq_sqrt (by linarith)]
  have hζimsq : ζ.im ^ 2 = (‖z‖ + η) / 2 := by
    rw [hζim, Real.sq_sqrt (by linarith)]
  have hnormζ : ‖ζ‖ ^ 2 = ‖z‖ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [hζresq, hζimsq]
  have hζpos : 0 < ζ.re := by rw [hζre, Real.sqrt_pos]; linarith
  have hζimpos : 0 < ζ.im := by rw [hζim, Real.sqrt_pos]; linarith
  have hζne : ζ ≠ 0 := fun h => by
    have : ζ.re = 0 := by rw [h]; rfl
    linarith [hζpos]
  have hζn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.mpr hζne
  have hcos : Real.cos ζ.arg = ζ.re / ‖ζ‖ := Complex.cos_arg hζne
  have hnum : 2 * ζ.re ^ 2 - ‖ζ‖ ^ 2 = -η := by nlinarith [hζresq, hnormζ]
  have hid : 2 * (ζ.re / ‖ζ‖) ^ 2 - 1 = (2 * ζ.re ^ 2 - ‖ζ‖ ^ 2) / ‖ζ‖ ^ 2 := by
    field_simp
  have hphi : mobiusPhiE η m = ζ.arg := by
    simp only [mobiusPhiE, hζ, hz]
  have hcos2 : Real.cos (2 * mobiusPhiE η m) = -η / ‖z‖ := by
    rw [hphi, Real.cos_two_mul, hcos, hid, hnum, hnormζ]
  have hC1 : leadProfileC1 η m = -η / ‖z‖ := by rw [leadProfileC1, hznorm]
  refine ⟨by rw [hcos2, hC1], ?_, ?_⟩
  · rw [hphi]
    have h0 : 0 ≤ ζ.arg := Complex.arg_nonneg_iff.mpr hζimpos.le
    rcases lt_or_eq_of_le h0 with h | h
    · exact h
    · exfalso
      have hz0 : ζ.arg = 0 := h.symm
      rw [Complex.arg_eq_zero_iff] at hz0
      linarith [hz0.2, hζimpos]
  · rw [hphi]
    exact Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hζpos)

/-! ## The numeric facts of the transition zone -/

/-- `√(η²+m²) < R²` in the standing range of parameters. -/
theorem leadProfile_sqrt_lt {η m R : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hm : 1 < m)
    (hm2 : m ≤ 2) (hR : 2 ≤ R) : Real.sqrt (η ^ 2 + m ^ 2) < R ^ 2 := by
  have hm0 : 0 < m := by linarith
  have h1 : Real.sqrt (η ^ 2 + m ^ 2) < 3 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hη, hη', hm2, hm0]
  nlinarith

/-- The transition zone is non-degenerate: `c₁ < c₂`. -/
theorem leadProfileC1_lt_C2 {η m R : ℝ} (hη : 0 < η) (hA : Real.sqrt (η ^ 2 + m ^ 2) < R ^ 2) :
    leadProfileC1 η m < leadProfileC2 η R := by
  have hApos : 0 < Real.sqrt (η ^ 2 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hR2 : 0 < R ^ 2 := by
    by_contra h
    have h0 : R ^ 2 = 0 := le_antisymm (not_lt.mp h) (sq_nonneg R)
    linarith [hA, h0]
  have hC1 : leadProfileC1 η m = -(η / Real.sqrt (η ^ 2 + m ^ 2)) := by
    simp [leadProfileC1, neg_div]
  have hC2 : leadProfileC2 η R = -(η / R ^ 2) := by simp [leadProfileC2, neg_div]
  rw [hC1, hC2, neg_lt_neg_iff, div_lt_div_iff₀ hR2 hApos]
  nlinarith

/-! ## The transition `τ` -/

theorem leadProfileTau_mono {η m R : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    Monotone (leadProfileTau η m R) := by
  intro c d hcd
  simp only [leadProfileTau]
  apply Real.smoothTransition.monotone
  rw [div_le_div_iff_of_pos_right hL]
  linarith

theorem leadProfileTau_eq_zero {η m R c : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hc : c ≤ leadProfileC1 η m) : leadProfileTau η m R c = 0 := by
  simp only [leadProfileTau]
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le

theorem leadProfileTau_eq_one {η m R c : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hc : leadProfileC2 η R ≤ c) : leadProfileTau η m R c = 1 := by
  simp only [leadProfileTau]
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hL]
  linarith

theorem leadProfileTau_le_one (η m R c : ℝ) : leadProfileTau η m R c ≤ 1 := by
  simp only [leadProfileTau]; exact Real.smoothTransition.le_one _

theorem leadProfileTau_nonneg (η m R c : ℝ) : 0 ≤ leadProfileTau η m R c := by
  simp only [leadProfileTau]; exact Real.smoothTransition.nonneg _

/-! ## The function `q` -/

theorem leadProfileQ_eq_neg {η m R c : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hc : c ≤ leadProfileC1 η m) : leadProfileQ η m R c = -c := by
  have hτ : leadProfileTau η m R c = 0 := leadProfileTau_eq_zero hL hc
  simp only [leadProfileQ, hτ]; ring

theorem leadProfileQ_pos {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) : 0 < leadProfileQ η m R c := by
  have hm : 0 < η / R ^ 2 := by positivity
  by_cases hc : c ≤ leadProfileC2 η R
  · have hC2 : leadProfileC2 η R = -(η / R ^ 2) := by simp [leadProfileC2, neg_div]
    have h1 : η / R ^ 2 ≤ -c := by linarith [hc, hC2]
    have hτ1 : 0 ≤ 1 - leadProfileTau η m R c := by
      have := leadProfileTau_le_one η m R c; linarith
    have key : leadProfileQ η m R c
        = η / R ^ 2 + (1 - leadProfileTau η m R c) * (-c - η / R ^ 2) := by
      simp only [leadProfileQ]; ring
    rw [key]
    nlinarith [mul_nonneg hτ1 (by linarith : 0 ≤ -c - η / R ^ 2)]
  · have hc2 : leadProfileC2 η R ≤ c := (not_le.mp hc).le
    have hτ : leadProfileTau η m R c = 1 := leadProfileTau_eq_one hL hc2
    have key : leadProfileQ η m R c = η / R ^ 2 := by simp only [leadProfileQ, hτ]; ring
    rw [key]; positivity

theorem leadProfileQ_ge {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) : η / R ^ 2 ≤ leadProfileQ η m R c := by
  have hm : 0 < η / R ^ 2 := by positivity
  by_cases hc : c ≤ leadProfileC2 η R
  · have hC2 : leadProfileC2 η R = -(η / R ^ 2) := by simp [leadProfileC2, neg_div]
    have h1 : η / R ^ 2 ≤ -c := by linarith [hc, hC2]
    have hτ1 : 0 ≤ 1 - leadProfileTau η m R c := by
      have := leadProfileTau_le_one η m R c; linarith
    have key : leadProfileQ η m R c
        = η / R ^ 2 + (1 - leadProfileTau η m R c) * (-c - η / R ^ 2) := by
      simp only [leadProfileQ]; ring
    rw [key]
    nlinarith [mul_nonneg hτ1 (by linarith : 0 ≤ -c - η / R ^ 2)]
  · have hc2 : leadProfileC2 η R ≤ c := (not_le.mp hc).le
    have hτ : leadProfileTau η m R c = 1 := leadProfileTau_eq_one hL hc2
    have key : leadProfileQ η m R c = η / R ^ 2 := by simp only [leadProfileQ, hτ]; ring
    rw [key]

theorem leadProfileQ_le {η m R c : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hc : leadProfileC1 η m ≤ c) : leadProfileQ η m R c ≤ -leadProfileC1 η m := by
  have hC1 : leadProfileC1 η m = -(η / Real.sqrt (η ^ 2 + m ^ 2)) := by
    simp [leadProfileC1, neg_div]
  have hC2 : leadProfileC2 η R = -(η / R ^ 2) := by simp [leadProfileC2, neg_div]
  have hL' : 0 < -(η / R ^ 2) - leadProfileC1 η m := by linarith
  have h2 : η / R ^ 2 + leadProfileC1 η m ≤ 0 := by linarith
  have h1 : -c + leadProfileC1 η m ≤ 0 := by linarith
  have hτ1 : 0 ≤ 1 - leadProfileTau η m R c := by
    have := leadProfileTau_le_one η m R c; linarith
  have hτ2 : 0 ≤ leadProfileTau η m R c := leadProfileTau_nonneg η m R c
  have key : leadProfileQ η m R c = -leadProfileC1 η m
      + ((1 - leadProfileTau η m R c) * (-c + leadProfileC1 η m)
        + leadProfileTau η m R c * (η / R ^ 2 + leadProfileC1 η m)) := by
    simp only [leadProfileQ]; ring
  rw [key]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hτ1 h1, mul_nonpos_of_nonneg_of_nonpos hτ2 h2]

theorem leadProfileQ_antitone {η m R : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    Antitone (leadProfileQ η m R) := by
  intro c d hcd
  have hτ : leadProfileTau η m R c ≤ leadProfileTau η m R d := leadProfileTau_mono hL hcd
  have hτ1 : 0 ≤ 1 - leadProfileTau η m R d := by
    have := leadProfileTau_le_one η m R d; linarith
  have key : leadProfileQ η m R c - leadProfileQ η m R d
      = (1 - leadProfileTau η m R d) * (d - c)
        + (leadProfileTau η m R d - leadProfileTau η m R c) * (-c - η / R ^ 2) := by
    simp only [leadProfileQ]; ring
  have h1 : 0 ≤ (1 - leadProfileTau η m R d) * (d - c) := mul_nonneg hτ1 (by linarith)
  have h2 : 0 ≤ (leadProfileTau η m R d - leadProfileTau η m R c) * (-c - η / R ^ 2) := by
    by_cases hc : c ≤ leadProfileC2 η R
    · have hC2 : leadProfileC2 η R = -(η / R ^ 2) := by simp [leadProfileC2, neg_div]
      exact mul_nonneg (by linarith) (by linarith [hc, hC2])
    · have hc2 : leadProfileC2 η R ≤ c := (not_le.mp hc).le
      have hA : leadProfileTau η m R c = 1 := leadProfileTau_eq_one hL hc2
      have hB : leadProfileTau η m R d = 1 :=
        leadProfileTau_eq_one hL (le_trans hc2 hcd)
      rw [hB, hA]; simp
  linarith [key, h1, h2]

/-! ## The function `F` -/

theorem leadProfileF_sq {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    leadProfileF η m R c ^ 2 = η / leadProfileQ η m R c := by
  rw [leadProfileF, Real.sq_sqrt (div_nonneg hη.le (leadProfileQ_pos hη hR hL).le)]

theorem leadProfileF_pos {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) : 0 < leadProfileF η m R c := by
  rw [leadProfileF, Real.sqrt_pos]
  exact div_pos hη (leadProfileQ_pos hη hR hL)

theorem leadProfileF_mono {η m R : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) : Monotone (leadProfileF η m R) := by
  intro c d hcd
  have h1 : leadProfileQ η m R d ≤ leadProfileQ η m R c := leadProfileQ_antitone hL hcd
  have h2 : η / leadProfileQ η m R c ≤ η / leadProfileQ η m R d := by
    rw [div_le_div_iff₀ (leadProfileQ_pos hη hR hL) (leadProfileQ_pos hη hR hL)]
    nlinarith [h1, hη]
  rw [leadProfileF]
  exact Real.sqrt_le_sqrt h2

theorem leadProfileF_le_R {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    leadProfileF η m R c ≤ R := by
  have hq := leadProfileQ_ge hη hR hL (c := c)
  have hqpos := leadProfileQ_pos hη hR hL (c := c)
  have hbound : η / leadProfileQ η m R c ≤ R ^ 2 := by
    rw [div_le_iff₀ hqpos]
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    calc η = R ^ 2 * (η / R ^ 2) := by field_simp
      _ ≤ R ^ 2 * leadProfileQ η m R c := mul_le_mul_of_nonneg_left hq hR2.le
  rw [leadProfileF]
  calc Real.sqrt (η / leadProfileQ η m R c) ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hbound
    _ = R := Real.sqrt_sq (by linarith)

theorem leadProfileF_ge {η m R c : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) (_hA2 : Real.sqrt (η ^ 2 + m ^ 2) ≤ R ^ 2)
    (hc : leadProfileC1 η m ≤ c) :
    Real.sqrt (η ^ 2 + m ^ 2) ≤ leadProfileF η m R c ^ 2 := by
  have hq := leadProfileQ_le hL hc
  have hqpos := leadProfileQ_pos hη hR hL (c := c)
  have hA2pos : 0 < Real.sqrt (η ^ 2 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hneg : -leadProfileC1 η m = η / Real.sqrt (η ^ 2 + m ^ 2) := by
    simp [leadProfileC1, neg_div]
  have hbound : Real.sqrt (η ^ 2 + m ^ 2) ≤ η / leadProfileQ η m R c := by
    rw [le_div_iff₀ hqpos]
    calc Real.sqrt (η ^ 2 + m ^ 2) * leadProfileQ η m R c
        ≤ Real.sqrt (η ^ 2 + m ^ 2) * (-leadProfileC1 η m) :=
          mul_le_mul_of_nonneg_left hq hA2pos.le
      _ = Real.sqrt (η ^ 2 + m ^ 2) * (η / Real.sqrt (η ^ 2 + m ^ 2)) := by rw [hneg]
      _ = η := by field_simp
  rw [leadProfileF_sq hη hR hL]
  exact hbound

/-! ## Smoothness -/

theorem leadProfileTau_contDiff {η m R : ℝ} (_hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (leadProfileTau η m R) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => (c - leadProfileC1 η m) / (leadProfileC2 η R - leadProfileC1 η m)) :=
    (contDiff_id.sub contDiff_const).div_const _
  exact Real.smoothTransition.contDiff.comp h1

theorem leadProfileQ_contDiff {η m R : ℝ} (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (leadProfileQ η m R) := by
  have hτ := leadProfileTau_contDiff hL
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => 1 - leadProfileTau η m R c) :=
    contDiff_const.sub hτ
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => -c) := contDiff_id.neg
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => η / R ^ 2) := contDiff_const
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => (1 - leadProfileTau η m R c) * (-c)) := h1.mul h2
  have h5 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c : ℝ => leadProfileTau η m R c * (η / R ^ 2)) := hτ.mul h3
  exact h4.add h5

theorem leadProfileF_contDiff {η m R : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (leadProfileF η m R) := by
  have hq := leadProfileQ_contDiff hL
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => η / leadProfileQ η m R c) :=
    ContDiff.div contDiff_const hq (fun c => (leadProfileQ_pos hη hR hL).ne')
  refine ContDiff.sqrt h1 (fun c => ?_)
  exact (div_pos hη (leadProfileQ_pos hη hR hL)).ne'

theorem leadProfileR_contDiff {η m R : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (leadProfileR η m R) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun φ : ℝ => Real.cos (2 * φ)) := by
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun φ : ℝ => (2 : ℝ) * φ) :=
      contDiff_const.mul contDiff_id
    exact h2.cos
  exact (leadProfileF_contDiff hη hR hL).comp h1

/-! ## The two angular comparisons -/

theorem leadProfile_cos_arc {η m : ℝ} (hcosE : Real.cos (2 * mobiusPhiE η m) = leadProfileC1 η m)
    (hE0 : 0 ≤ mobiusPhiE η m) :
    ∀ φ : ℝ, mobiusPhiE η m ≤ φ → φ ≤ Real.pi - mobiusPhiE η m →
      Real.cos (2 * φ) ≤ leadProfileC1 η m := by
  intro φ h1 h2
  have hsub := Real.cos_sub_cos (2 * φ) (2 * mobiusPhiE η m)
  rw [show (2 * φ + 2 * mobiusPhiE η m) / 2 = φ + mobiusPhiE η m by ring,
    show (2 * φ - 2 * mobiusPhiE η m) / 2 = φ - mobiusPhiE η m by ring] at hsub
  have hs1 : 0 ≤ Real.sin (φ + mobiusPhiE η m) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : 0 ≤ Real.sin (φ - mobiusPhiE η m) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hprod : 0 ≤ Real.sin (φ + mobiusPhiE η m) * Real.sin (φ - mobiusPhiE η m) :=
    mul_nonneg hs1 hs2
  have : Real.cos (2 * φ) ≤ Real.cos (2 * mobiusPhiE η m) := by nlinarith [hsub, hprod]
  rwa [hcosE] at this

theorem leadProfile_cos_bridge {η m : ℝ} (hcosE : Real.cos (2 * mobiusPhiE η m) = leadProfileC1 η m)
    (hE0 : 0 ≤ mobiusPhiE η m) (hEhalf : mobiusPhiE η m ≤ Real.pi / 2) :
    ∀ φ : ℝ, 0 ≤ φ → φ ≤ mobiusPhiE η m → leadProfileC1 η m ≤ Real.cos (2 * φ) := by
  intro φ h1 h2
  have hsub := Real.cos_sub_cos (2 * φ) (2 * mobiusPhiE η m)
  rw [show (2 * φ + 2 * mobiusPhiE η m) / 2 = φ + mobiusPhiE η m by ring,
    show (2 * φ - 2 * mobiusPhiE η m) / 2 = φ - mobiusPhiE η m by ring] at hsub
  have hs1 : 0 ≤ Real.sin (φ + mobiusPhiE η m) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs2 : Real.sin (φ - mobiusPhiE η m) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  have hprod : Real.sin (φ + mobiusPhiE η m) * Real.sin (φ - mobiusPhiE η m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs1 hs2
  have : leadProfileC1 η m ≤ Real.cos (2 * φ) := by
    rw [← hcosE]; nlinarith [hsub, hprod]
  exact this



open scoped Manifold ContDiff Topology in
/-- **The polar radial profile of the packet picture** (§4 `D2d.4` and §5.2 of
`Submission/Work/Drive/N2Lead/NOTES_LEAD_mobiusSaddle.md`; the corrected form is recorded in
`N2Lead/NOTES_H8_mobiusNote_gap_and_relaxedCrossRow.md` §1).  For the endpoint `E₁ = √(-η + i m)` of
the pinned top arc of the saddle anchor level (whose argument is `mobiusPhiE η m` and whose modulus
squared is `√(η² + m²)`), there is a smooth positive radial profile `r` of a planar polar curve
`φ ↦ r φ · e^{iφ}` which

* is `π`-periodic and even (so that the curve has the two-arc symmetry of the anchor level);
* realises the hyperbola branch `r² = -η / cos (2φ)`, i.e. `r φ = √(η / -cos (2φ))`, on the angular
  range `[φE, π - φE]` of the two model arcs;
* on the *bridge zone* `[0, φE]` (and hence, by the two symmetries, on every bridge zone) has
  `r φ ^ 2 ∈ [√(η² + m²), R²]` and is nonincreasing, so that the bridge leaves `E₁` and climbs
  monotonically to the outer radius `R` — the form of the profile that §2.2 of the note builds as
  `(1 - b) * √(η / -cos (2φ)) + b * R` with `b = smoothTransition ((φ_hi - d) / (φ_hi - φ_lo))`,
  `d φ = dist (φ, πℤ)`, `π/4 < φ_lo < φ_hi < φE` (note `φE ∈ (π/4, π/2)`, since
  `arg (-η + i m) ∈ (π/2, π)` and `φE` is half of it; the endpoint values agree:
  `η / (-cos (2 * φE)) = √(η² + m²)`).  The bridge lower bound is false on the arcs, where
  `r (π/2)² = η < √(η² + m²)`; the arcs are where the *model* provides the bound
  `‖cE3 (Ψ (Z ·))‖² < c₀ + 2η` instead. -/
theorem mobius_lowerProfile {η m R : ℝ} (hη : 0 < η) (hη' : η < 1 / 10) (hm : 1 < m) (hm2 : m ≤ 2)
    (hR : 2 ≤ R) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ φ : ℝ, 0 < r φ) ∧
      (∀ φ : ℝ, r (φ + Real.pi) = r φ) ∧ (∀ φ : ℝ, r (-φ) = r φ) ∧
      (∀ φ : ℝ, Work.Drive.N2Lead.mobiusPhiE η m ≤ φ →
        φ ≤ Real.pi - Work.Drive.N2Lead.mobiusPhiE η m →
        r φ = Real.sqrt (η / -Real.cos (2 * φ))) ∧
      (∀ φ ∈ Set.Icc 0 (Work.Drive.N2Lead.mobiusPhiE η m),
        Real.sqrt (η ^ 2 + m ^ 2) ≤ r φ ^ 2 ∧ r φ ^ 2 ≤ R ^ 2) ∧
      (∀ φ ∈ Set.Icc 0 (Work.Drive.N2Lead.mobiusPhiE η m), deriv r φ ≤ 0) := by
  have hm0 : 0 < m := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨hEcos, hEpos, hElt⟩ := leadProfile_phiE hη hm0
  have hA2 : Real.sqrt (η ^ 2 + m ^ 2) < R ^ 2 := leadProfile_sqrt_lt hη hη' hm hm2 hR
  have hC1C2 : leadProfileC1 η m < leadProfileC2 η R := leadProfileC1_lt_C2 hη hA2
  have hL : 0 < leadProfileC2 η R - leadProfileC1 η m := by linarith
  refine ⟨leadProfileR η m R, leadProfileR_contDiff hη hR0 hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    exact leadProfileF_pos hη hR0 hL
  · intro φ
    simp only [leadProfileR]
    have h : 2 * (φ + Real.pi) = 2 * φ + 2 * Real.pi := by ring
    rw [h, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
    ring_nf
  · intro φ
    simp only [leadProfileR]
    have h : 2 * (-φ) = -(2 * φ) := by ring
    rw [h, Real.cos_neg]
  · intro φ h1 h2
    have hle : Real.cos (2 * φ) ≤ leadProfileC1 η m :=
      leadProfile_cos_arc hEcos hEpos.le φ h1 h2
    have hτ : leadProfileTau η m R (Real.cos (2 * φ)) = 0 := leadProfileTau_eq_zero hL hle
    have hq : leadProfileQ η m R (Real.cos (2 * φ)) = -Real.cos (2 * φ) := by
      simp only [leadProfileQ, hτ]; ring
    simp only [leadProfileR, leadProfileF, hq]
  · intro φ hφ
    have hφ0 : 0 ≤ φ := hφ.1
    have hφ1 : φ ≤ mobiusPhiE η m := hφ.2
    have hgele : leadProfileC1 η m ≤ Real.cos (2 * φ) :=
      leadProfile_cos_bridge hEcos hEpos.le hElt.le φ hφ0 hφ1
    constructor
    · rw [leadProfileR]
      exact leadProfileF_ge hη hR0 hL hA2.le hgele
    · have hFle : leadProfileF η m R (Real.cos (2 * φ)) ≤ R := leadProfileF_le_R hη hR0 hL
      have hFpos : 0 < leadProfileF η m R (Real.cos (2 * φ)) := leadProfileF_pos hη hR0 hL
      rw [leadProfileR]
      nlinarith
  · intro φ hφ
    have hφ0 : 0 ≤ φ := hφ.1
    have hφ1 : φ ≤ mobiusPhiE η m := hφ.2
    have hsin : 0 ≤ Real.sin (2 * φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hFdiff : DifferentiableAt ℝ (leadProfileF η m R) (Real.cos (2 * φ)) :=
      ((leadProfileF_contDiff hη hR0 hL).differentiable (by simp)).differentiableAt
    have hderiv : deriv (leadProfileR η m R) φ
        = deriv (leadProfileF η m R) (Real.cos (2 * φ)) * (-Real.sin (2 * φ) * 2) := by
      have hc : HasDerivAt (fun ψ : ℝ => Real.cos (2 * ψ)) (-Real.sin (2 * φ) * 2) φ := by
        have h1 : HasDerivAt (fun ψ : ℝ => (2 : ℝ) * ψ) 2 φ := by
          simpa using (hasDerivAt_id (x := φ)).const_mul (2 : ℝ)
        exact h1.cos
      have h2 := (hFdiff.hasDerivAt).comp φ hc
      exact h2.deriv
    rw [hderiv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Monotone.deriv_nonneg (leadProfileF_mono hη hR0 hL)) (by linarith)
end

end Work.Drive.N2Lead
