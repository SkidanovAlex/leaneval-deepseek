import Mathlib
import Submission.Work.Drive.N2Lead.mobius_lowerProfile
import Submission.Work.Drive.N2Lead.mobiusGeomDefs

namespace Work.Drive.N2Lead

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-! ## The arctan parametrisation of the two model arcs

The upper arc angle of the profile is `φU w = π/2 - (1/2) arctan (w/η)` and the lower one is
`φL w = -(π/2) - (1/2) arctan (w/η) = φU w - π`.  The endpoint of the arc range is
`φE = mobiusPhiE η m = φU m`, and for `|w| ≤ m` the upper angle lies in `[φE, π - φE]`. -/

/-- `cos (arctan (b/a)) = a / √(a² + b²)` for `a > 0`. -/
lemma cos_arctan_div_aux {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.cos (Real.arctan (b / a)) = a / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hS : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [Real.cos_arctan]
  have h1 : (1 : ℝ) + (b / a) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 := by field_simp
  have h2 : Real.sqrt (1 + (b / a) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / a := by
    rw [h1, Real.sqrt_div (show (0 : ℝ) ≤ a ^ 2 + b ^ 2 by positivity), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  rw [h2]; field_simp

/-- `cos (2 * (π/2 - (1/2) * arctan (w/η))) = -η/√(η²+w²)`. -/
lemma cos_two_phiU {η : ℝ} (hη : 0 < η) (w : ℝ) :
    Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / η)))
      = -η / Real.sqrt (η ^ 2 + w ^ 2) := by
  have h2 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / η))
      = Real.pi - Real.arctan (w / η) := by ring
  rw [h2, Real.cos_pi_sub, cos_arctan_div_aux hη w]
  ring

/-- **The arc-range check.**  For `|w| ≤ m` the upper arc angle `π/2 - (1/2) arctan (w/η)` lies in
the arc range `[φE, π - φE]` of the profile, where `φE = mobiusPhiE η m`. -/
lemma phiU_mem_arcRange {η m : ℝ} (hη : 0 < η) (hm : 0 < m) {w : ℝ}
    (hw : w ∈ Set.Icc (-m) m) :
    mobiusPhiE η m ≤ Real.pi / 2 - (1 / 2) * Real.arctan (w / η) ∧
      Real.pi / 2 - (1 / 2) * Real.arctan (w / η) ≤ Real.pi - mobiusPhiE η m := by
  obtain ⟨hEcos, hEpos, hElt⟩ := leadProfile_phiE hη hm
  have hanti : Antitone (fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η)) := by
    intro a b hab
    have h1 : a / η ≤ b / η := div_le_div_of_nonneg_right hab hη.le
    have h2 : Real.arctan (a / η) ≤ Real.arctan (b / η) := Real.arctan_mono h1
    show Real.pi / 2 - (1 / 2) * Real.arctan (b / η)
      ≤ Real.pi / 2 - (1 / 2) * Real.arctan (a / η)
    linarith
  have htpos : 0 < Real.arctan (m / η) := Real.arctan_pos.mpr (div_pos hm hη)
  have htlt : Real.arctan (m / η) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hfm : Real.pi / 2 - (1 / 2) * Real.arctan (m / η) = mobiusPhiE η m := by
    have hcos : Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (m / η)))
        = Real.cos (2 * mobiusPhiE η m) := by
      rw [hEcos, cos_two_phiU hη m]
      rfl
    have h1 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (m / η)) ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [htpos, htlt, Real.pi_pos]
    have h2 : 2 * mobiusPhiE η m ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [hEpos, hElt, Real.pi_pos]
    have hinj := Real.strictAntiOn_cos.injOn h1 h2 hcos
    linarith
  have hfnm : Real.pi / 2 - (1 / 2) * Real.arctan ((-m) / η)
      = Real.pi - mobiusPhiE η m := by
    have harm : Real.arctan ((-m) / η) = -Real.arctan (m / η) := by
      rw [show (-m) / η = -(m / η) by ring, Real.arctan_neg]
    rw [harm, ← hfm]
    ring
  exact ⟨le_trans hfm.ge (hanti hw.2), le_trans (hanti hw.1) hfnm.le⟩

/-! ## Rows of the explicit profile `leadProfileR` -/

/-- On the arc range the profile is the hyperbola branch `√(η / -cos (2φ))`. -/
lemma leadProfileR_arc {η m R : ℝ}
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hcosE : Real.cos (2 * mobiusPhiE η m) = leadProfileC1 η m) (hE0 : 0 ≤ mobiusPhiE η m)
    {φ : ℝ} (h1 : mobiusPhiE η m ≤ φ) (h2 : φ ≤ Real.pi - mobiusPhiE η m) :
    leadProfileR η m R φ = Real.sqrt (η / -Real.cos (2 * φ)) := by
  have hle : Real.cos (2 * φ) ≤ leadProfileC1 η m := leadProfile_cos_arc hcosE hE0 φ h1 h2
  have hτ : leadProfileTau η m R (Real.cos (2 * φ)) = 0 := leadProfileTau_eq_zero hL hle
  have hq : leadProfileQ η m R (Real.cos (2 * φ)) = -Real.cos (2 * φ) := by
    simp only [leadProfileQ, hτ]; ring
  simp only [leadProfileR, leadProfileF, hq]

/-- `leadProfileR` is `π`-periodic. -/
lemma leadProfileR_periodic_pi (η m R : ℝ) :
    Function.Periodic (leadProfileR η m R) Real.pi := by
  intro φ
  simp only [leadProfileR]
  rw [show 2 * (φ + Real.pi) = 2 * φ + 2 * Real.pi by ring, Real.cos_add_two_pi]

/-- `leadProfileR` is even. -/
lemma leadProfileR_even (η m R : ℝ) (φ : ℝ) :
    leadProfileR η m R (-φ) = leadProfileR η m R φ := by
  simp only [leadProfileR]
  rw [show 2 * (-φ) = -(2 * φ) by ring, Real.cos_neg]

/-- The bridge lower bound of the profile on the bridge zone. -/
lemma leadProfileR_bridge {η m R : ℝ} (hη : 0 < η) (hR : 0 < R)
    (hL : 0 < leadProfileC2 η R - leadProfileC1 η m)
    (hA2 : Real.sqrt (η ^ 2 + m ^ 2) ≤ R ^ 2)
    (hcosE : Real.cos (2 * mobiusPhiE η m) = leadProfileC1 η m) (hE0 : 0 ≤ mobiusPhiE η m)
    (hEhalf : mobiusPhiE η m ≤ Real.pi / 2) {φ : ℝ} (hφ : |φ| ≤ mobiusPhiE η m) :
    Real.sqrt (η ^ 2 + m ^ 2) ≤ leadProfileR η m R φ ^ 2 := by
  have hc : leadProfileC1 η m ≤ Real.cos (2 * |φ|) :=
    leadProfile_cos_bridge hcosE hE0 hEhalf |φ| (abs_nonneg φ) hφ
  have hb := leadProfileF_ge hη hR hL hA2 hc
  have hcos : Real.cos (2 * φ) = Real.cos (2 * |φ|) := by
    rcases abs_choice φ with h | h
    · rw [h]
    · rw [h, show 2 * (-φ) = -(2 * φ) by ring, Real.cos_neg]
  rw [show leadProfileR η m R φ ^ 2 = leadProfileF η m R (Real.cos (2 * |φ|)) ^ 2 by
    simp only [leadProfileR, hcos]]
  exact hb

end

open scoped ContDiff Topology in
open Set Filter in
/-- **The radial-profile rows the saddle packet consumes**, in the exact shape of the hypotheses
`hr`, `hrpos`, `hrper`, `hrR`, `hrArcU`, `hrArcL` of `Work.Drive.N2Lead.saddlePacketRows`, plus the
bridge bound off the arc ranges.  The profile is `Work.Drive.N2Lead.mobius_lowerProfile`'s `r`
(positive, `C^∞`, `π`-periodic and even, equal to the hyperbola branch `√(η / -cos (2φ))` on the arc
range `[φE, π - φE]`, and with `√(η² + m²) ≤ r φ ^ 2 ≤ R²` on the bridge zone
`dist (φ, πℤ) ≤ φE`).

The three derived rows are: `2π`-periodicity (from `π`-periodicity), the branch clause at the *lower*
arc angles `-π/2 - (1/2) arctan (w/ηs)` (from the upper one by `π`-periodicity, since
`-π/2 - (1/2) arctan (w/ηs) + π = π/2 - (1/2) arctan (w/ηs)`), and the bridge bound on the whole
bridge zone (from `[0, φE]` by evenness and `π`-periodicity).  The arc range check is
`φE = π/2 - (1/2) arctan (m/ηs)` (the definition of `mobiusPhiE`), so for `|w| ≤ m` the upper angle
lies in `[φE, π - φE]`. -/
theorem saddleProfileRows {ηs m R : ℝ} (hηs : 0 < ηs) (hηs1 : ηs < 1 / 10) (hm : 1 < m)
    (hm2 : m < 2) (hR : 2 ≤ R) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ φ : ℝ, 0 < r φ) ∧
      (∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ) ∧ (∀ φ : ℝ, r φ ≤ R) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ w ∈ Set.Icc (-m) m,
        r (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
          = Real.sqrt (ηs / -Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))))) ∧
      (∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
        Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hR0 : 0 < R := by linarith
  obtain ⟨hEcos, hEpos, hElt⟩ := leadProfile_phiE hηs hm0
  have hA2lt : Real.sqrt (ηs ^ 2 + m ^ 2) < R ^ 2 := leadProfile_sqrt_lt hηs hηs1 hm hm2.le hR
  have hL : 0 < leadProfileC2 ηs R - leadProfileC1 ηs m := by
    have := leadProfileC1_lt_C2 hηs hA2lt; linarith
  have hper : Function.Periodic (leadProfileR ηs m R) Real.pi := leadProfileR_periodic_pi ηs m R
  refine ⟨leadProfileR ηs m R, leadProfileR_contDiff hηs hR0 hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ
    exact leadProfileF_pos hηs hR0 hL
  · intro φ
    calc leadProfileR ηs m R (φ + 2 * Real.pi)
        = leadProfileR ηs m R ((φ + Real.pi) + Real.pi) := by
          rw [show φ + 2 * Real.pi = (φ + Real.pi) + Real.pi by ring]
      _ = leadProfileR ηs m R (φ + Real.pi) := hper (φ + Real.pi)
      _ = leadProfileR ηs m R φ := hper φ
  · intro φ
    exact leadProfileF_le_R hηs hR0 hL
  · intro w hw
    have hrange := phiU_mem_arcRange hηs hm0 hw
    exact leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2
  · intro w hw
    have hrange := phiU_mem_arcRange hηs hm0 hw
    have hstep : leadProfileR ηs m R (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
        = leadProfileR ηs m R (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)) := by
      have h := hper (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
      rw [show -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs) + Real.pi
            = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs) by ring] at h
      exact h.symm
    rw [hstep, leadProfileR_arc hL hEcos hEpos.le hrange.1 hrange.2]
    have hcos : Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs)))
        = Real.cos (2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))) := by
      have h2 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
          = 2 * (-(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
            + (1 : ℤ) * (2 * Real.pi) := by
        push_cast; ring
      rw [h2, Real.cos_add_int_mul_two_pi]
    rw [hcos]
  · intro φ k hk
    have h1 : leadProfileR ηs m R (φ - (k : ℝ) * Real.pi) = leadProfileR ηs m R φ := by
      have hint := (hper.int_mul k) (φ - (k : ℝ) * Real.pi)
      rw [show φ - (k : ℝ) * Real.pi + (k : ℝ) * Real.pi = φ by ring] at hint
      exact hint.symm
    have hb := leadProfileR_bridge hηs hR0 hL hA2lt.le hEcos hEpos.le hElt.le
      (φ := φ - (k : ℝ) * Real.pi) hk
    rw [h1] at hb
    exact hb

end Work.Drive.N2Lead
