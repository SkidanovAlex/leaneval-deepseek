import Mathlib
import Submission.Work.OddCurve.LowSlope.CurveDefs
import Submission.Work.OddCurve.Free.radCurveDerivs

namespace Work.OddVolterra.Free

open Filter Topology Set
open scoped ContDiff

/-- The elementary relation `σ * cos (arctan σ) = sin (arctan σ)`. -/
private lemma mul_cos_arctan_eq_sin_arctan {σ : ℝ} :
    σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) := by
  rw [Real.sin_arctan, Real.cos_arctan]
  have h : Real.sqrt (1 + σ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- The first and second derivatives of the radial chord curve `τ ↦ R (arctan τ) cos (arctan τ)`,
in the `c / s / A / B / C` notation of `Work.OddCurve.Free.radCurveDerivs`
(`c = cos (arctan σ)`, `s = sin (arctan σ)`, `A = R (arctan σ)`,
`B = deriv R (arctan σ)`, `C = deriv (deriv R) (arctan σ)`):

* `(fun τ => R (arctan τ) cos (arctan τ))' σ = c² (B c - s A)`,
* `(fun τ => R (arctan τ) cos (arctan τ))'' σ = c³ ((2 s² - c²) A + c² C - 4 c s B)`.

These are `radCurveDerivs` combined with the explicit semicircle formulas for `profileX`. -/
private lemma radCurve_derivs_form {R : ℝ → ℝ}
    (hR : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2))) {σ : ℝ} (hσ : 0 < σ) :
    deriv (fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ =
        Real.cos (Real.arctan σ) ^ 2 *
          (deriv R (Real.arctan σ) * Real.cos (Real.arctan σ)
            - Real.sin (Real.arctan σ) * R (Real.arctan σ)) ∧
    deriv (deriv (fun τ => R (Real.arctan τ) * Real.cos (Real.arctan τ))) σ =
        Real.cos (Real.arctan σ) ^ 3 *
          ((2 * Real.sin (Real.arctan σ) ^ 2 - Real.cos (Real.arctan σ) ^ 2) * R (Real.arctan σ)
            + Real.cos (Real.arctan σ) ^ 2 * deriv (deriv R) (Real.arctan σ)
            - 4 * Real.cos (Real.arctan σ) * Real.sin (Real.arctan σ) * deriv R (Real.arctan σ)) := by
  obtain ⟨h1, h2⟩ := Work.OddCurve.Free.radCurveDerivs R hR hσ
  have hP1 : deriv Work.OddEnvelope.profileX σ = -σ * Real.cos (Real.arctan σ) ^ 3 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  have hP2 : deriv (deriv Work.OddEnvelope.profileX) σ =
      (2 * σ ^ 2 - 1) * Real.cos (Real.arctan σ) ^ 5 := by
    rw [(Work.OddEnvelope.Close.profileX_deriv_formulas σ).2.1,
      Work.OddCurve.LowSlope.profileX_eq_cos_arctan]
  have hsc := mul_cos_arctan_eq_sin_arctan (σ := σ)
  constructor
  · rw [hP1] at h1
    rw [sub_eq_iff_eq_add.mp h1, ← hsc]
    ring
  · rw [hP2] at h2
    rw [sub_eq_iff_eq_add.mp h2, ← hsc]
    ring

theorem radialPiece_deriv_neg_and_shape :
    ∃ η : ℝ, 0 < η ∧ ∀ R : ℝ → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R (Set.Icc 0 (Real.pi / 2)) →
      (∀ α ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        |R α - 1| ≤ η ∧ |deriv R α| ≤ η * α ∧ |deriv (deriv R) α| ≤ η) →
      (∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
        deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ < 0) ∧
      (∀ σ : ℝ, 0 < σ → σ < 3 / 4 →
        0 < 2 * (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ)) σ) ^ 2 -
          (R (Real.arctan σ) * Real.cos (Real.arctan σ)) *
            deriv (deriv (fun τ : ℝ => R (Real.arctan τ) * Real.cos (Real.arctan τ))) σ) := by
  refine ⟨1/100, by norm_num, ?_⟩
  intro R hR hbnd
  constructor
  · -- first claim: the derivative is negative
    intro σ hσ0 hσ1
    have hαmem : Real.arctan σ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨le_of_lt (Real.arctan_pos.mpr hσ0), le_of_lt (Real.arctan_lt_pi_div_two σ)⟩
    obtain ⟨hA1, hB1, hC1⟩ := hbnd (Real.arctan σ) hαmem
    obtain ⟨hG', _⟩ := radCurve_derivs_form hR hσ0
    rw [hG']
    have hc : 0 < Real.cos (Real.arctan σ) := Real.cos_arctan_pos σ
    have hs : 0 < Real.sin (Real.arctan σ) :=
      Real.sin_pos_of_pos_of_lt_pi (Real.arctan_pos.mpr hσ0)
        (by linarith [Real.arctan_lt_pi_div_two σ, Real.pi_pos])
    have hAge : 1 - (1:ℝ)/100 ≤ R (Real.arctan σ) := by linarith [(abs_le.mp hA1).1]
    have hBle : deriv R (Real.arctan σ) ≤ (1:ℝ)/100 * Real.arctan σ := (abs_le.mp hB1).2
    have hsc : σ * Real.cos (Real.arctan σ) = Real.sin (Real.arctan σ) :=
      mul_cos_arctan_eq_sin_arctan
    have hαlt : Real.arctan σ < σ := by
      have h := Real.lt_tan (Real.arctan_pos.mpr hσ0) (Real.arctan_lt_pi_div_two σ)
      rwa [Real.tan_arctan] at h
    have hkey : deriv R (Real.arctan σ) * Real.cos (Real.arctan σ)
        - Real.sin (Real.arctan σ) * R (Real.arctan σ) < 0 := by
      have h1 : deriv R (Real.arctan σ) * Real.cos (Real.arctan σ)
          ≤ ((1:ℝ)/100 * Real.arctan σ) * Real.cos (Real.arctan σ) :=
        mul_le_mul_of_nonneg_right hBle (le_of_lt hc)
      have h2 : Real.sin (Real.arctan σ) * (1 - (1:ℝ)/100)
          ≤ Real.sin (Real.arctan σ) * R (Real.arctan σ) :=
        mul_le_mul_of_nonneg_left hAge (le_of_lt hs)
      have hb : ((1:ℝ)/100 * Real.arctan σ) * Real.cos (Real.arctan σ)
          - Real.sin (Real.arctan σ) * (1 - (1:ℝ)/100) < 0 := by
        rw [← hsc]
        nlinarith [hαlt, hc, hσ0]
      linarith
    exact mul_neg_of_pos_of_neg (pow_pos hc 2) hkey
  · -- second claim: the shape condition
    intro σ hσ0 hσ1
    have hαmem : Real.arctan σ ∈ Set.Icc 0 (Real.pi / 2) :=
      ⟨le_of_lt (Real.arctan_pos.mpr hσ0), le_of_lt (Real.arctan_lt_pi_div_two σ)⟩
    obtain ⟨hA1, hB1, hC1⟩ := hbnd (Real.arctan σ) hαmem
    obtain ⟨hG', hG''⟩ := radCurve_derivs_form hR hσ0
    rw [hG', hG'']
    have hc : 0 < Real.cos (Real.arctan σ) := Real.cos_arctan_pos σ
    have hid : 2 * (Real.cos (Real.arctan σ) ^ 2 *
          (deriv R (Real.arctan σ) * Real.cos (Real.arctan σ)
            - Real.sin (Real.arctan σ) * R (Real.arctan σ))) ^ 2
        - (R (Real.arctan σ) * Real.cos (Real.arctan σ)) *
          (Real.cos (Real.arctan σ) ^ 3 *
            ((2 * Real.sin (Real.arctan σ) ^ 2 - Real.cos (Real.arctan σ) ^ 2) * R (Real.arctan σ)
              + Real.cos (Real.arctan σ) ^ 2 * deriv (deriv R) (Real.arctan σ)
              - 4 * Real.cos (Real.arctan σ) * Real.sin (Real.arctan σ) * deriv R (Real.arctan σ)))
        = Real.cos (Real.arctan σ) ^ 6 *
          (2 * (deriv R (Real.arctan σ)) ^ 2 + (R (Real.arctan σ)) ^ 2
            - R (Real.arctan σ) * deriv (deriv R) (Real.arctan σ)) := by ring
    rw [hid]
    refine mul_pos (pow_pos hc 6) ?_
    have hAge : (99:ℝ)/100 ≤ R (Real.arctan σ) := by linarith [(abs_le.mp hA1).1]
    have hCle : deriv (deriv R) (Real.arctan σ) ≤ (1:ℝ)/100 := (abs_le.mp hC1).2
    have hApos : (0:ℝ) < R (Real.arctan σ) := by linarith
    have hAC : 0 < R (Real.arctan σ) - deriv (deriv R) (Real.arctan σ) := by linarith
    have h1 : 0 < R (Real.arctan σ) * (R (Real.arctan σ) - deriv (deriv R) (Real.arctan σ)) :=
      mul_pos hApos hAC
    nlinarith [sq_nonneg (deriv R (Real.arctan σ)), h1]

end Work.OddVolterra.Free
