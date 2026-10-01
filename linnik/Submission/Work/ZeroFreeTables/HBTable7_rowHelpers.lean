/-
# ZeroFreeTables — HBTable7_rowHelpers

The two extraction helpers for the **five-term** (HB Lemma 8.5) route of Table 7, the analogue of
`HBTable7_extract.row_extract` / `HBTable7_assembly.cert_forces` for the third method.

The engine `Work.ZeroFreeTables.lemma85pt_region` concludes

`0 ≤ J₂ - J₁ - J₀ + f(0)(3c + 4ε)`, i.e. with `c = 1/8`, `0 ≤ J₂ - J₁ - J₀ + f(0)(3/8 + 4ε)`,

where `J₂ = ∫ e^{λ₂t} f`, `J₁ = ∫ e^{(λ₂-λ₁)t} f`, `J₀ = ∫ f`.  Its left-hand side is (for `f ≥ 0`)
increasing in `λ₁` and in `λ₂` — the same pointwise monotonicity `bracket_integral_le` proves for
the third method — so the *strict failure* of the inequality at the row values `(b,c)`
(`CertRow85`) together with its validity at the true pair `(λ₁,λ₂)` with `λ₁ ≤ b`, `λ₂ ≤ c`
forces a contradiction.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_extract
import Submission.Work.ZeroFreeTables.HBTable7_assembly
import Submission.Work.ZeroFreeTables.HBTable7_defs85

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **The extraction of one row (five-term form).**  If the engine's inequality (HB Lemma 8.5)
holds at the true pair `(z₁, z₂)`, and the row certificate `CertRow85` strictly violates it at the
row values `(b,c)`, while `0 ≤ z₁ ≤ b` and `z₂ ≤ c`, then we have a contradiction. -/
theorem row_extract85 {x₀ : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hfnn : ∀ t ∈ Set.Icc 0 x₀, 0 ≤ f t)
    {A b c z₁ z₂ : ℝ} (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c)
    (heng : 0 ≤ (∫ t in (0:ℝ)..x₀, Real.exp (z₂ * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((z₂ - z₁) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + A)
    (hcert : (∫ t in (0:ℝ)..x₀, Real.exp (c * t) * f t)
        - (∫ t in (0:ℝ)..x₀, Real.exp ((c - b) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t) + A < 0) : False := by
  have hkey := bracket_integral_le hx₀ hcont hfnn h1 hz₁ hz₂
  linarith only [heng, hcert, hkey]

/-- **`cert_forces` for the five-term form**: conversion of the engine's conclusion into the `tfF`
form (via the bridge `tfF =` the Laplace transform of `tf71f (π/4) lam` and `f(0) = 2λ(π-3)`)
followed by the extraction. -/
theorem cert_forces85 (lam ε b c z₁ z₂ : ℝ) (hlam : 0 < lam)
    (hcont : ContinuousOn (tf71f (Real.pi/4) lam) (Set.Icc 0 (2 * tf71γ (Real.pi/4) lam)))
    (hfnn : ∀ t ∈ Set.Icc 0 (2 * tf71γ (Real.pi/4) lam), 0 ≤ tf71f (Real.pi/4) lam t)
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (heng : 0 ≤ tfF lam (-z₂) - tfF lam (z₁ - z₂) - tfF lam 0
      + (2 * lam * (Real.pi - 3)) * ((3 : ℝ) / 8 + 4 * ε))
    (hcert : CertRow85 b c lam ε) (h1 : 0 ≤ z₁) (hz₁ : z₁ ≤ b) (hz₂ : z₂ ≤ c) : False := by
  have hx₀ : 0 ≤ 2 * tf71γ (Real.pi/4) lam := by
    have h := tf71γ_pos pi_div_four_mem.1 pi_div_four_mem.2 hlam
    linarith
  have hF0 : tfF lam 0 =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), tf71f (Real.pi/4) lam t := by
    rw [hbridge 0]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  obtain ⟨hlam', hcert'⟩ := hcert
  rw [tfF_eq_exp hbridge z₂, tfF_eq_exp_sub hbridge z₁ z₂, hF0] at heng
  rw [tfF_eq_exp hbridge c, tfF_eq_exp_sub hbridge b c, hF0] at hcert'
  exact row_extract85 (A := (2 * lam * (Real.pi - 3)) * ((3 : ℝ) / 8 + 4 * ε))
    hx₀ hcont hfnn h1 hz₁ hz₂ heng hcert'

/-- The certificate of the five-term route is proved at `ε = 0`; since the left hand side is
*affine* in `ε` with positive slope `8λ(π-3)`, a strictly negative value at `ε = 0` upgrades to a
strictly negative value at a (tiny) positive `ε` (the engine `lemma85pt_region` requires
`0 < ε`). -/
theorem CertRow85.eps_pos {b c lam : ℝ} (h : CertRow85 b c lam 0) (hlam : 0 < lam) :
    ∃ ε : ℝ, 0 < ε ∧ CertRow85 b c lam ε := by
  obtain ⟨hlam', hineq⟩ := h
  have hpi : (0 : ℝ) < Real.pi - 3 := by linarith [Real.pi_gt_three]
  have hD : (0 : ℝ) < (2 * lam * (Real.pi - 3)) * 4 := by positivity
  set P : ℝ := tfF lam (-c) - tfF lam (b - c) - tfF lam 0
    + (2 * lam * (Real.pi - 3)) * ((3 : ℝ) / 8) with hP
  have hPneg : P < 0 := by
    rw [hP]
    simpa using hineq
  refine ⟨-P / (2 * ((2 * lam * (Real.pi - 3)) * 4)), ?_, ?_⟩
  · refine div_pos (neg_pos.mpr hPneg) ?_
    have : (0:ℝ) < 2 * ((2 * lam * (Real.pi - 3)) * 4) := by positivity
    exact this
  · refine ⟨hlam', ?_⟩
    have hkey : tfF lam (-c) - tfF lam (b - c) - tfF lam 0
        + (2 * lam * (Real.pi - 3)) *
            ((3 : ℝ) / 8 + 4 * (-P / (2 * ((2 * lam * (Real.pi - 3)) * 4)))) = P / 2 := by
      rw [hP]
      field_simp
      ring
    rw [hkey]
    linarith only [hPneg]

end Work.ZeroFreeTables
