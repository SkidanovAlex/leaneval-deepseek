import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.ktarg_signedArea

namespace Work.RPB.B5

/-! ## The two halves of the `τ = 0` slice of the glued shape

On `σ ≥ 0` the glued shape is the target circle by `ksb_kshape_zero_slice` (the `τ = 0`
correction is switched on at full strength, `xfade δ σ = 1`).  On `-δ/4 < σ < 0` the same
conclusion holds by the opposite mechanism: the clamp is the identity there (`kclamp_of_abs_le`),
so the hypothesis `hcirc` identifies the chart point with the circle `√(2+2σ) · e^{it}`, while the
target circle is the *same* circle (`kphc δ k σ = 0`); hence the correction factor
`ktarg - uproj (…)` in `knear` vanishes identically, and the blend cut-off `kblf δ σ` is `0`
because `σ < 0 ≤ δ/2`. -/

/-- For `-δ/4 < σ < 0` the glued shape at `τ = 0` is the target circle. -/
theorem kshape_zero_slice_neg (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ)
    (hcirc : ∀ σ ∈ Set.Ioo (-δ) 0, ∀ u : ℝ,
      Work.RPV.uproj (W 0 u (ρh 0 u σ))
        = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (u * Complex.I)) :
    ∀ σ : ℝ, -(δ / 4) < σ → σ < 0 → ∀ t : ℝ,
      Work.RPB.B5.kshape CI W ρh δ k 0 σ t = Work.RPB.B5.ktarg δ k σ t := by
  intro σ hσ hσ0 t
  have hσδ : -δ < σ := by linarith
  have hclamp : kclamp δ σ = σ := by
    apply kclamp_of_abs_le hδ
    rw [abs_of_neg hσ0]
    linarith
  have hcir : Work.RPV.uproj (W 0 t (ρh 0 t σ))
      = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) :=
    hcirc σ ⟨hσδ, hσ0⟩ t
  have hkpc : kphc δ k σ = 0 := ksb_kphc_zero k hδ (by linarith)
  have htarg : ktarg δ k σ t
      = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I) := by
    unfold ktarg krd
    rw [hkpc]
    simp
  have hU : Work.RPV.uproj (W 0 t (ρh 0 t (kclamp δ σ))) = ktarg δ k σ t := by
    rw [hclamp, htarg]
    exact hcir
  have hknear : knear CI W ρh δ k 0 σ t = ktarg δ k σ t := by
    unfold knear
    rw [hU, ksb_kbbmp_zero δ]
    ring
  have hblf : kblf δ σ = 0 := ksb_kblf_zero hδ (by linarith)
  unfold kshape
  rw [hblf]
  simp only [Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero]
  exact hknear

/-- At `τ = 0` the glued shape is the target circle for every `σ > -δ/4`. -/
theorem kshape_zero_slice_of_gt (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ)
    (hcirc : ∀ σ ∈ Set.Ioo (-δ) 0, ∀ u : ℝ,
      Work.RPV.uproj (W 0 u (ρh 0 u σ))
        = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (u * Complex.I)) :
    ∀ σ : ℝ, -(δ / 4) < σ → ∀ t : ℝ,
      Work.RPB.B5.kshape CI W ρh δ k 0 σ t = Work.RPB.B5.ktarg δ k σ t := by
  intro σ hσ t
  rcases lt_or_ge σ 0 with h | h
  · exact kshape_zero_slice_neg CI W ρh hδ k hcirc σ hσ h t
  · exact ksb_kshape_zero_slice CI W ρh δ k hδ h (t := t)

/-- **The `τ = 0` slice of the collar is the target circle.**

For `σ > -δ/4` the glued shape `kshape` is `ktarg`, so its signed area is `(2+2σ)π` and the
normalisation factor is `kg = 2π(1+σ)/((2+2σ)π) = 1`; applying `kdiagM 1` is the identity
(`ksb_kdiagM_one`).  Note that `σ > -δ/4 ≥ -1/4` because `δ ≤ 1`, so `1 + σ > 0` and the division
by `karS` is legitimate. -/
theorem kcf_tau0_slice (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℤ)
    (hcirc : ∀ σ ∈ Set.Ioo (-δ) 0, ∀ u : ℝ,
      Work.RPV.uproj (W 0 u (ρh 0 u σ))
        = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (u * Complex.I)) :
    ∀ σ : ℝ, -(δ / 4) < σ → ∀ t : ℝ,
      Work.RPB.B5.kgam CI W ρh δ k 0 σ t = Work.RPB.B5.ktarg δ k σ t := by
  intro σ hσ t
  have hsh : ∀ s : ℝ, kshape CI W ρh δ k 0 σ s = ktarg δ k σ s :=
    kshape_zero_slice_of_gt CI W ρh hδ k hcirc σ hσ
  have hpos : (0 : ℝ) < 1 + σ := by linarith
  have hfun : (fun s : ℝ => kshape CI W ρh δ k 0 σ s) = (fun s : ℝ => ktarg δ k σ s) :=
    funext hsh
  have hkarS : karS CI W ρh δ k 0 σ = 2 * Real.pi * (1 + σ) := by
    unfold karS
    rw [hfun, ktarg_signedArea δ k σ (by linarith)]
    ring
  have hkg : kg CI W ρh δ k 0 σ = 1 := by
    rw [kg, hkarS]
    exact div_self (ne_of_gt (by positivity))
  show kgam CI W ρh δ k 0 σ t = ktarg δ k σ t
  rw [kgam, hkg, hsh t, ksb_kdiagM_one]

end Work.RPB.B5
