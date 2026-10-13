/-
Copyright: work module for the Elgindi finite-time singularity project.

# `r ↦ F_*(F)(r)/r` is integrable on `(0,∞)` for an open-quadrant smooth source `F ∈ ℋ^k`

The requested statement of this file,

  `SmoothOpen F → HkMem α k F → IntegrableOn (fun r => F_*(F)(r)/r) (Ioi 0)`,

is the *PDE-free* version of the certificate `Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk`:
no solution `Ψ` of (PolarBSL) is assumed, the regularity of `F` is only `C^∞` on the **open**
quadrant (`Work.FTS.EllipticEst.SmoothOpen`), and the decay is the honest weighted `ℋ^k`
membership `Work.Spaces.HkMem`.

(The `HkMem`-only version, without `SmoothOpen`, is *false* — see
`Submission/Work/FTS/EllipticEst/IntegrableOn_Fstar_div_of_HkMem.lean`: `HkIntegrand` only sees
`F²`, so multiplying `F` by a non-measurable `{±1}`-valued radial factor preserves `HkMem`
while destroying a.e. strong measurability of `r ↦ F_*(F)(r)`.  The hypothesis `SmoothOpen F`
is exactly what rules this out: `F` is continuous on the open quadrant, hence the angular
integral `r ↦ ∫_θ F(r,θ) sinθcos²θ` is a.e. strongly measurable for `volume.restrict (Ioi 0)`.)

The mathematics of the estimate is Cauchy–Schwarz in `θ`:

  `|F_*(F)(r)|·w(r) ≤ √((π/2)·∫_θ (F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ) =: √X(r)`,

the weight identities `r²·w(r) = (1+r)² ≥ 1` on `(0,1]` and `w(r) ≥ 1` on `(1,∞)`, and the
domination `X(r) ≤ (π/2)·∫_θ HkIntegrand α k F r θ`, whose radial integral is `HkMem`'s
`hmem.2`.  The two pointwise majorants are proved once and for all in
`Submission/Work/FTS/EllipticEst/Cert/FstarDivIntegrableOfSolHk.lean`
(`Fstar_div_le_majorant_Ioc`, `Fstar_div_le_majorant_Ioi`, stated for exactly the hypotheses
`SmoothOpen F` and `HkMem α k F`, with no PDE input); this file only has to supply the
measurability of `r ↦ F_*(F)(r)/r` and glue the two halves along `(0,1] ∪ (1,∞) = (0,∞)`.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.FstarDivOpen

set_option maxHeartbeats 1000000

/-! ## Measurability of the angular-moment quotient -/

/-- **Measurability of the angular-moment quotient.**  For a source `F` which is `C^∞` on the
open quadrant, `r ↦ F_*(F)(r)/r` is a.e. strongly measurable on `(0,∞)`.

This is the `SmoothOpen`-analogue of `Work.FTS.EllipticEst.Cert.aesm_Fstar_div_of_bslSol` (which
derives the same measurability from `F = bslOp α Ψ`); here no PDE is needed, `C^∞` on the open
quadrant suffices. -/
theorem aesm_Fstar_div_of_smoothOpen (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hmom := Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0 F hF.continuousOn
    Work.Elliptic.sinCos2 hφ
  have hinv : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => r⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (continuousOn_id.inv₀ (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
  have hmul := hmom.mul hinv
  rw [show (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      = (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, F r θ * Work.Elliptic.sinCos2 θ) * r⁻¹)
      from by funext r; rw [Work.Elliptic.Fstar, div_eq_mul_inv]]
  exact hmul

/-! ## The target statement -/

/-- **`r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`** for a source `F` which is `C^∞` on the open
quadrant `(0,∞) × (0,π/2)` and whose weighted `ℋ^k`-norm is honest.

Assembled from the two majorants of `Cert.FstarDivIntegrableOfSolHk`
(`Fstar_div_le_majorant_Ioc` on `(0,1]`, `Fstar_div_le_majorant_Ioi` on `(1,∞)`) and the
measurability `aesm_Fstar_div_of_smoothOpen` above. -/
theorem fstar_div_integrable_of_smoothOpen (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Fstar_div_of_smoothOpen F hF
  have hIoc_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioc] at hr; simp only [Set.mem_Ioi]; exact hr.1) le_rfl)
  have hIoi_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioi] at hr ⊢; linarith) le_rfl)
  have hGIoc : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioc 0 1) :=
    hmem.2.mono_set (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
  have hGIoi : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioi 1) :=
    hmem.2.mono_set (fun r hr => by
      rw [Work.Spaces.Iz]
      exact le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))
  have hc1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
    integrableOn_const (s := Set.Ioc 0 1) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hM1 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2)
      (Set.Ioc 0 1) :=
    ((hGIoc.const_mul (Real.pi / 2)).add hc1).div_const 2
  have hrpow : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)
  have hInvSq : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹) ^ 2) (Set.Ioi 1) :=
    hrpow.congr_fun (fun r hr => by
      show r ^ (-2 : ℝ) = (r⁻¹) ^ 2
      rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, inv_pow])
      measurableSet_Ioi
  have hM2 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
        + (r⁻¹) ^ 2) / 2) (Set.Ioi 1) :=
    ((hGIoi.const_mul (Real.pi / 2)).add hInvSq).div_const 2
  have h1 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioc 0 1) :=
    hM1.mono' hIoc_aesm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr.1]
      exact Work.FTS.EllipticEst.Cert.Fstar_div_le_majorant_Ioc α k F hF hmem hr)
  have h2 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 1) := by
    have hr0 : ∀ r : ℝ, r ∈ Set.Ioi 1 → (0 : ℝ) < r := fun r hr =>
      lt_trans zero_lt_one (Set.mem_Ioi.mp hr)
    refine hM2.mono' hIoi_aesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hr0 r hr)]
    exact Work.FTS.EllipticEst.Cert.Fstar_div_le_majorant_Ioi α k F hF hmem (Set.mem_Ioi.mp hr)
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h1) <;> linarith
    · intro hr
      rcases lt_or_ge r 1 with h | h
      · exact Or.inl ⟨hr, le_of_lt h⟩
      · rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl ⟨hr, le_of_eq h'.symm⟩
        · exact Or.inr h'
  have hU := h1.union h2
  rw [hset] at hU
  exact hU

end Work.FTS.EllipticEst.FstarDivOpen
