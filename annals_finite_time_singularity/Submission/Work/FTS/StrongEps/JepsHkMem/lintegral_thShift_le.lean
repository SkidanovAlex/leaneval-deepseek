import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst_gen
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lintegral_thShift_le`

The angular half of the `L¹`-stability of the `ε`-mollifier weights under the log-coordinate
shifts: for an **arbitrary** `ENNReal`-valued function `U`,

  `∫⁻ θ ∈ Iθ, U (thShift θ p₂) ≤ e^{3|p₂|} ∫⁻ θ ∈ Iθ, U θ`,

where `Iθ = [0, π/2]` and `thShift θ p = arctan (tan θ · e^{-p})`.

## Proof

The map `θ ↦ thShift θ p₂` is the translation `ζ ↦ ζ - p₂` in the log coordinate
`ζ = log tan θ` (`thShift_arctan_exp`), and `θ ↦ arctan (e^ζ)` is a bijection of `ℝ` onto
`(0, π/2)` with Jacobian `kappa ζ = e^ζ/(1 + e^{2ζ})`.  So

  `∫⁻_{Iθ} U (thShift θ p₂) = ∫⁻_{Ioo 0 (π/2)} U (thShift θ p₂)`
  `   = ∫⁻_ζ kappa ζ · U (arctan (e^{ζ-p₂}))        (lintegral_arctan_exp_subst_gen)`
  `   = ∫⁻_ζ kappa (ζ + p₂) · U (arctan (e^ζ))      (translation invariance)`

and the comparison with `∫⁻_{Iθ} U` is the pointwise bound
`kappa (ζ + p₂) ≤ e^{3|p₂|} kappa ζ`, which is `kappa_shift_core` (`kappa (ζ+p) ≤ e^{2|p|+p}
kappa ζ`, `logJac_shift_le.lean`) together with `2|p₂| + p₂ ≤ 3|p₂|`.

The passage `Icc 0 (π/2) ↔ Ioo 0 (π/2)` is a null-set argument (`Ioo_ae_eq_Icc`); no
measurability of `U` is ever needed, since the substitution and translation lemmas are
`lintegral` (not Bochner) statements.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

/-- **`thShift` in the log coordinate `ζ = log tan θ`**: the shift of
`θ = arctan (e^ζ)` is `arctan (e^{ζ - p})`, i.e. the translation `ζ ↦ ζ - p`. -/
theorem thShift_arctan_exp' (ζ p : ℝ) :
    Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p
      = Real.arctan (Real.exp (ζ - p)) := by
  rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

theorem lintegral_thShift_le (U : ℝ → ENNReal) (p₂ : ℝ) :
    (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      ≤ ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Work.Spaces.Iθ, U θ) := by
  -- `Iθ = Icc 0 (π/2)` differs from `Ioo 0 (π/2)` by the null set `{0, π/2}`
  have hIccI : (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂) :=
    setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (π / 2))).symm
  have hIccU : (∫⁻ θ in Work.Spaces.Iθ, U θ) = ∫⁻ θ in Set.Ioo 0 (π / 2), U θ :=
    setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (π / 2))).symm
  -- the log-coordinate substitution `θ = arctan (e^ζ)`
  have hA : (∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp (ζ - p₂))) := by
    rw [HkSqAux.lintegral_arctan_exp_subst_gen
      (fun θ => U (Work.FTS.StrongEps.thShift θ p₂))]
    simp only [thShift_arctan_exp']
  -- translation invariance in the log coordinate
  have hB : (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
        * U (Real.arctan (Real.exp (ζ - p₂))))
      = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)) := by
    have h := lintegral_add_right_eq_self (μ := volume)
      (fun ζ : ℝ => ENNReal.ofReal (HkSqAux.kappa ζ)
        * U (Real.arctan (Real.exp (ζ - p₂)))) p₂
    simp only [add_sub_cancel_right] at h
    exact h.symm
  -- the pointwise Jacobian comparison
  have hk : ∀ ζ : ℝ, HkSqAux.kappa (ζ + p₂) ≤ Real.exp (3 * |p₂|) * HkSqAux.kappa ζ := by
    intro ζ
    have h1 := HkSqAux.kappa_shift_core (ζ + p₂) p₂
    simp only [add_sub_cancel_right] at h1
    have h2 : Real.exp (2 * |p₂| + p₂) ≤ Real.exp (3 * |p₂|) := by
      rw [Real.exp_le_exp]
      nlinarith [le_abs_self p₂]
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (HkSqAux.kappa_nonneg ζ))
  have hC : (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
        * U (Real.arctan (Real.exp ζ)))
      ≤ ENNReal.ofReal (Real.exp (3 * |p₂|))
          * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
              * U (Real.arctan (Real.exp ζ)) := by
    calc (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)))
        ≤ ∫⁻ ζ : ℝ, (ENNReal.ofReal (Real.exp (3 * |p₂|))
            * ENNReal.ofReal (HkSqAux.kappa ζ)) * U (Real.arctan (Real.exp ζ)) := by
          refine lintegral_mono fun ζ => ?_
          refine mul_le_mul_of_nonneg_right ?_
            (zero_le (a := U (Real.arctan (Real.exp ζ))))
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal (hk ζ)
      _ = ENNReal.ofReal (Real.exp (3 * |p₂|))
            * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
                * U (Real.arctan (Real.exp ζ)) := by
          rw [← lintegral_const_mul' (ENNReal.ofReal (Real.exp (3 * |p₂|)))
                (fun ζ => ENNReal.ofReal (HkSqAux.kappa ζ)
                  * U (Real.arctan (Real.exp ζ)))
                ENNReal.ofReal_ne_top]
          exact lintegral_congr fun ζ => mul_assoc _ _ _
  calc (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂) := hIccI
    _ = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp (ζ - p₂))) := hA
    _ = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)) := hB
    _ ≤ ENNReal.ofReal (Real.exp (3 * |p₂|))
          * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
              * U (Real.arctan (Real.exp ζ)) := hC
    _ = ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Set.Ioo 0 (π / 2), U θ) := by
        rw [← HkSqAux.lintegral_arctan_exp_subst_gen U]
    _ = ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Work.Spaces.Iθ, U θ) := by
        rw [hIccU]

end Work.FTS.StrongEps.JepsHkMem
