import Mathlib
import Submission.Work.BMF.kdr_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset MeasureTheory
open scoped BigOperators

/-- A measurable nonnegative function bounded above by `C` is `MemLp` for every exponent, on a
finite measure space. -/
private lemma memLp_of_le_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : α → ℝ} {C : ℝ} (hFm : Measurable F) (hF : ∀ x, 0 ≤ F x)
    (hFb : ∀ x, F x ≤ C) (p : ENNReal) : MemLp F p μ :=
  MemLp.of_bound hFm.aestronglyMeasurable C
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hF x)]; exact hFb x)

/-- **Two-factor Lyapunov interpolation.**  On a finite measure space, for a measurable
`f : α → ℝ` with values in `[0, C]` and `0 < θ ≤ 1`,
`∫ f^{1+θ} ≤ (∫ f²)^θ · (∫ f)^{1-θ}`. -/
theorem interp_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hfm : Measurable f) {C θ : ℝ} (hC : 0 ≤ C) (hf : ∀ x, f x ∈ Set.Icc 0 C)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ x, f x ^ (1 + θ) ∂μ) ≤ (∫ x, f x ^ (2 : ℝ) ∂μ) ^ θ * (∫ x, f x ∂μ) ^ (1 - θ) := by
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · subst h1
    rw [show (1:ℝ) + 1 = 2 by norm_num, Real.rpow_one, sub_self, Real.rpow_zero, mul_one]
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hf x).1
  have hfC : ∀ x, f x ≤ C := fun x => (hf x).2
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have h1θ0 : 0 < 1 - θ := by linarith
  have h1θne : (1 - θ) ≠ 0 := ne_of_gt h1θ0
  have hpq : θ⁻¹.HolderConjugate (1 - θ)⁻¹ := by
    rw [Real.holderConjugate_iff]
    exact ⟨(one_lt_inv₀ hθ0).mpr h1, by rw [inv_inv, inv_inv]; ring⟩
  have hm1 : Measurable fun x => f x ^ (2 * θ) :=
    (Real.continuous_rpow_const (by positivity)).measurable.comp hfm
  have hm2 : Measurable fun x => f x ^ (1 - θ) :=
    (Real.continuous_rpow_const (by linarith)).measurable.comp hfm
  have hM1 : MemLp (fun x => f x ^ (2 * θ)) (ENNReal.ofReal θ⁻¹) μ :=
    memLp_of_le_bound hm1 (fun x => Real.rpow_nonneg (hf0 x) _)
      (fun x => Real.rpow_le_rpow (hf0 x) (hfC x) (by positivity)) _
  have hM2 : MemLp (fun x => f x ^ (1 - θ)) (ENNReal.ofReal (1 - θ)⁻¹) μ :=
    memLp_of_le_bound hm2 (fun x => Real.rpow_nonneg (hf0 x) _)
      (fun x => Real.rpow_le_rpow (hf0 x) (hfC x) (by linarith)) _
  have hholder :
      (∫ x, f x ^ (2 * θ) * f x ^ (1 - θ) ∂μ)
        ≤ (∫ x, (f x ^ (2 * θ)) ^ θ⁻¹ ∂μ) ^ (1 / θ⁻¹)
          * (∫ x, (f x ^ (1 - θ)) ^ (1 - θ)⁻¹ ∂μ) ^ (1 / (1 - θ)⁻¹) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (ae_of_all _ fun x => Real.rpow_nonneg (hf0 x) _)
      (ae_of_all _ fun x => Real.rpow_nonneg (hf0 x) _) hM1 hM2
  have hfun1 : (fun x => (f x ^ (2 * θ)) ^ θ⁻¹) = fun x => f x ^ (2 : ℝ) := by
    funext x
    simp only [← Real.rpow_mul (hf0 x),
      show 2 * θ * θ⁻¹ = (2:ℝ) by rw [mul_assoc, mul_inv_cancel₀ hθne, mul_one]]
  have hfun2 : (fun x => (f x ^ (1 - θ)) ^ (1 - θ)⁻¹) = fun x => f x := by
    funext x
    simp only [← Real.rpow_mul (hf0 x), mul_inv_cancel₀ h1θne, Real.rpow_one]
  have e1 : (∫ x, (f x ^ (2 * θ)) ^ θ⁻¹ ∂μ) = ∫ x, f x ^ (2 : ℝ) ∂μ := by rw [hfun1]
  have e2 : (∫ x, (f x ^ (1 - θ)) ^ (1 - θ)⁻¹ ∂μ) = ∫ x, f x ∂μ := by rw [hfun2]
  have hfun0 : (fun x => f x ^ (1 + θ)) = fun x => f x ^ (2 * θ) * f x ^ (1 - θ) := by
    funext x
    rw [show (1:ℝ) + θ = 2 * θ + (1 - θ) by ring,
      Real.rpow_add_of_nonneg (hf0 x) (show (0:ℝ) ≤ 2 * θ by positivity)
        (show (0:ℝ) ≤ 1 - θ by linarith)]
  calc (∫ x, f x ^ (1 + θ) ∂μ)
      = ∫ x, f x ^ (2 * θ) * f x ^ (1 - θ) ∂μ := by rw [hfun0]
    _ ≤ (∫ x, (f x ^ (2 * θ)) ^ θ⁻¹ ∂μ) ^ (1 / θ⁻¹)
          * (∫ x, (f x ^ (1 - θ)) ^ (1 - θ)⁻¹ ∂μ) ^ (1 / (1 - θ)⁻¹) := hholder
    _ = (∫ x, f x ^ (2 : ℝ) ∂μ) ^ θ * (∫ x, f x ∂μ) ^ (1 - θ) := by
        rw [e1, e2]
        simp only [one_div, inv_inv]

/-- **Three-factor Hölder on the unit box.**  For nonnegative measurable `U`, `V` on `[0,1]^m` and
`s ≥ 1`,
`∫ U·V ≤ (∫ U^{2s})^{1/(2s)} · (∫ V²)^{1/(2s)} · (∫ V)^{1-1/s}`.

Hölder with conjugates `p = 2s`, `q = 1 + θ` (where `θ = 1/(2s-1)`, so that `q = 2s/(2s-1)`)
gives `∫ U·V ≤ (∫ U^{2s})^{1/(2s)} (∫ V^{1+θ})^{1/(1+θ)}`; then the Lyapunov interpolation
`∫ V^{1+θ} ≤ (∫ V²)^θ (∫ V)^{1-θ}` (`interp_rpow`) raised to `1/(1+θ)` yields the stated
exponents, since `θ/(1+θ) = 1/(2s)` and `(1-θ)/(1+θ) = 1 - 1/s`. -/
theorem holder_box (m : ℕ) (s : ℕ) (hs : 1 ≤ s) {U V : (Fin m → ℝ) → ℝ} {BU BV : ℝ}
    (hU : ∀ α, 0 ≤ U α) (hV : ∀ α, 0 ≤ V α) (hUm : Measurable U) (hVm : Measurable V)
    (hUb : ∀ α, U α ≤ BU) (hVb : ∀ α, V α ≤ BV) :
    (∫ α in unitBox m, U α * V α)
      ≤ (∫ α in unitBox m, U α ^ (2 * (s:ℝ))) ^ (1 / (2 * (s:ℝ)))
        * (∫ α in unitBox m, V α ^ 2) ^ (1 / (2 * (s:ℝ)))
        * (∫ α in unitBox m, V α) ^ (1 - 1 / (s:ℝ)) := by
  have hvbox : volume (unitBox m) = 1 := by
    rw [unitBox, volume_pi, Measure.pi_pi]
    simp
  set μ : Measure (Fin m → ℝ) := volume.restrict (unitBox m) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]
    exact isFiniteMeasure_restrict.mpr (by rw [hvbox]; exact ENNReal.one_ne_top)
  have hBU : 0 ≤ BU := le_trans (hU 0) (hUb 0)
  have hBV : 0 ≤ BV := le_trans (hV 0) (hVb 0)
  have hsqVfun : (fun α => V α ^ (2 : ℝ)) = fun α => V α ^ 2 := by
    funext α
    exact Real.rpow_natCast (V α) 2
  have hsqV : (∫ α, V α ^ (2 : ℝ) ∂μ) = ∫ α, V α ^ 2 ∂μ := by rw [hsqVfun]
  rw [← hsqV]
  have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hsR0 : 0 < (s:ℝ) := by linarith
  have hsne : (s:ℝ) ≠ 0 := ne_of_gt hsR0
  have hden : 0 < 2 * (s:ℝ) - 1 := by linarith
  have hdenne : 2 * (s:ℝ) - 1 ≠ 0 := ne_of_gt hden
  have h2sne : 2 * (s:ℝ) ≠ 0 := by positivity
  set θ : ℝ := 1 / (2 * (s:ℝ) - 1) with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hden]; linarith
  have h1θpos : 0 < 1 + θ := by linarith
  have hq : 1 + θ = 2 * (s:ℝ) / (2 * (s:ℝ) - 1) := by
    rw [hθdef]; field_simp; ring
  have hconj : (2 * (s:ℝ)).HolderConjugate (1 + θ) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    rw [hq, inv_div]
    field_simp
    ring
  have hid1 : θ * (1 / (1 + θ)) = 1 / (2 * (s:ℝ)) := by
    rw [hq, hθdef, one_div_div]
    field_simp
    try ring
  have hid2 : (1 - θ) * (1 / (1 + θ)) = 1 - 1 / (s:ℝ) := by
    rw [hq, hθdef, one_div_div]
    field_simp
    ring
  have hH1 : (∫ α, U α * V α ∂μ) ≤ (∫ α, U α ^ (2 * (s:ℝ)) ∂μ) ^ (1 / (2 * (s:ℝ)))
      * (∫ α, V α ^ (1 + θ) ∂μ) ^ (1 / (1 + θ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg hconj (ae_of_all _ hU) (ae_of_all _ hV)
      (memLp_of_le_bound hUm hU hUb _) (memLp_of_le_bound hVm hV hVb _)
  have hinterp : (∫ α, V α ^ (1 + θ) ∂μ)
      ≤ (∫ α, V α ^ (2 : ℝ) ∂μ) ^ θ * (∫ α, V α ∂μ) ^ (1 - θ) :=
    interp_rpow hVm hBV (fun α => ⟨hV α, hVb α⟩) hθ0 hθ1
  have hIV2 : 0 ≤ ∫ α, V α ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun α => Real.rpow_nonneg (hV α) _
  have hIV : 0 ≤ ∫ α, V α ∂μ := integral_nonneg hV
  have hIU : 0 ≤ ∫ α, U α ^ (2 * (s:ℝ)) ∂μ :=
    integral_nonneg fun α => Real.rpow_nonneg (hU α) _
  have hI1θ : 0 ≤ ∫ α, V α ^ (1 + θ) ∂μ :=
    integral_nonneg fun α => Real.rpow_nonneg (hV α) _
  have hstep : (∫ α, V α ^ (1 + θ) ∂μ) ^ (1 / (1 + θ))
      ≤ ((∫ α, V α ^ (2 : ℝ) ∂μ) ^ θ * (∫ α, V α ∂μ) ^ (1 - θ)) ^ (1 / (1 + θ)) :=
    Real.rpow_le_rpow hI1θ hinterp (by positivity)
  have hrhs : ((∫ α, V α ^ (2 : ℝ) ∂μ) ^ θ * (∫ α, V α ∂μ) ^ (1 - θ)) ^ (1 / (1 + θ))
      = (∫ α, V α ^ (2 : ℝ) ∂μ) ^ (1 / (2 * (s:ℝ)))
        * (∫ α, V α ∂μ) ^ (1 - 1 / (s:ℝ)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hIV2 _) (Real.rpow_nonneg hIV _)]
    rw [← Real.rpow_mul hIV2 θ (1 / (1 + θ)),
      ← Real.rpow_mul hIV (1 - θ) (1 / (1 + θ))]
    rw [hid1, hid2]
  calc (∫ α, U α * V α ∂μ)
      ≤ (∫ α, U α ^ (2 * (s:ℝ)) ∂μ) ^ (1 / (2 * (s:ℝ)))
          * (∫ α, V α ^ (1 + θ) ∂μ) ^ (1 / (1 + θ)) := hH1
    _ ≤ (∫ α, U α ^ (2 * (s:ℝ)) ∂μ) ^ (1 / (2 * (s:ℝ)))
          * ((∫ α, V α ^ (2 : ℝ) ∂μ) ^ θ * (∫ α, V α ∂μ) ^ (1 - θ)) ^ (1 / (1 + θ)) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hIU _)
    _ = (∫ α, U α ^ (2 * (s:ℝ)) ∂μ) ^ (1 / (2 * (s:ℝ)))
          * ((∫ α, V α ^ (2 : ℝ) ∂μ) ^ (1 / (2 * (s:ℝ)))
            * (∫ α, V α ∂μ) ^ (1 - 1 / (s:ℝ))) := by rw [hrhs]
    _ = (∫ α, U α ^ (2 * (s:ℝ)) ∂μ) ^ (1 / (2 * (s:ℝ)))
          * (∫ α, V α ^ (2 : ℝ) ∂μ) ^ (1 / (2 * (s:ℝ)))
          * (∫ α, V α ∂μ) ^ (1 - 1 / (s:ℝ)) := by rw [mul_assoc]

end Work.BMF
