import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.window_integral_Bsum
import Submission.Work.GM.Affine.supf_le_of_decay

/-!
# GM §9: the `L²` bound for the inner `m₂`-sum `H_ℓ` (region II)

For `H_ℓ(τ) = Σ_{m₂ ∈ R2 M₂} m₂ · F̂f(m₂(ℓ + τ/M₃))` the window mass
`∫_{[-2,2]} ‖H_ℓ(τ)‖² dτ` is bounded, via Cauchy–Schwarz in `m₂` with weights `m₂`,
by the sum over `m₂` of the corresponding `F̂f`-mass:

`∫_{[-2,2]} ‖H_ℓ‖² ≤ (Σ_{m₂∈R2 M₂} m₂) · Σ_{m₂∈R2 M₂} M₃ ∫_{m₂(ℓ-2/M₃)}^{m₂(ℓ+2/M₃)} ‖F̂f‖²`.

The second ingredient is the *exact* change of variables `y = m₂(ℓ + τ/M₃)`
(`window_mul_integral`), which turns each `m₂`-term of the majorant into the corresponding
`F̂f`-integral.
-/

open MeasureTheory Finset

set_option autoImplicit false

-- the hypothesis `0 < M₂` is not needed (for `M₂ ≤ 0` the range `R2 M₂` is empty);
-- it is kept because the statement is fixed.
set_option linter.unusedVariables false

namespace Work.GM.Affine

/-- **Weighted Cauchy–Schwarz** for a finite family of complex numbers `z i` with nonnegative
real weights `w i`: `‖Σ_i w_i z_i‖² ≤ (Σ_i w_i) · Σ_i w_i ‖z_i‖²`. -/
lemma weighted_cs {ι : Type*} (s : Finset ι) (w : ι → ℝ) (z : ι → ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * z i‖ ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, (w i : ℂ) * z i‖ ≤ ∑ i ∈ s, w i * ‖z i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
    rw [norm_mul]
    simp [abs_of_nonneg (hw i hi)]
  have h2 : (∑ i ∈ s, w i * ‖z i‖) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
    calc (∑ i ∈ s, w i * ‖z i‖) ^ 2
        = (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * ‖z i‖)) ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi => by
            rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)])
      _ ≤ (∑ i ∈ s, (Real.sqrt (w i)) ^ 2) * ∑ i ∈ s, (Real.sqrt (w i) * ‖z i‖) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq s _ _
      _ = (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := by
          congr 1
          · exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
          · exact Finset.sum_congr rfl (fun i hi => by
              rw [mul_pow, Real.sq_sqrt (hw i hi)])
  calc ‖∑ i ∈ s, (w i : ℂ) * z i‖ ^ 2
      ≤ (∑ i ∈ s, w i * ‖z i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖z i‖ ^ 2 := h2

/-- The change of variables `x = d + c·τ` on the set integrals over `[-2,2]`:
`c ∫_{[-2,2]} F(d + c τ) dτ = ∫_{d-2c}^{d+2c} F` for `c > 0`. -/
lemma window_mul_Icc (F : ℝ → ℝ) {c d : ℝ} (hc : 0 < c) :
    c * (∫ τ in Set.Icc (-2 : ℝ) 2, F (d + c * τ))
      = ∫ x in Set.Icc (d - 2 * c) (d + 2 * c), F x := by
  have hcd : d - 2 * c ≤ d + 2 * c := by linarith
  have h1 : (∫ τ in Set.Icc (-2 : ℝ) 2, F (d + c * τ))
      = ∫ τ in (-2 : ℝ)..2, F (d + c * τ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2),
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have h2 : (∫ x in Set.Icc (d - 2 * c) (d + 2 * c), F x)
      = ∫ x in (d - 2 * c)..(d + 2 * c), F x := by
    rw [intervalIntegral.integral_of_le hcd,
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  rw [h1, h2, window_affine F (ne_of_gt hc)]

/-- The change of variables `y = m·(ℓ + τ/M₃)`:
`m ∫_{[-2,2]} F(m(ℓ + τ/M₃)) dτ = M₃ ∫_{m(ℓ-2/M₃)}^{m(ℓ+2/M₃)} F(y) dy`
for `m > 0`, `M₃ > 0`. -/
lemma window_mul_integral (F : ℝ → ℝ) {M₃ m : ℝ} (hM₃ : 0 < M₃) (hm : 0 < m) (ℓ : ℤ) :
    m * (∫ τ in Set.Icc (-2 : ℝ) 2, F (m * ((ℓ : ℝ) + τ / M₃)))
      = M₃ * ∫ y in Set.Icc (m * ((ℓ : ℝ) - 2 / M₃)) (m * ((ℓ : ℝ) + 2 / M₃)), F y := by
  have hM₃ne : M₃ ≠ 0 := ne_of_gt hM₃
  have hcpos : 0 < m / M₃ := div_pos hm hM₃
  have hkey := window_mul_Icc F (c := m / M₃) (d := m * (ℓ : ℝ)) hcpos
  have harg : ∀ τ : ℝ, m * (ℓ : ℝ) + (m / M₃) * τ = m * ((ℓ : ℝ) + τ / M₃) := by
    intro τ; field_simp
  have hb1 : m * (ℓ : ℝ) - 2 * (m / M₃) = m * ((ℓ : ℝ) - 2 / M₃) := by field_simp
  have hb2 : m * (ℓ : ℝ) + 2 * (m / M₃) = m * ((ℓ : ℝ) + 2 / M₃) := by field_simp
  rw [hb1, hb2] at hkey
  have hInt : (∫ τ in Set.Icc (-2 : ℝ) 2, F (m * ((ℓ : ℝ) + τ / M₃)))
      = ∫ τ in Set.Icc (-2 : ℝ) 2, F (m * (ℓ : ℝ) + (m / M₃) * τ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun τ _ => ?_)
    rw [harg τ]
  rw [hInt, ← hkey]
  rw [← mul_assoc, show M₃ * (m / M₃) = m by field_simp]

theorem Hfun_sq_integral_le {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (ℓ : ℤ) :
    (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Work.GM.Affine.Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      ≤ (∑ m ∈ Work.GM.Affine.R2 M₂, (m : ℝ)) *
          ∑ m₂ ∈ Work.GM.Affine.R2 M₂, M₃ *
            ∫ y in Set.Icc ((m₂ : ℝ) * ((ℓ : ℝ) - 2 / M₃))
              ((m₂ : ℝ) * ((ℓ : ℝ) + 2 / M₃)), ‖Work.GM.Affine.Fhat f y‖ ^ 2 := by
  have hcontg : Continuous (Fhat f) := continuous_fhat hf hcs
  -- the weights `m₂ ∈ R2 M₂` are strictly positive
  have hmpos : ∀ m ∈ R2 M₂, (0 : ℝ) < (m : ℝ) := by
    intro m hm
    have h1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
    have h1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  -- pointwise Cauchy–Schwarz in `m₂`
  have hpoint : ∀ τ : ℝ,
      ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2
        ≤ (∑ m ∈ R2 M₂, (m : ℝ)) *
            ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2 := by
    intro τ
    have h := weighted_cs (R2 M₂) (fun m => (m : ℝ))
      (fun m => Fhat f ((m : ℝ) * ((ℓ : ℝ) + τ / M₃)))
      (fun m hm => le_of_lt (hmpos m hm))
    simpa only [Hfun] using h
  -- integrability of each summand of the majorant
  have hGint_each : ∀ m₂ ∈ R2 M₂,
      Integrable (fun τ : ℝ => (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2)
        (volume.restrict (Set.Icc (-2 : ℝ) 2)) := by
    intro m₂ hm₂
    have hcont : Continuous
        (fun τ : ℝ => (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2) := by
      fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  -- integrability of the majorant
  have hGint : Integrable (fun τ : ℝ => (∑ m ∈ R2 M₂, (m : ℝ)) *
      ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2)
      (volume.restrict (Set.Icc (-2 : ℝ) 2)) := by
    have hsum : Continuous (fun τ : ℝ =>
        ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2) :=
      continuous_finsetSum _ (fun m₂ _ => by fun_prop)
    exact (hsum.const_mul _).continuousOn.integrableOn_compact isCompact_Icc
  -- the integral comparison
  have hmono : (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      ≤ ∫ τ in Set.Icc (-2 : ℝ) 2, (∑ m ∈ R2 M₂, (m : ℝ)) *
          ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun τ => sq_nonneg _))
      hGint (Filter.Eventually.of_forall hpoint)
  -- the computation of the majorant integral
  have hcomp : (∫ τ in Set.Icc (-2 : ℝ) 2, (∑ m ∈ R2 M₂, (m : ℝ)) *
        ∑ m₂ ∈ R2 M₂, (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2)
      = (∑ m ∈ R2 M₂, (m : ℝ)) *
          ∑ m₂ ∈ R2 M₂, M₃ *
            ∫ y in Set.Icc ((m₂ : ℝ) * ((ℓ : ℝ) - 2 / M₃))
              ((m₂ : ℝ) * ((ℓ : ℝ) + 2 / M₃)), ‖Fhat f y‖ ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum (R2 M₂)
      (f := fun m₂ τ => (m₂ : ℝ) * ‖Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))‖ ^ 2)
      (fun m₂ hm₂ => hGint_each m₂ hm₂)]
    refine Finset.sum_congr rfl (fun m₂ hm₂ => ?_)
    rw [MeasureTheory.integral_const_mul]
    exact window_mul_integral (fun y => ‖Fhat f y‖ ^ 2) hM₃ (hmpos m₂ hm₂) ℓ
  exact hmono.trans (le_of_eq hcomp)

end Work.GM.Affine
