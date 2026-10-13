/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T45AbndInts` — the angular integrals of the `A`-slot factor `Abnd`

`Abnd α i θ` is the angular factor of the pointwise bound
`|D_z^j D_θ^i A| ≤ C·K·Abnd α i θ` for a `𝒲^{6,∞}`-bounded coefficient `A`
(see `T45Defs`).  It is `1` when `i = 0` and `(α + sin 2θ)·sin(2θ)^{α/5}`
otherwise.  This file proves that the leftover angular weights of the level-six
rows are integrable on `Iθ = [0,π/2]` and that their integrals are bounded by
`D·α^{-1}` for an absolute constant `D` (we take `D = 40000`):

* `sin(2θ)^{-η}·Abnd α i θ²` for every `i` (`η = 99/100`);
* `Abnd α i θ²` for every `i`;
* `sin(2θ)^{-γ}·Abnd α i θ²` for `i ≥ 1` (`γ = 1 + α/10`).

## Mathematics

`Abnd α i θ ≤ 2` on `Iθ` for `α ≤ 1`, so the first two families are dominated by
`4·sin(2θ)^{-η}` resp. the constant `4`, whose integrals are bounded by
`4·10000` resp. `2π`.

For the third family one must use the extra vanishing of `Abnd`: for `i ≠ 0`,
`Abnd α i θ² = (α + sin 2θ)²·sin(2θ)^{2α/5}`, hence

  `sin(2θ)^{-γ}·Abnd α i θ² = (α + sin 2θ)²·sin(2θ)^{2α/5 - γ}`
                            `≤ 4·sin(2θ)^{2α/5 - γ}`,

and `2α/5 - γ = 3α/10 - 1 ∈ (-1, 0)`; `Work.Spaces.sin_two_rpow` then gives an
integral `≤ 4·100/(3α/10) = 4000/(3α) ≤ 40000·α^{-1}`.  The exponent `α/5` in
`Abnd` is exactly what makes `3α/10 > 0`, i.e. the singular weight integrable.

The general `q`-estimate used for the third family is proved separately in
`Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux.Abnd_rpow_sq_integral_le`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux.Abnd_rpow_sq_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false

/-! ## Elementary facts about `Abnd` -/

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `Abnd α i` is measurable: it is either the constant `1` or
`(α + sin 2·)·sin(2·)^{α/5}`. -/
private lemma Abnd_measurable (α : ℝ) (i : ℕ) : Measurable (Abnd α i) := by
  by_cases h : i = 0
  · have hf : Abnd α i = fun _ : ℝ => (1 : ℝ) := by
      funext θ; rw [Abnd, ite_eq_left h]
    rw [hf]; exact measurable_const
  · have hf : Abnd α i = fun θ : ℝ => (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      funext θ; rw [Abnd, ite_eq_right (by simpa using h)]
    rw [hf]; fun_prop

/-- Strong measurability of the `η`-weighted integrand. -/
private lemma Abnd_eta_integrand_aesm (α : ℝ) (i : ℕ) :
    AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
  have h1 : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by fun_prop
  exact (h1.mul ((Abnd_measurable α i).pow_const 2)).aestronglyMeasurable

/-! ## The target -/

theorem T45AbndInts : ∃ D : ℝ, 0 < D ∧ ∀ α ∈ Set.Ioc 0 1,
    (∀ i : ℕ, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) ∧
    (∀ i : ℕ, MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) ∧
    (∀ i : ℕ, 1 ≤ i → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.FTS.StrongPersist.H6Pair6Aux.Abnd α i θ) ^ 2)
        ≤ D * α ^ (-(1 : ℝ))) := by
  refine ⟨40000, by norm_num, ?_⟩
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  -- `α^{-1} ≥ 1`, so it suffices to bound every integral by `40000`.
  have hαinv : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one]; exact (one_le_inv₀ hα0).mpr hα1
  have hD : (40000 : ℝ) ≤ 40000 * α ^ (-(1 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hαinv (by norm_num : (0 : ℝ) ≤ 40000)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · -- Family 1: `sin(2θ)^{-η}·Abnd²`, bounded by `4·sin(2θ)^{-η}` since `Abnd ≤ 2`.
    intro i
    have hbase : Integrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict Work.Spaces.Iθ) := by
      have h1 : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
      have h2 : (-(Work.Spaces.eta)) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
      exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) h1 h2).1
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
      have h1 := Abnd_nonneg hα0 hθ i
      positivity
    have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
      have h1 := Abnd_nonneg hα0 hθ i
      have h2 := Abnd_le_two hα0 hα1 hθ i
      have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
      have h4 : (Abnd α i θ) ^ 2 ≤ 4 := by nlinarith
      calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * 4 := mul_le_mul_of_nonneg_left h4 hsnn
        _ = 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
    have hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖(fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2) θ‖
          ≤ (fun θ : ℝ => 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) θ := by
      filter_upwards [hle, hnn] with θ hle' hnn'
      rw [Real.norm_of_nonneg hnn']; exact hle'
    refine ⟨(hbase.const_mul 4).mono' (Abnd_eta_integrand_aesm α i) hbdd, ?_⟩
    calc (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * (Abnd α i θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, 4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          integral_mono_of_nonneg hnn (hbase.const_mul 4) hle
      _ = 4 * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ 40000 := by
          have h1 := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
            (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)).2
          have hnum : (100 : ℝ) / (-(Work.Spaces.eta) + 1) = 10000 := by
            rw [Work.Spaces.eta]; norm_num
          rw [hnum] at h1
          linarith [h1]
      _ ≤ 40000 * α ^ (-(1 : ℝ)) := hD
  · -- Family 2: `Abnd²`, bounded by the constant `4`.
    intro i
    have hvol : volume Work.Spaces.Iθ < ⊤ := by
      rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Abnd α i θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Abnd_measurable α i).pow_const 2).aestronglyMeasurable
    have hbdd : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ‖(Abnd α i θ) ^ 2‖ ≤ 4 := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have h1 := Abnd_nonneg hα0 hθ i
      have h2 := Abnd_le_two hα0 hα1 hθ i
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith
    refine ⟨MeasureTheory.IntegrableOn.of_bound hvol hmeas 4 hbdd, ?_⟩
    have hle : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        (Abnd α i θ) ^ 2 ≤ (fun _ : ℝ => (4 : ℝ)) θ := by
      filter_upwards [hbdd] with θ hθ; simpa using hθ
    have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (Abnd α i θ) ^ 2) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      positivity
    have h4int : Integrable (fun _ : ℝ => (4 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (by rw [lt_top_iff_ne_top] at hvol; exact hvol)
    have hreal : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Abnd α i θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, (4 : ℝ) := integral_mono_of_nonneg hnn h4int hle
      _ = 4 * volume.real Work.Spaces.Iθ := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
      _ = 4 * (Real.pi / 2) := by rw [hreal]
      _ ≤ 40000 * α ^ (-(1 : ℝ)) := by
          have hpi : Real.pi ≤ 4 := Real.pi_le_four
          linarith [hD]
  · -- Family 3: `sin(2θ)^{-γ}·Abnd²` for `i ≥ 1`; now the `sin(2θ)^{2α/5}` of `Abnd²`
    -- is essential.
    intro i hi
    have hi0 : i ≠ 0 := by omega
    have hq1 : (1 : ℝ) ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have hq2 : Work.Spaces.gam α < 1 + 2 * (α / 5) := by rw [Work.Spaces.gam]; linarith
    obtain ⟨hint, hbd⟩ := T45Aux.Abnd_rpow_sq_integral_le hα0 hα1 hi0 hq1 hq2
    refine ⟨hint, ?_⟩
    have hden : 2 * (α / 5) - Work.Spaces.gam α + 1 = 3 * α / 10 := by
      rw [Work.Spaces.gam]; ring
    rw [hden] at hbd
    have hkey : (4 : ℝ) * (100 / (3 * α / 10)) = (4000 / 3) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      field_simp
      ring
    rw [hkey] at hbd
    have hfin : (4000 / 3 : ℝ) / α ≤ 40000 * α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hα0.le)
    linarith [hbd, hfin]

end Work.FTS.StrongPersist.H6Pair6Aux
