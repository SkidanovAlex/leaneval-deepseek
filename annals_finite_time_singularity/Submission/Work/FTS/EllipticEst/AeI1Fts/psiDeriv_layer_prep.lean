import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/psiDeriv_layer_prep` — the ingredients of the angular layer bound

The `θ`-analysis of the boundary term `∫_θ σ θ (χ_ε)' θ (U·V)` of `psiDeriv_tendsto_zero`:

`|∫_{(0,π/2)} σ (χ_ε)' Uloc Vloc| ≤ 2 S₁ √(2·(2^η/(1+η))·(π/4)^η) √A
    √(∫_{(0,ε)} σ Vloc² + ∫_{(π/2-ε,π/2)} σ Vloc²)`,

for `0 < ε ≤ π/4`, given the two endpoint bounds `Uloc θ² ≤ (2^η/(1+η)) A θ^{1+η}` and
`Uloc θ² ≤ (2^η/(1+η)) A (π/2-θ)^{1+η}` for the slice `Uloc` and the `σ`-integrability of
`Uloc²`, `Vloc²`.

## Route

* `(χ_ε)'` vanishes on `(ε, π/2-ε)` (`deriv_cut_support`) and `|(χ_ε)'| ≤ 2S₁/ε` everywhere
  (`SliceMixedAux.abs_deriv_cut_le`); hence the integrand vanishes a.e. off the two layers and
  the integral splits as `∫_L + ∫_R` (`setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`), each part
  being bounded by `(2S₁/ε)` times the layer integral of `σ|Uloc||Vloc|`.
* Cauchy–Schwarz (`Work.Spaces.cs_integral`) on `L ∪ R`: `∫ σ|Uloc||Vloc| ≤ √(∫σUloc²)√(∫σVloc²)`.
* On `L = (0,ε)`: `σ θ ≤ (π/4)^η θ^{-η}` (Jordan) and `Uloc θ² ≤ C A θ^{1+η}` give
  `σUloc² ≤ C A (π/4)^η ε`, so `∫_L σUloc² ≤ C A (π/4)^η ε²`; on `R = (π/2-ε,π/2)` the reflected
  inequalities give the same (with `θ ↦ π/2-θ`), so `∫_{L∪R} σUloc² ≤ 2 C A (π/4)^η ε²`.
* The `1/ε` cancels against the `ε` of the square root.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- `σ (π/2 - θ) = σ θ`. -/
theorem sigE_pi_div_two_sub (θ : ℝ) : sigE (Real.pi / 2 - θ) = sigE θ := by
  rw [sigE, sigE, show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- The model form of the angular weight: `σ θ ≤ (π/4)^η θ^{-η}` for `θ ∈ (0, π/4]`
(Jordan's inequality `sin x ≥ (2/π) x` at `x = 2θ`). -/
theorem sigE_le_rpow {θ : ℝ} (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) :
    sigE θ ≤ (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)) := by
  have hsin : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
    have h1 : 0 ≤ 2 * θ := by linarith
    have h2 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have hle := Real.mul_le_sin h1 h2
    calc (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      _ ≤ Real.sin (2 * θ) := hle
  have hpos : 0 < (4 / Real.pi) * θ := by positivity
  have hstep := Real.rpow_le_rpow_of_nonpos hpos hsin
    (neg_nonpos.mpr Work.Spaces.eta_nonneg)
  have h4pos : (0 : ℝ) < 4 / Real.pi := by positivity
  have hinv : (4 / Real.pi) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ Work.Spaces.eta := by
    rw [Real.rpow_neg h4pos.le, ← Real.inv_rpow h4pos.le, inv_div]
  calc sigE θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
    _ ≤ ((4 / Real.pi) * θ) ^ (-(Work.Spaces.eta)) := hstep
    _ = (4 / Real.pi) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)) :=
        Real.mul_rpow h4pos.le h0.le
    _ = (Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)) := by rw [hinv]

/-- `∫_L σ Uloc² ≤ (2^η/(1+η)) A (π/4)^η ε²` on the left layer `L = (0,ε)`. -/
theorem layerLeft_U_bound {A ε : ℝ} {Uloc : ℝ → ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hεπ : ε ≤ Real.pi / 4)
    (hUc : ContinuousOn Uloc Iθo)
    (hUbd : ∀ θ ∈ Iθo, (Uloc θ) ^ 2
        ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * θ ^ (1 + Work.Spaces.eta))
    (hUint : MeasureTheory.IntegrableOn (fun θ => (Uloc θ) ^ 2 * sigE θ) Iθo) :
    (∫ θ in Set.Ioo 0 ε, (Uloc θ) ^ 2 * sigE θ)
      ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
        * ε ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hCs0 : 0 ≤ 2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith [Work.Spaces.eta_pos])
  have hLsub : Set.Ioo 0 ε ⊆ Iθo := fun x hx => ⟨hx.1, by linarith [hx.2, hεπ, hpi]⟩
  have hint : MeasureTheory.IntegrableOn (fun θ => (Uloc θ) ^ 2 * sigE θ) (Set.Ioo 0 ε) :=
    hUint.mono_set hLsub
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
        * (Real.pi / 4) ^ Work.Spaces.eta * ε) (Set.Ioo 0 ε) :=
    MeasureTheory.integrableOn_const (C := (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
      * (Real.pi / 4) ^ Work.Spaces.eta * ε) (μ := MeasureTheory.volume)
      (hs := by rw [Real.volume_Ioo, sub_zero]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ θ ∈ Set.Ioo 0 ε, (Uloc θ) ^ 2 * sigE θ
      ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta * ε := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθ4 : θ ≤ Real.pi / 4 := le_trans (le_of_lt hθ.2) hεπ
    have hsig := sigE_le_rpow hθ0 hθ4
    have hU := hUbd θ (hLsub hθ)
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt (hLsub hθ).2⟩
    have hσ0 : 0 ≤ sigE θ := sigE_nonneg hIθ
    have hbigU0 : 0 ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
        * θ ^ (1 + Work.Spaces.eta) :=
      mul_nonneg (mul_nonneg hCs0 hA) (Real.rpow_nonneg hθ0.le _)
    have hstep : (Uloc θ) ^ 2 * sigE θ
        ≤ ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * θ ^ (1 + Work.Spaces.eta))
          * ((Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta))) :=
      mul_le_mul hU hsig hσ0 hbigU0
    have hpow : θ ^ (1 + Work.Spaces.eta) * θ ^ (-(Work.Spaces.eta)) = θ := by
      rw [← Real.rpow_add hθ0, show (1 + Work.Spaces.eta) + (-(Work.Spaces.eta)) = 1 by ring,
        Real.rpow_one]
    have hfin : ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * θ ^ (1 + Work.Spaces.eta))
        * ((Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
        = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta * θ := by
      rw [show ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * θ ^ (1 + Work.Spaces.eta))
          * ((Real.pi / 4) ^ Work.Spaces.eta * θ ^ (-(Work.Spaces.eta)))
          = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (1 + Work.Spaces.eta) * θ ^ (-(Work.Spaces.eta))) by ring]
      rw [hpow]
    rw [hfin] at hstep
    have h1 : (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta * θ
        ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
          * ε :=
      mul_le_mul_of_nonneg_left (le_of_lt hθ.2)
        (mul_nonneg (mul_nonneg hCs0 hA)
          (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _))
    exact hstep.trans h1
  have h := MeasureTheory.setIntegral_mono_on hint hmaj measurableSet_Ioo hpt
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hε.le]
  ring

/-- `∫_R σ Uloc² ≤ (2^η/(1+η)) A (π/4)^η ε²` on the right layer `R = (π/2-ε, π/2)`. -/
theorem layerRight_U_bound {A ε : ℝ} {Uloc : ℝ → ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hεπ : ε ≤ Real.pi / 4)
    (hUc : ContinuousOn Uloc Iθo)
    (hUbd : ∀ θ ∈ Iθo, (Uloc θ) ^ 2
        ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
            * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
    (hUint : MeasureTheory.IntegrableOn (fun θ => (Uloc θ) ^ 2 * sigE θ) Iθo) :
    (∫ θ in Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2), (Uloc θ) ^ 2 * sigE θ)
      ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
        * ε ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hCs0 : 0 ≤ 2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta) :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith [Work.Spaces.eta_pos])
  have hπ40 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hRsub : Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2) ⊆ Iθo :=
    fun x hx => ⟨by linarith [hx.1, hεπ, hpi], hx.2⟩
  have hint : MeasureTheory.IntegrableOn (fun θ => (Uloc θ) ^ 2 * sigE θ)
      (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) := hUint.mono_set hRsub
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
        * (Real.pi / 4) ^ Work.Spaces.eta * ε)
      (Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2)) :=
    MeasureTheory.integrableOn_const (C := (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
      * (Real.pi / 4) ^ Work.Spaces.eta * ε) (μ := MeasureTheory.volume)
      (hs := by
        rw [Real.volume_Ioo, show Real.pi / 2 - (Real.pi / 2 - ε) = ε by ring]
        exact ENNReal.ofReal_ne_top)
  have hpt : ∀ θ ∈ Set.Ioo (Real.pi / 2 - ε) (Real.pi / 2),
      (Uloc θ) ^ 2 * sigE θ
        ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
          * (Real.pi / 4) ^ Work.Spaces.eta * ε := by
    intro θ hθ
    set u : ℝ := Real.pi / 2 - θ with hudef
    have hu0 : 0 < u := by rw [hudef]; linarith [hθ.2]
    have hu4 : u ≤ Real.pi / 4 := by rw [hudef]; linarith [hθ.1]
    have huε : u < ε := by rw [hudef]; linarith [hθ.1]
    have hsig := sigE_le_rpow hu0 hu4
    have hsig' : sigE θ ≤ (Real.pi / 4) ^ Work.Spaces.eta * u ^ (-(Work.Spaces.eta)) := by
      rw [show θ = Real.pi / 2 - u by rw [hudef]; ring, sigE_pi_div_two_sub]
      exact hsig
    have hU := hUbd θ (hRsub hθ)
    have hIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt (hRsub hθ).1, le_of_lt (hRsub hθ).2⟩
    have hσ0 : 0 ≤ sigE θ := sigE_nonneg hIθ
    have hπθ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have hbigU0 : 0 ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
        * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) :=
      mul_nonneg (mul_nonneg hCs0 hA) (Real.rpow_nonneg hπθ0 _)
    have hstep : (Uloc θ) ^ 2 * sigE θ
        ≤ ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
            * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
          * ((Real.pi / 4) ^ Work.Spaces.eta * u ^ (-(Work.Spaces.eta))) :=
      mul_le_mul hU hsig' hσ0 hbigU0
    have hpow : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * u ^ (-(Work.Spaces.eta)) = u := by
      rw [hudef, ← Real.rpow_add hu0,
        show (1 + Work.Spaces.eta) + (-(Work.Spaces.eta)) = 1 by ring, Real.rpow_one]
    have hfin : ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
          * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
        * ((Real.pi / 4) ^ Work.Spaces.eta * u ^ (-(Work.Spaces.eta)))
        = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
          * u := by
      rw [show ((2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A
            * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta))
          * ((Real.pi / 4) ^ Work.Spaces.eta * u ^ (-(Work.Spaces.eta)))
          = (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
            * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) * u ^ (-(Work.Spaces.eta))) by ring]
      rw [hpow]
    rw [hfin] at hstep
    have h1 : (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta * u
        ≤ (2 ^ Work.Spaces.eta / (1 + Work.Spaces.eta)) * A * (Real.pi / 4) ^ Work.Spaces.eta
          * ε :=
      mul_le_mul_of_nonneg_left (le_of_lt huε)
        (mul_nonneg (mul_nonneg hCs0 hA) (Real.rpow_nonneg hπ40 _))
    exact hstep.trans h1
  have h := MeasureTheory.setIntegral_mono_on hint hmaj measurableSet_Ioo hpt
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at h
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.measureReal_def, Real.volume_Ioo,
    show Real.pi / 2 - (Real.pi / 2 - ε) = ε by ring, ENNReal.toReal_ofReal hε.le]
  ring


/-- **Cauchy-Schwarz for the weighted pair** on a set `S ⊆ (0,π/2)`: with `u = √σ |Uloc|` and
`v = √σ |Vloc|` one has `∫_S u v ≤ √(∫_S u²) √(∫_S v²)`, which is the estimate
`∫_S σ|Uloc||Vloc| ≤ √(∫_S σ Uloc²) √(∫_S σ Vloc²)`. -/
theorem layer_cs {Uloc Vloc : ℝ → ℝ} {S : Set ℝ} (hS : S ⊆ Iθo) (hSmeas : MeasurableSet S)
    (hUc : ContinuousOn Uloc Iθo) (hVc : ContinuousOn Vloc Iθo)
    (hUint : MeasureTheory.IntegrableOn (fun θ => (Uloc θ) ^ 2 * sigE θ) Iθo)
    (hVint : MeasureTheory.IntegrableOn (fun θ => (Vloc θ) ^ 2 * sigE θ) Iθo) :
    (∫ θ in S, sigE θ * |Uloc θ| * |Vloc θ|)
      ≤ Real.sqrt (∫ θ in S, (Uloc θ) ^ 2 * sigE θ)
        * Real.sqrt (∫ θ in S, (Vloc θ) ^ 2 * sigE θ) := by
  classical
  have hsig0_of : ∀ θ ∈ Iθo, 0 ≤ sigE θ := fun θ hθ =>
    sigE_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  set u : ℝ → ℝ := fun θ => Real.sqrt (sigE θ) * |Uloc θ| with hudef
  set v : ℝ → ℝ := fun θ => Real.sqrt (sigE θ) * |Vloc θ| with hvdef
  have hu_sq : ∀ θ ∈ S, (u θ) ^ 2 = (Uloc θ) ^ 2 * sigE θ := by
    intro θ hθ
    have hσ := hsig0_of θ (hS hθ)
    rw [hudef]
    simp only
    rw [mul_pow, Real.sq_sqrt hσ, sq_abs]
    ring
  have hv_sq : ∀ θ ∈ S, (v θ) ^ 2 = (Vloc θ) ^ 2 * sigE θ := by
    intro θ hθ
    have hσ := hsig0_of θ (hS hθ)
    rw [hvdef]
    simp only
    rw [mul_pow, Real.sq_sqrt hσ, sq_abs]
    ring
  have huv : ∀ θ ∈ S, u θ * v θ = sigE θ * |Uloc θ| * |Vloc θ| := by
    intro θ hθ
    have hσ := hsig0_of θ (hS hθ)
    rw [hudef, hvdef]
    simp only
    calc (Real.sqrt (sigE θ) * |Uloc θ|) * (Real.sqrt (sigE θ) * |Vloc θ|)
        = (Real.sqrt (sigE θ) * Real.sqrt (sigE θ)) * (|Uloc θ| * |Vloc θ|) := by ring
      _ = sigE θ * (|Uloc θ| * |Vloc θ|) := by rw [Real.mul_self_sqrt hσ]
      _ = sigE θ * |Uloc θ| * |Vloc θ| := by ring
  have huaesm : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict S) := by
    rw [hudef]
    exact (((continuousOn_sigE.mono hS).sqrt).mul ((hUc.mono hS).abs)).aestronglyMeasurable hSmeas
  have hvaesm : MeasureTheory.AEStronglyMeasurable v (MeasureTheory.volume.restrict S) := by
    rw [hvdef]
    exact (((continuousOn_sigE.mono hS).sqrt).mul ((hVc.mono hS).abs)).aestronglyMeasurable hSmeas
  have huint : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) S :=
    (hUint.mono_set hS).congr_fun (fun θ hθ => (hu_sq θ hθ).symm) hSmeas
  have hvint : MeasureTheory.IntegrableOn (fun θ => (v θ) ^ 2) S :=
    (hVint.mono_set hS).congr_fun (fun θ hθ => (hv_sq θ hθ).symm) hSmeas
  have humem : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict S) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr huint
  have hvmem : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict S) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvaesm).mpr hvint
  have hcs := Work.Spaces.cs_integral humem hvmem
  have e1 : (∫ θ in S, u θ * v θ) = ∫ θ in S, sigE θ * |Uloc θ| * |Vloc θ| :=
    MeasureTheory.setIntegral_congr_fun hSmeas huv
  have e2 : (∫ θ in S, (u θ) ^ 2) = ∫ θ in S, (Uloc θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_congr_fun hSmeas hu_sq
  have e3 : (∫ θ in S, (v θ) ^ 2) = ∫ θ in S, (Vloc θ) ^ 2 * sigE θ :=
    MeasureTheory.setIntegral_congr_fun hSmeas hv_sq
  rw [e1, e2, e3] at hcs
  have hA0 : 0 ≤ ∫ θ in S, sigE θ * |Uloc θ| * |Vloc θ| :=
    MeasureTheory.setIntegral_nonneg hSmeas fun θ hθ =>
      mul_nonneg (mul_nonneg (hsig0_of θ (hS hθ)) (abs_nonneg _)) (abs_nonneg _)
  calc (∫ θ in S, sigE θ * |Uloc θ| * |Vloc θ|)
      = Real.sqrt ((∫ θ in S, sigE θ * |Uloc θ| * |Vloc θ|) ^ 2) := (Real.sqrt_sq hA0).symm
    _ ≤ Real.sqrt ((∫ θ in S, (Uloc θ) ^ 2 * sigE θ)
          * ∫ θ in S, (Vloc θ) ^ 2 * sigE θ) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∫ θ in S, (Uloc θ) ^ 2 * sigE θ)
          * Real.sqrt (∫ θ in S, (Vloc θ) ^ 2 * sigE θ) :=
        Real.sqrt_mul (show (0 : ℝ) ≤ ∫ θ in S, (Uloc θ) ^ 2 * sigE θ from
            MeasureTheory.setIntegral_nonneg hSmeas fun θ hθ =>
              mul_nonneg (sq_nonneg (Uloc θ)) (hsig0_of θ (hS hθ)))
          (∫ θ in S, (Vloc θ) ^ 2 * sigE θ)

end Work.FTS.EllipticEst.AeI1Fts
