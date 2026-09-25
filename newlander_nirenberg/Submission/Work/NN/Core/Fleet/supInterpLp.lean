import Mathlib

/-!
# Interpolation of an `L^{2k}` norm against the sup bound and the `L²` norm

`Work.NN.Core.Fleet.supInterpLp` is the elementary interpolation step used in the
self-improvement of the Moser exponent:
if `‖u‖ ≤ M` pointwise on a set `S`, then for every `k ≥ 1`

  `‖u‖_{L^{2k}(μ|_S)} ≤ M^{(k-1)/k} · ‖u‖_{L²(μ|_T)}^{1/k}`,   (`S ⊆ T`).

The proof is the elementary inequality `|u|^{2k} = |u|^{2k-2}|u|² ≤ M^{2k-2}|u|²`
integrated over `μ|_S`, followed by taking the `(2k)`-th root.

The pointwise bound is only assumed on `S`, while `eLpNorm` is taken with respect to
`μ.restrict S`; the two are reconciled a.e. by `MeasureTheory.ae_restrict_iff₀`,
which needs no measurability of `S` itself, only that the predicate
`‖u z‖ ≤ M` define a null measurable set (it does, by a.e. strong measurability of `u`).
-/

namespace Work.NN.Core.Fleet

open MeasureTheory ENNReal
open scoped ENNReal

/-- The pointwise inequality behind `supInterpLp`: for `1 ≤ k` and `a ≤ M` in `ℝ≥0∞`,
`a ^ (2k) ≤ M ^ (2k - 2) * a ^ 2`. -/
private lemma rpow_two_mul_le_rpow {a M : ℝ≥0∞} {k : ℕ} (hk : 1 ≤ k) (ha : a ≤ M) :
    a ^ (2 * (k : ℝ)) ≤ M ^ (2 * (k : ℝ) - 2) * a ^ (2 : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h2 : (0 : ℝ) ≤ 2 * (k : ℝ) - 2 := by linarith
  have hstep : a ^ (2 * (k : ℝ)) = a ^ (2 * (k : ℝ) - 2) * a ^ (2 : ℝ) := by
    conv_lhs => rw [show 2 * (k : ℝ) = (2 * (k : ℝ) - 2) + 2 by ring]
    exact ENNReal.rpow_add_of_nonneg (x := a) (2 * (k : ℝ) - 2) 2 h2 (by norm_num)
  rw [hstep]
  exact mul_le_mul' (ENNReal.rpow_le_rpow ha h2) le_rfl

theorem supInterpLp {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {S T : Set α}
    {u : α → ℂ} {k : ℕ} (hk : 1 ≤ k) {M : ENNReal}
    (hM : ∀ z ∈ S, ENNReal.ofReal ‖u z‖ ≤ M) (hST : S ⊆ T)
    (hmeas : MeasureTheory.AEStronglyMeasurable u (μ.restrict T)) :
    MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ))) (μ.restrict S)
      ≤ M ^ (((k : ℝ) - 1) / (k : ℝ)) *
        (MeasureTheory.eLpNorm u 2 (μ.restrict T)) ^ (1 / (k : ℝ)) := by
  have hmeasS : MeasureTheory.AEStronglyMeasurable u (μ.restrict S) :=
    hmeas.mono_measure (Measure.restrict_mono_set μ hST)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have h2kpos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  -- The pointwise bound holds a.e. on `S` for `μ.restrict S`.
  have hae_le : ∀ᵐ z ∂(μ.restrict S), ‖u z‖ₑ ≤ M := by
    have hnull : NullMeasurableSet {z | ‖u z‖ₑ ≤ M} (μ.restrict S) :=
      hmeasS.enorm.nullMeasurableSet_preimage measurableSet_Iic
    refine (ae_restrict_iff₀ hnull).mpr ?_
    filter_upwards with z hz
    simpa using hM z hz
  have hae : ∀ᵐ z ∂(μ.restrict S),
      ‖u z‖ₑ ^ (2 * (k : ℝ)) ≤ M ^ (2 * (k : ℝ) - 2) * ‖u z‖ₑ ^ (2 : ℝ) :=
    hae_le.mono fun _ hz => rpow_two_mul_le_rpow hk hz
  -- Integrate the pointwise inequality.
  have hI : ∫⁻ z, ‖u z‖ₑ ^ (2 * (k : ℝ)) ∂(μ.restrict S)
      ≤ M ^ (2 * (k : ℝ) - 2) * ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) := by
    calc ∫⁻ z, ‖u z‖ₑ ^ (2 * (k : ℝ)) ∂(μ.restrict S)
        ≤ ∫⁻ z, M ^ (2 * (k : ℝ) - 2) * ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) :=
          lintegral_mono_ae hae
      _ = M ^ (2 * (k : ℝ) - 2) * ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S) :=
          lintegral_const_mul'' _
            (f := fun z => ‖u z‖ₑ ^ (2 : ℝ)) (hmeasS.enorm.pow_const (2 : ℝ))
  -- Rewrite both `eLpNorm`s as roots of the corresponding integrals.
  have hA : eLpNorm u (ENNReal.ofReal (2 * (k : ℝ))) (μ.restrict S)
      = (∫⁻ z, ‖u z‖ₑ ^ (2 * (k : ℝ)) ∂(μ.restrict S)) ^ (1 / (2 * (k : ℝ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.mpr h2kpos)
      ENNReal.ofReal_ne_top hmeasS, ENNReal.toReal_ofReal h2kpos.le]
  have hB : eLpNorm u 2 (μ.restrict S)
      = (∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hmeasS]
    norm_num
  calc eLpNorm u (ENNReal.ofReal (2 * (k : ℝ))) (μ.restrict S)
      = (∫⁻ z, ‖u z‖ₑ ^ (2 * (k : ℝ)) ∂(μ.restrict S)) ^ (1 / (2 * (k : ℝ))) := hA
    _ ≤ (M ^ (2 * (k : ℝ) - 2) * ∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S))
          ^ (1 / (2 * (k : ℝ))) := ENNReal.rpow_le_rpow hI (by positivity)
    _ = M ^ (((k : ℝ) - 1) / (k : ℝ)) *
          ((∫⁻ z, ‖u z‖ₑ ^ (2 : ℝ) ∂(μ.restrict S)) ^ (1 / 2 : ℝ)) ^ (1 / (k : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        congr 1
        · rw [← ENNReal.rpow_mul]
          congr 1
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        · rw [show (1 : ℝ) / (2 * (k : ℝ)) = (1 / 2) * (1 / (k : ℝ)) by ring,
            ENNReal.rpow_mul]
    _ = M ^ (((k : ℝ) - 1) / (k : ℝ)) * (eLpNorm u 2 (μ.restrict S)) ^ (1 / (k : ℝ)) := by
        rw [hB]
    _ ≤ M ^ (((k : ℝ) - 1) / (k : ℝ)) *
          (eLpNorm u 2 (μ.restrict T)) ^ (1 / (k : ℝ)) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
          (eLpNorm_mono_measure u (Measure.restrict_mono_set μ hST)) (by positivity))

end Work.NN.Core.Fleet
