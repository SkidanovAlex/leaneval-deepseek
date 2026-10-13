import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces.ThetaAgmon

set_option autoImplicit false

/-- **Weighted Hardy inequality on the angular interval.**

For `1 < γ ≤ 2` and `h` continuous on `[0,π/2]` with `∫_θ h² sin(2θ)^{2-γ} < ∞`,

`(∫_0^θ h)² ≤ (100/(γ-1)) ∫_θ h² sin(2θ)^{2-γ}` for every `θ ∈ [0,π/2]`.

The proof writes `sin(2θ)^{2-γ} = sin(2θ)^{(2-γ)/2} · sin(2θ)^{(γ-2)/2}` and applies
Cauchy–Schwarz (`Work.Spaces.cs_integral`) against the two factors, the second of which
has integral `≤ 100/(γ-1)` because `γ - 2 ∈ (-1,0]` (`Work.Spaces.sin_two_rpow`). -/
theorem HardyWeightedInterval (γ : ℝ) (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) (h : ℝ → ℝ)
    (hcont : ContinuousOn h (Set.Icc 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) (Set.Icc 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      (∫ s in (0 : ℝ)..θ, h s) ^ 2 ≤
        (100 / (γ - 1)) * ∫ s in Set.Icc 0 (Real.pi / 2),
          (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
  intro θ hθ
  obtain ⟨hθ0, hθπ⟩ := hθ
  have hsubIoc : Set.Ioc (0 : ℝ) θ ⊆ Work.Spaces.Iθ :=
    fun s hs => ⟨le_of_lt hs.1, le_trans hs.2 hθπ⟩
  -- the weighted bound `∫_Iθ sin(2θ)^(γ-2) ≤ 100/(γ-1)` from the library
  have hbase := Work.Spaces.sin_two_rpow (γ - 2) (by linarith) (by linarith)
  have hWint : MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ (γ - 2))
      Work.Spaces.Iθ := hbase.1
  have hWval : ∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (γ - 2) ≤ 100 / (γ - 1) := by
    have hh := hbase.2
    rwa [show γ - 2 + 1 = γ - 1 by ring] at hh
  have hWintIoc : MeasureTheory.IntegrableOn (fun s : ℝ => (Real.sin (2 * s)) ^ (γ - 2))
      (Set.Ioc 0 θ) := hWint.mono_set hsubIoc
  have hbaseIoc : MeasureTheory.IntegrableOn
      (fun s : ℝ => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) (Set.Ioc 0 θ) :=
    hint.mono_set hsubIoc
  -- nonnegativity on the angular interval
  have hsin_nn : ∀ s ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * s) := fun s hs =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hs.1], by linarith [hs.2, Real.pi_pos]⟩
  have hbasenn_ae : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn s hs) _)
  have hWnn_ae : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun s : ℝ => (Real.sin (2 * s)) ^ (γ - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact Real.rpow_nonneg (hsin_nn s hs) _
  have hIoc_le : Set.Ioc 0 θ ≤ᵐ[volume] Work.Spaces.Iθ := Filter.Eventually.of_forall hsubIoc
  -- the two factors of the weight
  set A : ℝ → ℝ := fun s => h s * (Real.sin (2 * s)) ^ ((2 - γ) / 2) with hA
  set B : ℝ → ℝ := fun s => (Real.sin (2 * s)) ^ ((γ - 2) / 2) with hB
  -- a.e. positivity of `sin(2·)` on `Ioc 0 θ` (only the endpoints can fail)
  have hfin : ({s : ℝ | s ∈ Set.Ioc 0 θ ∧ ¬ (0 < Real.sin (2 * s))} : Set ℝ).Finite := by
    apply Set.Finite.subset (Set.finite_singleton (Real.pi / 2))
    rintro s ⟨hsI, hsin⟩
    simp only [Set.mem_singleton_iff]
    by_contra hne
    have hspos : 0 < 2 * s := by linarith [hsI.1]
    have hslt : 2 * s < Real.pi := by
      have : s < Real.pi / 2 := lt_of_le_of_ne (le_trans hsI.2 hθπ) hne
      linarith
    exact absurd (Real.sin_pos_of_pos_of_lt_pi hspos hslt) (not_lt.mpr (le_of_not_gt hsin))
  have hae_pos : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 θ)), 0 < Real.sin (2 * s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
    simpa only [not_imp] using hfin.measure_zero MeasureTheory.volume
  -- pointwise (a.e.) identifications of the squares and of the product
  have hsqA : (fun s : ℝ => A s ^ 2) =ᵐ[volume.restrict (Set.Ioc 0 θ)]
      (fun s : ℝ => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_pos] with s hs hpos
    simp only [hA]
    have hc : (Real.sin (2 * s) ^ ((2 - γ) / 2)) ^ 2
        = Real.sin (2 * s) ^ (2 - γ) := by
      rw [sq, ← Real.rpow_add hpos ((2 - γ) / 2) ((2 - γ) / 2),
        show (2 - γ) / 2 + (2 - γ) / 2 = 2 - γ by ring]
    rw [mul_pow, hc]
  have hsqB : (fun s : ℝ => B s ^ 2) =ᵐ[volume.restrict (Set.Ioc 0 θ)]
      (fun s : ℝ => (Real.sin (2 * s)) ^ (γ - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_pos] with s hs hpos
    simp only [hB]
    rw [sq, ← Real.rpow_add hpos ((γ - 2) / 2) ((γ - 2) / 2),
      show (γ - 2) / 2 + (γ - 2) / 2 = γ - 2 by ring]
  have hprod : (fun s : ℝ => A s * B s) =ᵐ[volume.restrict (Set.Ioc 0 θ)] h := by
    filter_upwards [hae_pos] with s hs
    simp only [hA, hB]
    rw [mul_assoc, ← Real.rpow_add hs,
      show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
  -- integrability of the squares
  have hA2_int : Integrable (fun s : ℝ => A s ^ 2) (volume.restrict (Set.Ioc 0 θ)) :=
    hbaseIoc.congr hsqA.symm
  have hB2_int : Integrable (fun s : ℝ => B s ^ 2) (volume.restrict (Set.Ioc 0 θ)) :=
    hWintIoc.congr hsqB.symm
  -- almost-everywhere strong measurability
  have hh_aesm : AEStronglyMeasurable h (volume.restrict (Set.Ioc 0 θ)) :=
    (hcont.mono hsubIoc).aestronglyMeasurable measurableSet_Ioc
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioc 0 θ)) := by
    simp only [hA]
    exact hh_aesm.mul
      (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id))
        ((2 - γ) / 2)).aestronglyMeasurable
  have hB_aesm : AEStronglyMeasurable B (volume.restrict (Set.Ioc 0 θ)) := by
    simp only [hB]
    exact (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id))
      ((γ - 2) / 2)).aestronglyMeasurable
  -- membership in `L²`
  have hMemA : MemLp A 2 (volume.restrict (Set.Ioc 0 θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hA_aesm).2 hA2_int
  have hMemB : MemLp B 2 (volume.restrict (Set.Ioc 0 θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hB_aesm).2 hB2_int
  -- Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral (u := A) (v := B) (s := Set.Ioc 0 θ) hMemA hMemB
  -- the two integral bounds
  have hA2_le : ∫ s in Set.Ioc 0 θ, A s ^ 2 ≤
      ∫ s in Work.Spaces.Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
    rw [MeasureTheory.integral_congr_ae hsqA]
    exact MeasureTheory.setIntegral_mono_set hint hbasenn_ae hIoc_le
  have hB2_le : ∫ s in Set.Ioc 0 θ, B s ^ 2 ≤ 100 / (γ - 1) := by
    rw [MeasureTheory.integral_congr_ae hsqB]
    exact le_trans (MeasureTheory.setIntegral_mono_set hWint hWnn_ae hIoc_le) hWval
  have hInt_eq : ∫ s in Set.Ioc 0 θ, A s * B s = ∫ s in Set.Ioc 0 θ, h s :=
    MeasureTheory.integral_congr_ae hprod
  -- nonnegativity of the two integrals used in the product estimate
  have hB2nn : 0 ≤ ∫ s in Set.Ioc 0 θ, B s ^ 2 :=
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall (fun s => sq_nonneg (B s)))
  have hbase_nn : 0 ≤ ∫ s in Work.Spaces.Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn s hs) _)
  have hmain : (∫ s in Set.Ioc 0 θ, h s) ^ 2 ≤
      (100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
        (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
    calc (∫ s in Set.Ioc 0 θ, h s) ^ 2
        = (∫ s in Set.Ioc 0 θ, A s * B s) ^ 2 := by rw [← hInt_eq]
      _ ≤ (∫ s in Set.Ioc 0 θ, A s ^ 2) * (∫ s in Set.Ioc 0 θ, B s ^ 2) := hcs
      _ ≤ (∫ s in Work.Spaces.Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ))
            * (100 / (γ - 1)) := mul_le_mul hA2_le hB2_le hB2nn hbase_nn
      _ = (100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
            (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by ring
  rw [intervalIntegral.integral_of_le hθ0]
  simpa only [Work.Spaces.Iθ] using hmain

end Work.Spaces.ThetaAgmon
