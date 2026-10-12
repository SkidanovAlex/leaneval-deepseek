import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Auxiliary.pIndOrth
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.SlabCountSplit` — the sliding-box count identity

`∑ᵢ ∫_{abox n ℓ} Φ²·1_{B(u)}(xᵢ) = n₀(Φ) + n₊(Φ)` for the sliding small box
`B(u) = dlBox ℓ d u`, where

* `n₀(Φ) = ∑ᵢ ∫ (P_{B,i}Φ)²` is the condensate count at the FS box projection
  `P_{B,i} = boxPInd |B| B i` (`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`), and
* `n₊(Φ) = cnPlusBoxInd ℓ B |B| Φ = ∑ᵢ ∫ (Q_{B,i}Φ)²` is the excited count at
  `Q_{B,i} = 1_B(xᵢ) − P_{B,i}`.

The proof is the per-slot Parseval (Pythagoras) decomposition
`∫(Q_{B,i}Φ)² + ∫(P_{B,i}Φ)² = ∫(1_B(xᵢ)Φ)²`, summed over `i`.  The two ingredients are

* `Work.BoseFixB1S.Aux.pIndOrth` (the orthogonality `∫ P_{B,i}Φ·(1_B(xᵢ)Φ − P_{B,i}Φ) = 0`,
  from `Work.BoseFixB1S.Q0C.one_self_N`), and
* the abstract Pythagorean identity `sqSubAddSq` below (`IsFiniteMeasure` + a.e. bounds).

The degenerate box (`|B(u)| = 0`, e.g. `B(u) = ∅` for `u` in the far set) is covered
separately: `P_{B,i} = 0` identically (`1/0 = 0`), so the identity is trivial there.  This
matters because `boxMass ℓ d u = |B(u)|` is *not* positive for every `u`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

set_option maxHeartbeats 1000000

/-- Abstract Pythagorean identity on a finite measure space: if `h` is orthogonal to `f − h`
(`∫ h·(f − h) = 0`) and both `f`, `h` are a.e. bounded, then `∫(f−h)² + ∫h² = ∫f²`. -/
private theorem sqSubAddSq {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {f h : α → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f μ) (hh : MeasureTheory.AEStronglyMeasurable h μ)
    {Cf Ch : ℝ} (hCf : 0 ≤ Cf) (hCh : 0 ≤ Ch)
    (hfb : ∀ᵐ x ∂μ, |f x| ≤ Cf) (hhb : ∀ᵐ x ∂μ, |h x| ≤ Ch)
    (horth : ∫ x, h x * (f x - h x) ∂μ = 0) :
    (∫ x, (f x - h x) ^ 2 ∂μ) + (∫ x, (h x) ^ 2 ∂μ) = ∫ x, (f x) ^ 2 ∂μ := by
  have hnorm : ∀ᵐ x ∂μ, ‖f x‖ ≤ Cf := by
    filter_upwards [hfb] with x hx; rwa [Real.norm_eq_abs]
  have hnormh : ∀ᵐ x ∂μ, ‖h x‖ ≤ Ch := by
    filter_upwards [hhb] with x hx; rwa [Real.norm_eq_abs]
  have hInt_f : Integrable f μ := Integrable.of_bound hf Cf hnorm
  have hInt_h : Integrable h μ := Integrable.of_bound hh Ch hnormh
  have hInt_fh : Integrable (fun x => f x * h x) μ :=
    Integrable.of_bound (hf.mul hh) (Cf * Ch) (by
      filter_upwards [hfb, hhb] with x h1 h2
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hCf)
  have hInt_f2 : Integrable (fun x => (f x) ^ 2) μ :=
    Integrable.of_bound (hf.pow 2) (Cf ^ 2) (by
      filter_upwards [hfb] with x h1
      rw [Real.norm_eq_abs]
      have h2 : |(f x) ^ 2| = |f x| ^ 2 := by rw [abs_pow]
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
  have hInt_h2 : Integrable (fun x => (h x) ^ 2) μ :=
    Integrable.of_bound (hh.pow 2) (Ch ^ 2) (by
      filter_upwards [hhb] with x h1
      rw [Real.norm_eq_abs]
      have h2 : |(h x) ^ 2| = |h x| ^ 2 := by rw [abs_pow]
      rw [h2]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
  have h_orth : (∫ x, (f x * h x - (h x) ^ 2) ∂μ) = 0 := by
    rw [← horth]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hfh : (∫ x, f x * h x ∂μ) = ∫ x, (h x) ^ 2 ∂μ := by
    have := integral_sub hInt_fh hInt_h2
    rw [this] at h_orth
    linarith
  have h_expand : (∫ x, (f x - h x) ^ 2 ∂μ)
      = ∫ x, ((f x) ^ 2 - 2 * (f x * h x) + (h x) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have h_lin : (∫ x, ((f x) ^ 2 - 2 * (f x * h x) + (h x) ^ 2) ∂μ)
      = (∫ x, (f x) ^ 2 ∂μ) - 2 * (∫ x, f x * h x ∂μ) + (∫ x, (h x) ^ 2 ∂μ) := by
    have h1 : Integrable (fun x => (f x) ^ 2 - 2 * (f x * h x)) μ :=
      hInt_f2.sub (hInt_fh.const_mul 2)
    have h2 : Integrable (fun x => 2 * (f x * h x)) μ := hInt_fh.const_mul 2
    rw [integral_add h1 hInt_h2, integral_sub hInt_f2 h2, integral_const_mul]
  rw [h_expand, h_lin, hfh]
  ring

/-- **Per-slot Parseval for the FS box projection.**  For measurable `A ⊆ acube ℓ` of volume
`volA = |A|` (no positivity of `volA` needed: at `volA = 0` the projection `P_{B,i}` vanishes),
`∫ (Q_{B,i}Φ)² + ∫ (P_{B,i}Φ)² = ∫ (1_A(· i)Φ)²` on the box `abox N ℓ`. -/
private theorem parsevalBoxInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      + (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
  by_cases hvol : volA = 0
  · rw [hvol]
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    simp
  · have hvol_nonneg : 0 ≤ volA := by rw [hvolA]; exact ENNReal.toReal_nonneg
    have hvol_pos : 0 < volA := by
      rcases lt_or_eq_of_le hvol_nonneg with hlt | heq
      · exact hlt
      · exact absurd heq.symm hvol
    haveI hfin : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
    have hC0 : 0 ≤ C :=
      le_trans (norm_nonneg _) (hC _ (Submission.BoseGases.zero_mem_abox hℓ.le))
    have habsC : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
      simpa [Real.norm_eq_abs] using hC x hx
    have hvolA' : volA = (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
      rw [MeasureTheory.Measure.real_def]; exact hvolA
    obtain ⟨B, hB0, hB⟩ :=
      Work.BoseFixB1S.Q0C.abs_boxPInd_le (volA := volA) hℓ hvol_pos hA hAc hvolA' i hΦc
    have horth : (∫ x, (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)
          ∂((volume : Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ))) = 0 := by
      simpa only [] using Work.BoseFixB1S.Aux.pIndOrth hℓ hvol_pos hA hvolA hAc i hΦc
    have hf_aesm : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
        ((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
      ((measurable_const.indicator hA).comp (measurable_pi_apply i)).aestronglyMeasurable.mul
        hΦc.measurable.aestronglyMeasurable
    have hP_aesm : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x)
        ((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)) :=
      Work.BoseFixB1S.Q0C.aem_boxPInd volA A hA i hΦc _
    have hfae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)),
        |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
      filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
        with x hx
      rw [abs_mul]
      have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases h : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
            mul_le_mul hind (habsC x hx) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    have hPae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)),
        |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B := by
      filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)]
        with x hx
      exact hB x hx
    have key := sqSubAddSq (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (f := fun x : Submission.BoseGases.X N =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      (h := fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x)
      hf_aesm hP_aesm hC0 hB0 hfae hPae horth
    simpa only [Work.UBBInputs8.boxQInd] using key

/-- **The sliding-box count identity.**  The box mass `∑ᵢ ∫ Φ²·1_{B(u)}(xᵢ)` splits exactly
into the condensate count `∑ᵢ ∫ (P_{B,i}Φ)²` plus the excited count `cnPlusBoxInd`. -/
theorem SlabCountSplit {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      = (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2)
        + Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) Φ := by
  set A : Set (EuclideanSpace ℝ (Fin 3)) := Submission.BoseGases.dlBox ℓ d u with hAdef
  have hA : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume A).toReal := by
    rw [hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  have hLHS : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * A.indicator (fun _ => (1 : ℝ)) (x i))
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x i ∈ A
    · rw [Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h]; ring
  have hRHS : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u) A i Φ x) ^ 2)
        + Work.UBBInputs8.cnPlusBoxInd ℓ A (Work.SmallBoxSliding.boxMass ℓ d u) Φ
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by
    have hunfold : Work.UBBInputs8.cnPlusBoxInd ℓ A (Work.SmallBoxSliding.boxMass ℓ d u) Φ
        = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u) A i Φ x) ^ 2 := rfl
    rw [hunfold, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [add_comm]
    exact parsevalBoxInd hℓ hA hvolA hAc i hΦc
  exact hLHS.trans hRHS.symm

end Work.BoseFixR
