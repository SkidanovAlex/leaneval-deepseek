import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSplit.pIndOrth` — orthogonality of the box projection with its complement

The FS-faithful box projection `Work.UBBInputs8.boxPInd volA A i` (FS `eq:HBU`) is

  `(PᵢΦ)(x) = 1_A(x i) · (1/volA)·∫_{z∈A} Φ(x|i↦z) dz`,

i.e. the box indicator in slot `i` times the slot-independent mean over `A`.  Its complement is
`1_A(· i)Φ − PᵢΦ`.  The claim of this file is the orthogonality

  `∫_{abox N ℓ} PᵢΦ · (1_A(· i)Φ − PᵢΦ) = 0`,

the `L²`-orthogonality of the decomposition `1_A(· i)Φ = (1_A(· i)Φ − PᵢΦ) + PᵢΦ` used to split
the box mass (`Work.BoseFixB1S.qInd_pInd_sq_split`).

The proof is one-line mathematics with the standard ingredients:

* pointwise, since `1_A(x i)² = 1_A(x i)`, the integrand equals `Φ·PᵢΦ − (PᵢΦ)²` (because
  `(1 − 1_A(· i))·PᵢΦ = 0`, the projection carrying the indicator);
* `∫ Φ·PᵢΦ = ∫ (PᵢΦ)²` is `Work.BoseFixB1S.Q0C.one_self_N` (the mean is the orthogonal
  projection of the fibre);
* `Φ` is bounded on the compact box and `PᵢΦ` inherits the bound, so both pieces are
  integrable on the box and `integral_sub` applies.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseSplit

/-- **Pointwise form of the integrand.**  Because the box projection carries the box indicator
in slot `i` (`(1 − 1_A(· i))·PᵢΦ = 0`) and `1_A(x i)² = 1_A(x i)`, the integrand of
`pIndOrth` equals `Φ·PᵢΦ − (PᵢΦ)²` pointwise. -/
theorem pIndOrth_integrand_eq {N : ℕ} (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    (Work.UBBInputs8.boxPInd volA A i Φ x)
        * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
            - Work.UBBInputs8.boxPInd volA A i Φ x)
      = Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
        - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 := by
  simp only [Work.UBBInputs8.boxPInd]
  by_cases h : x i ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h] <;> ring

theorem pIndOrth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 := by
  haveI : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  -- a bound for `Φ` on the box and the inherited bound for `PᵢΦ`
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (Submission.BoseGases.zero_mem_abox hℓ.le))
  obtain ⟨B, hB0, hB⟩ :=
    Work.BoseFixB1S.Q0C.abs_boxPInd_le (volA := volA) hℓ hvol hA hAc hvolA i hΦc
  -- integrability of the two pieces on the box
  have hIntΦ : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) (Submission.BoseGases.abox N ℓ) volume := by
    refine Integrable.mono' (integrable_const (C * B)) ?_ ?_
    · exact ((hΦc.measurable.aestronglyMeasurable).mul
        (Work.BoseFixB1S.Q0C.aem_boxPInd volA A hA i hΦc _))
    · filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hC x hx) (hB x hx) (abs_nonneg _) hC0
  have hIntP2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound (N := N) hℓ
      (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦc.measurable) hB
  -- the pointwise rewriting of the integrand
  have hEq : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    exact pIndOrth_integrand_eq volA i Φ x
  rw [hEq]
  -- split the integral and use the one-slot self-adjointness `one_self_N`
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2))
      = (∫ x in Submission.BoseGases.abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x)
        - (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      from integral_sub hIntΦ hIntP2]
  rw [Work.BoseFixB1S.Q0C.one_self_N (volA := volA) hℓ hvol hA hvolA hAc i hΦc]
  ring

end Work.BoseSplit
