import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxPInd_adjoint_int
import Submission.Work.BoseFixB1.boxPInd_self_idem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.BddSector.parsevalBdd`

The Parseval/Pythagoras splitting of the box mass at the FS-faithful box projection
`Pᵢ = Work.UBBInputs8.boxPInd volA A i` and its complement
`Qᵢ = Work.UBBInputs8.boxQInd volA A i = 1_A(·ᵢ) − Pᵢ`,

  `∫_{abox N ℓ} (QᵢΦ)² + ∫_{abox N ℓ} (PᵢΦ)² = ∫_{abox N ℓ} 1_A(x ᵢ)·(Φ x)²`,

in the *bounded sector*: `Φ` is only assumed **measurable** and **bounded on the box**
(`∀ x ∈ abox N ℓ, |Φ x| ≤ B`) — not continuous.

The continuous (compactness) version of the same identity is
`Work.BoseFixB1S.qInd_pInd_sq_split`.  The point of this file is that *every* ingredient of that
proof is available in the bounded sector:

* `Work.BoseFixB1S.abs_boxPInd_le` gives the inherited bound `|PᵢΦ| ≤ B` on the box from a
  *pointwise* bound of `Φ` (no continuity), and `Work.BoseFixB1S.measurable_boxPInd` gives
  measurability of `PᵢΦ`;
* the orthogonality `∫ PᵢΦ·(1_A(·ᵢ)Φ − PᵢΦ) = 0` is obtained from the two corpus facts
  `Work.BoseFixB1.boxPInd_adjoint_int` (self-adjointness at `L¹` regularity in the second
  argument — boundedness of `Φ` on the box is all it needs for the first) and
  `Work.BoseFixB1.boxPInd_self_idem` (`PᵢPᵢ = Pᵢ`): with `f := Φ`, `h := PᵢΦ` they give
  `∫ (PᵢΦ)² = ∫ Φ·Pᵢ(PᵢΦ) = ∫ Φ·PᵢΦ`, and `Work.BoseSplit.pIndOrth_integrand_eq` rewrites the
  integrand pointwise as `Φ·PᵢΦ − (PᵢΦ)²`;
* the abstract Pythagoras `Work.BoseSplit.sqSubAddSq` only asks for a.e. bounds and a.e. strong
  measurability, which is what the bounded sector supplies.

The last step is the indicator collapse `(1_A(x ᵢ)·Φ x)² = 1_A(x ᵢ)·(Φ x)²` (the indicator
takes only the values `0` and `1`).
-/

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory

namespace Work.BoseFixB1.BddSector

open Submission.BoseGases

/-- **Orthogonality of the FS box projection in the bounded sector.**  For measurable `Φ`
bounded on the box by `B`,

  `∫_{abox N ℓ} (PᵢΦ)·(1_A(·ᵢ)Φ − PᵢΦ) = 0`,

i.e. the box projection of `1_A(·ᵢ)Φ` is `L²`-orthogonal to its complement.  This is the
measurable/bounded companion of `Work.BoseSplit.pIndOrth` (which assumes `Φ` continuous); the
proof uses self-adjointness `boxPInd_adjoint_int` and idempotence `boxPInd_self_idem`
instead of the slot-peeled value identity `Q0C.one_self_N`. -/
theorem parsevalBdd_orth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x)) = 0 := by
  -- the bound is nonnegative (the box is nonempty, `ℓ > 0`)
  have hB0 : 0 ≤ B :=
    le_trans (abs_nonneg _) (hb 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
  -- measurability and the inherited bound of `PᵢΦ`
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hm
  have hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hb
  -- `PᵢΦ` is integrable on the finite-measure box
  have hPint : IntegrableOn (Work.UBBInputs8.boxPInd volA A i Φ)
      (Submission.BoseGases.abox N ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le)
      hPm.aestronglyMeasurable B ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs]; exact hPb x hx)
  -- self-adjointness with `f := Φ`, `h := PᵢΦ`:  `∫ (PᵢΦ)·(PᵢΦ) = ∫ Φ·(PᵢPᵢΦ)`
  have hadj := Work.BoseFixB1.boxPInd_adjoint_int (N := N) (ℓ := ℓ) (V := volA) hℓ hvol
    (A := A) hA hvolA hAc i (f := Φ)
    (h := Work.UBBInputs8.boxPInd volA A i Φ) hm hB0 hb hPm hPint
  -- idempotence: `PᵢPᵢΦ = PᵢΦ`
  have hidem : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ)
      = Work.UBBInputs8.boxPInd volA A i Φ :=
    Work.BoseFixB1.boxPInd_self_idem hvol hA (by
      rw [MeasureTheory.Measure.real_def]; exact hvolA) i Φ
  -- hence the projection identity `∫ (PᵢΦ)² = ∫ Φ·PᵢΦ`
  have hself : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
    rw [hidem] at hadj
    calc (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
      _ = ∫ x in Submission.BoseGases.abox N ℓ,
            Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := hadj
  -- integrability of the two pieces of the pointwise expansion
  have hInt1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A i Φ x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hm hPm hb hPb
  have hInt2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_sq_of_bound hℓ hPm hPb
  -- pointwise rewriting of the integrand, then split and use `hself`
  have hpoint : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x)
          * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
              - Work.UBBInputs8.boxPInd volA A i Φ x))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
            - (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    exact Work.BoseSplit.pIndOrth_integrand_eq volA i Φ x
  rw [hpoint, integral_sub hInt1 hInt2, hself, sub_self]

theorem parsevalBdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ : Submission.BoseGases.X N → ℝ} (hm : Measurable Φ) {B : ℝ}
    (hb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      + (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
  haveI hfin : IsFiniteMeasure ((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le⟩
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hm
  have hPb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i hb
  -- a.e. strong measurability of the two factors
  have hf_aesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hm).aestronglyMeasurable
  have hP_aesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X N => Work.UBBInputs8.boxPInd volA A i Φ x)
      ((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)) :=
    hPm.aestronglyMeasurable
  -- a.e. bounds
  have hfae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)),
      |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ B := by
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    rw [abs_mul]
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * B :=
          mul_le_mul hind (hb x hx) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hPae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)),
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ B := by
    filter_upwards [self_mem_ae_restrict (Submission.BoseGases.abox_measurable N ℓ)] with x hx
    exact hPb x hx
  -- orthogonality of the two parts, in the restricted-measure form used by `sqSubAddSq`
  have horth : (∫ x, (Work.UBBInputs8.boxPInd volA A i Φ x)
        * ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
            - Work.UBBInputs8.boxPInd volA A i Φ x)
        ∂((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ))) = 0 := by
    simpa only using parsevalBdd_orth hℓ hvol hA hvolA hAc i hm hb
  -- Pythagoras
  have key := Work.BoseSplit.sqSubAddSq
    (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ))
    (f := fun x => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x)
    (h := fun x => Work.UBBInputs8.boxPInd volA A i Φ x)
    hf_aesm hP_aesm hfae hPae horth
  -- the squared-indicator collapse on the right-hand side
  have hsq : (∫ x in Submission.BoseGases.abox N ℓ,
        (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases h : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [hsq] at key
  simpa only [Work.UBBInputs8.boxQInd, add_comm] using key

end Work.BoseFixB1.BddSector
