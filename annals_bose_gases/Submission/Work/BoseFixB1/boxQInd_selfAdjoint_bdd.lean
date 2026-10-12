import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.boxQInd_selfAdjoint_bdd`

Self-adjointness, on the analysis box `abox N ℓ`, of FS's box mean-free projection

  `Q_{B,i} = 1_A(x_i)·Φ − P_{B,i}Φ`      (`Work.UBBInputs8.boxQInd`),

where `P_{B,i}` is FS's box condensate projection (`Work.UBBInputs8.boxPInd`,
`P_{B,i}ψ = |B|⁻¹⟨1_B,ψ⟩1_B` in slot `i`, self-adjoint by
`Work.BoseFixB1S.boxPIndSelfAdjoint`).

## Math

Writing `σᵢ(x) = 1_A(x i)`, the pointwise identity

  `(Qᵢf)·g − f·(Qᵢg) = f·(Pᵢg) − (Pᵢf)·g`

(the two `σ`-terms cancel since `σ` is a real scalar and multiplication commutes) turns the
difference of the two integrals into `∫ f·(Pᵢg) − ∫ (Pᵢf)·g`, which vanishes by the
self-adjointness of `Pᵢ`.

Integrability of each of the four products on `abox N ℓ` is obtained from the bounds
`|f| ≤ Cf`, `|g| ≤ Cg`, `|Pᵢf| ≤ Cf`, `|Pᵢg| ≤ Cg` (`Work.BoseFixB1S.abs_boxPInd_le`) and
`|σᵢ| ≤ 1`, hence `|Qᵢf| ≤ 2|Cf|`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- `boxQInd` is measurable for measurable `f`. -/
theorem measurable_boxQInd_bdd {N : ℕ} (volA : ℝ) {A : Set E3} (hA : MeasurableSet A)
    (i : Fin N) {f : Submission.BoseGases.X N → ℝ} (hf : Measurable f) :
    Measurable (Work.UBBInputs8.boxQInd volA A i f) := by
  have hσ : Measurable (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * f x) :=
    ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hf
  have hP : Measurable (Work.UBBInputs8.boxPInd volA A i f) :=
    Work.BoseFixB1S.measurable_boxPInd volA A hA i hf
  have hEq : Work.UBBInputs8.boxQInd volA A i f
      = fun x : Submission.BoseGases.X N =>
          A.indicator (fun _ => (1 : ℝ)) (x i) * f x
            - Work.UBBInputs8.boxPInd volA A i f x := rfl
  rw [hEq]
  exact hσ.sub hP

/-- Bound on `boxQInd` on the box: `|Qᵢf| ≤ 2|Cf|` whenever `|f| ≤ Cf` on the box. -/
theorem abs_boxQInd_le_two {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {f : Submission.BoseGases.X N → ℝ} {Cf : ℝ}
    (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxQInd V A i f x| ≤ 2 * |Cf| := by
  intro x hx
  have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * f x| ≤ |Cf| := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |f x|
        ≤ 1 * |Cf| :=
          mul_le_mul hσ (le_trans (hfb x hx) (le_abs_self Cf)) (abs_nonneg _) zero_le_one
      _ = |Cf| := one_mul _
  have h2 : |Work.UBBInputs8.boxPInd V A i f x| ≤ |Cf| :=
    le_trans (Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb x hx) (le_abs_self Cf)
  have hEq : Work.UBBInputs8.boxQInd V A i f x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * f x
        - Work.UBBInputs8.boxPInd V A i f x := rfl
  rw [hEq]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * f x - Work.UBBInputs8.boxPInd V A i f x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * f x| + |Work.UBBInputs8.boxPInd V A i f x| :=
        abs_sub _ _
    _ ≤ |Cf| + |Cf| := add_le_add h1 h2
    _ = 2 * |Cf| := by ring

/-- The pointwise identity `(Qᵢf)·g − f·(Qᵢg) = f·(Pᵢg) − (Pᵢf)·g`. -/
theorem boxQInd_mul_sub_mul {n : ℕ} (V : ℝ) {A : Set E3} (i : Fin n)
    (f g : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    Work.UBBInputs8.boxQInd V A i f x * g x - f x * Work.UBBInputs8.boxQInd V A i g x
      = f x * Work.UBBInputs8.boxPInd V A i g x
        - Work.UBBInputs8.boxPInd V A i f x * g x := by
  simp only [Work.UBBInputs8.boxQInd]
  ring

theorem boxQInd_selfAdjoint_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (i : Fin N) {f g : Submission.BoseGases.X N → ℝ} (hfm : Measurable f) {Cf : ℝ}
    (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf)
    (hgm : Measurable g) {Cg : ℝ}
    (hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |g x| ≤ Cg) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A i f x * g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          f x * Work.UBBInputs8.boxQInd V A i g x := by
  have hQfm : Measurable (Work.UBBInputs8.boxQInd V A i f) :=
    measurable_boxQInd_bdd V hA i hfm
  have hQgm : Measurable (Work.UBBInputs8.boxQInd V A i g) :=
    measurable_boxQInd_bdd V hA i hgm
  have hQfb := abs_boxQInd_le_two (V := V) hℓ hV hA hVeq hAc i hfb
  have hQgb := abs_boxQInd_le_two (V := V) hℓ hV hA hVeq hAc i hgb
  have hPfm : Measurable (Work.UBBInputs8.boxPInd V A i f) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hfm
  have hPgm : Measurable (Work.UBBInputs8.boxPInd V A i g) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hgm
  have hPfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxPInd V A i f x| ≤ Cf :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hfb
  have hPgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Work.UBBInputs8.boxPInd V A i g x| ≤ Cg :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hgb
  -- Integrability of the four products on the box
  have hI1 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxQInd V A i f x * g x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hQfm hgm hQfb hgb
  have hI2 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      f x * Work.UBBInputs8.boxQInd V A i g x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hfm hQgm hfb hQgb
  have hI3 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      f x * Work.UBBInputs8.boxPInd V A i g x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hfm hPgm hfb hPgb
  have hI4 : IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.UBBInputs8.boxPInd V A i f x * g x) (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_mul_of_bound hℓ hPfm hgm hPfb hgb
  -- The pointwise cancellation
  have hpt : ∀ x : Submission.BoseGases.X N,
      Work.UBBInputs8.boxQInd V A i f x * g x - f x * Work.UBBInputs8.boxQInd V A i g x
        = f x * Work.UBBInputs8.boxPInd V A i g x
          - Work.UBBInputs8.boxPInd V A i f x * g x :=
    fun x => boxQInd_mul_sub_mul V i f g x
  have hcongr : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i f x * g x
          - f x * Work.UBBInputs8.boxQInd V A i g x))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (f x * Work.UBBInputs8.boxPInd V A i g x
            - Work.UBBInputs8.boxPInd V A i f x * g x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact hpt x
  have hQdiff : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A i f x * g x)
      - (∫ x in Submission.BoseGases.abox N ℓ,
          f x * Work.UBBInputs8.boxQInd V A i g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd V A i f x * g x
            - f x * Work.UBBInputs8.boxQInd V A i g x) :=
    (MeasureTheory.integral_sub hI1 hI2).symm
  have hPdiff : (∫ x in Submission.BoseGases.abox N ℓ,
        f x * Work.UBBInputs8.boxPInd V A i g x)
      - (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd V A i f x * g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (f x * Work.UBBInputs8.boxPInd V A i g x
            - Work.UBBInputs8.boxPInd V A i f x * g x) :=
    (MeasureTheory.integral_sub hI3 hI4).symm
  have hSA : (∫ x in Submission.BoseGases.abox N ℓ,
        f x * Work.UBBInputs8.boxPInd V A i g x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxPInd V A i f x * g x :=
    (Work.BoseFixB1S.boxPIndSelfAdjoint (volA := V) hℓ hV hA hVeq hAc i hfm hfb hgm hgb).symm
  have hzero : (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd V A i f x * g x)
      - (∫ x in Submission.BoseGases.abox N ℓ,
          f x * Work.UBBInputs8.boxQInd V A i g x) = 0 := by
    rw [hQdiff, hcongr, ← hPdiff, hSA, sub_self]
  exact sub_eq_zero.mp hzero

end Work.BoseFixB1
