import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxQInd_self_boxPInd
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxQIndSelfAdjoint
import Submission.Work.BoseFixB1S.n0SumAqEqX
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## Auxiliary pointwise facts about the box projections -/

/-- The box indicator does not see `Pᵢ` in its own slot:
`1_A(xᵢ)·(PᵢΨ)(x) = (PᵢΨ)(x)`.  Indeed `PᵢΨ = 1_A(·ᵢ)·oneMean` and `1_A` is idempotent. -/
theorem aind_mul_boxPInd {N : ℕ} (volA : ℝ) {A : Set E3} (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Aind A (x i) * Work.UBBInputs8.boxPInd volA A i Ψ x
      = Work.UBBInputs8.boxPInd volA A i Ψ x := by
  rw [boxPInd_eq volA A i Ψ x]
  rw [← mul_assoc, Aind_mul_self]

/-- **`Qᵢ` is idempotent on the box**: `Qᵢ(QᵢΨ) = QᵢΨ` for measurable `Ψ` bounded on `abox N ℓ`.

Since `QᵢΨ = 1_A(·ᵢ)Ψ − PᵢΨ` and `PᵢQᵢ = 0` (`boxPInd_boxQInd_self_zero`), we get
`Qᵢ(QᵢΨ) = 1_A(·ᵢ)·(QᵢΨ) − 0 = QᵢΨ`, the middle step being `1_A² = 1_A` together with
`1_A(·ᵢ)·Pᵢ = Pᵢ` (`aind_mul_boxPInd`). -/
theorem boxQInd_idem_on_box {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A i Ψ) x
        = Work.UBBInputs8.boxQInd volA A i Ψ x := by
  intro x hx
  have hP0 := boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i hΨ x hx
  calc Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A i Ψ) x
      = Aind A (x i) * Work.UBBInputs8.boxQInd volA A i Ψ x
          - Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A i Ψ) x :=
        boxQInd_eq volA A i (Work.UBBInputs8.boxQInd volA A i Ψ) x
    _ = Aind A (x i) * Work.UBBInputs8.boxQInd volA A i Ψ x := by rw [hP0, sub_zero]
    _ = Aind A (x i) * (Aind A (x i) * Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x) := by
        rw [boxQInd_eq volA A i Ψ x]
    _ = Aind A (x i) * Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x := by
        rw [mul_sub]
        rw [show Aind A (x i) * (Aind A (x i) * Ψ x) = Aind A (x i) * Ψ x from by
          rw [← mul_assoc, Aind_mul_self]]
        rw [aind_mul_boxPInd volA i Ψ x]
    _ = Work.UBBInputs8.boxQInd volA A i Ψ x := (boxQInd_eq volA A i Ψ x).symm

/-! ## The pairing identity -/

theorem boxQIndPInd_pairing_sq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) (i j : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x) * (Work.UBBInputs8.boxPInd volA A j Φ x) := by
  obtain ⟨hΦm, CΦ, hΦb⟩ := hΦ
  have hΦg : GoodState ℓ Φ := ⟨hΦm, CΦ, hΦb⟩
  -- `QᵢΦ`, `Pⱼ(QᵢΦ)` are measurable and bounded on the box
  have hQgood : GoodState ℓ (Work.UBBInputs8.boxQInd volA A i Φ) :=
    goodState_boxQInd hℓ hvol hA hvolA hAc i hΦg
  obtain ⟨hQm, CQ, hQb⟩ := hQgood
  have hPQm : Measurable (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ)) :=
    measurable_boxPInd volA A hA j hQm
  have hPQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ CQ :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hQb
  -- (★): the square is the pairing against `Pⱼ(QᵢΦ)`
  have hstep1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxQInd volA A i Φ x)
            * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) := by
    rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
              * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) from by
      apply integral_congr_ae
      filter_upwards with x
      rw [pow_two]]
    rw [boxPIndSelfAdjoint (ℓ := ℓ) (volA := volA) (A := A)
      (Φ := Work.UBBInputs8.boxQInd volA A i Φ)
      (Ψ := Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ))
      hℓ hvol hA hvolA hAc j hQm hQb hPQm hPQb]
    apply integral_congr_ae
    filter_upwards with x
    rw [boxPInd_idempotent hℓ hvol hA hvolA hAc j (Work.UBBInputs8.boxQInd volA A i Φ) x]
  rw [hstep1]
  by_cases hij : i = j
  · -- diagonal case: `Pᵢ(QᵢΦ) = 0` and `Qᵢ(PᵢΦ) = 0`
    rw [hij]
    have hQz : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A j Φ) = 0 :=
      funext (Work.BoseFixB1.boxQInd_self_boxPInd hvol hA hvolA j Φ)
    have hL : (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A j Φ x
            * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A j Φ) x) = 0 := by
      rw [show (∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxQInd volA A j Φ x
              * Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A j Φ) x)
          = ∫ x in Submission.BoseGases.abox N ℓ, (0 : ℝ) from
        MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          (fun x hx => by
            rw [boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc j hΦg x hx, mul_zero])]
      simp
    rw [hL]
    rw [boxQIndSelfAdjoint (ℓ := ℓ) (volA := volA) (A := A) (Φ := Φ)
        (Ψ := Work.UBBInputs8.boxPInd volA A j Φ)
        hℓ hvol hA hvolA hAc j hΦm hΦb
        (measurable_boxPInd volA A hA j hΦm) (abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb)]
    rw [hQz]
    simp
  · -- off-diagonal case: `Pⱼ` commutes with `Qᵢ`, then `Qᵢ` is an idempotent self-adjoint projection
    rw [MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        (fun x hx => by rw [boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΦg x hx])]
    rw [← boxQIndSelfAdjoint (ℓ := ℓ) (volA := volA) (A := A)
        (Φ := Work.UBBInputs8.boxQInd volA A i Φ)
        (Ψ := Work.UBBInputs8.boxPInd volA A j Φ)
        hℓ hvol hA hvolA hAc i hQm hQb
        (measurable_boxPInd volA A hA j hΦm) (abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb)]
    rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A i Φ) x
            * Work.UBBInputs8.boxPInd volA A j Φ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x from
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        (fun x hx => by rw [boxQInd_idem_on_box hℓ hvol hA hvolA hAc i hΦg x hx])]

end Work.BoseFixB1S
