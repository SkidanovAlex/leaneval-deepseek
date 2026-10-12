import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.a0FlatPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.flatPieceList_meas_bdd`

Measurability and box-boundedness of the joint `(P,Q)`-flat piece
`flatPieceList V A l S f` — the fold over the slot list `l` of the one-slot box projections
`Work.UBBInputs8.boxPInd V A i` (when `i ∈ S`) and `Work.UBBInputs8.boxQInd V A i` (when
`i ∉ S`) applied to a state `f` (`Work.BoseFixB1.a0FlatPieces`).

Both properties are inherited **slot by slot** along the list, so they are proved by induction on
`l`:

* *measurability*: `Work.BoseFixB1S.measurable_boxPInd` and
  `Work.SlotWord.measurable_boxQInd` say that `Pᵢ` and `Qᵢ` preserve measurability (no further
  hypothesis on `f`), so the induction needs nothing but `Measurable f`;
* *boundedness on the box*: the one-step estimates `Work.BoseFixB1S.abs_boxPInd_le`
  (`Pᵢ` is a contraction on `abox N ℓ`) and `abs_boxQInd_le_aux` below (`Qᵢ` costs a factor `2`)
  reduce the bound of the next fold step to the bound of the previous one, all on the same set
  `abox N ℓ`.  Each of these is *local to the box*: `PᵢΦ x` and `QᵢΦ x` for `x ∈ abox N ℓ` only
  involve `Φ` at configurations in `abox N ℓ` (the slot integral runs over `z ∈ A ⊆ acube ℓ`).

The resulting bound is `2^{#{i ∈ l}} · C`, but only its existence is recorded, as the target
statement requires.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- One step of the `Q`-bound: `|QᵢΦ| ≤ 2C` on the box whenever `|Φ| ≤ C` there.

Indeed `QᵢΦ = 1_A(x_i)·Φ - PᵢΦ` and both terms are bounded by `C` on `abox N ℓ`
(the indicator by `1`, the state by the hypothesis, and `Pᵢ` by `Work.BoseFixB1S.abs_boxPInd_le`).
No positivity of `C` is needed. -/
private theorem abs_boxQInd_le_aux {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set 𝔼3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N) {Φ : X N → ℝ} {C : ℝ}
    (hC : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) :
    ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * C := by
  intro x hx
  have hP : |Work.UBBInputs8.boxPInd V A i Φ x| ≤ C :=
    Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hC x hx
  have hσ : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    by_cases hxi : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
  have hmul : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * C :=
          mul_le_mul hσ (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have hQ : Work.UBBInputs8.boxQInd V A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        - Work.UBBInputs8.boxPInd V A i Φ x := rfl
  rw [hQ]
  calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd V A i Φ x|
      ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
        + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
    _ ≤ C + C := add_le_add hmul hP
    _ = 2 * C := by ring

/-- Measurability is preserved slot by slot. -/
private theorem flatPieceList_measurable_aux {N : ℕ} {V : ℝ} {A : Set 𝔼3}
    (hA : MeasurableSet A) (l : List (Fin N)) (S : Finset (Fin N)) {f : X N → ℝ}
    (hf : Measurable f) : Measurable (flatPieceList V A l S f) := by
  induction l with
  | nil => simpa using hf
  | cons i l ih =>
      rw [flatPieceList_cons]
      split_ifs with hi
      · exact Work.BoseFixB1S.measurable_boxPInd V A hA i ih
      · exact Work.SlotWord.measurable_boxQInd V A hA i ih

/-- The box-bound is inherited slot by slot: if `|f| ≤ C` on `abox N ℓ` then
`flatPieceList V A l S f` is bounded on `abox N ℓ` (by `2^{#{i ∈ l}} C`, the existence of a
bound being all that is claimed). -/
private theorem flatPieceList_bdd_aux {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set 𝔼3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (l : List (Fin N)) (S : Finset (Fin N))
    {f : X N → ℝ} {C : ℝ} (hfb : ∀ x ∈ abox N ℓ, |f x| ≤ C) :
    ∃ C' : ℝ, ∀ x ∈ abox N ℓ, |flatPieceList V A l S f x| ≤ C' := by
  induction l with
  | nil => exact ⟨C, hfb⟩
  | cons i l ih =>
      obtain ⟨C', hC'⟩ := ih
      rw [flatPieceList_cons]
      split_ifs with hi
      · exact ⟨C', fun x hx => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc i hC' x hx⟩
      · exact ⟨2 * C', fun x hx => abs_boxQInd_le_aux hℓ hV hA hVeq hAc i hC' x hx⟩

theorem flatPieceList_meas_bdd {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (l : List (Fin N)) (S : Finset (Fin N))
    {f : Submission.BoseGases.X N → ℝ} (hfm : Measurable f) {C : ℝ}
    (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ C) :
    Measurable (Work.BoseFixB1.flatPieceList V A l S f) ∧
      ∃ C' : ℝ, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.BoseFixB1.flatPieceList V A l S f x| ≤ C' :=
  ⟨flatPieceList_measurable_aux hA l S hfm,
   flatPieceList_bdd_aux hℓ hV hA hVeq hAc l S hfb⟩

end Work.BoseFixB1
