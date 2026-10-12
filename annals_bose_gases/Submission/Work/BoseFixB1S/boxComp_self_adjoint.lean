import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.boxQIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxComp_self_adjoint`

The joint component `boxComp volA A S = ∏_{i∈S}Pᵢ ∏_{j∉S}Qⱼ` of the FS box projections
(`Pᵢ = UBBInputs8.boxPInd`, `Qᵢ = UBBInputs8.boxQInd`, FS `eq:HBU`) is a product of
**commuting** orthogonal projections — more precisely each slot operator is self-adjoint
(`boxPIndSelfAdjoint`, `boxQIndSelfAdjoint`) and slot operators in distinct slots commute
(`boxPInd_boxPInd_comm_good`, `boxPInd_boxQInd_comm_good`, `boxQInd_boxQInd_comm_good`).
Hence `boxComp` is self-adjoint on `L²(abox N ℓ)`:

  `∫_{abox N ℓ} (boxComp S Φ)·Ψ = ∫_{abox N ℓ} Φ·(boxComp S Ψ)`

for continuous `Φ, Ψ` (compact box + `exists_abox_bound`), or more generally for states that are
measurable and bounded on the box (`GoodState`, the class of `boxPInd_boxComp`).

## Math

`boxComp volA A S = boxCompAux volA A S (List.finRange N)`, where
`boxCompAux L` is the fold `Ψ ↦ Op_{l₁}(Op_{l₂}(…(Op_{lₙ}Ψ)))` (`Op` the slot operator of `S`,
from `boxPInd_boxComp`).  The proof is an induction on the fold list with the *nodup* side
condition:

* the self-adjointness of a single slot operator (`Op_self_adjoint`) is `boxPIndSelfAdjoint`
  resp. `boxQIndSelfAdjoint`;
* the induction step peels the innermost slot operator `Op i` off the fold: the induction
  hypothesis moves it to the second argument of the pairing, `Op_self_adjoint` moves it to the
  right, and `Op_comm_fold` (`Op i` commutes with the rest of the fold for `i ∉ L`, built from
  the pairwise commutations `Op_comm_good`) puts it back on the other side.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. The slot operator of `boxComp`, case lemmas -/

/-- The slot operator is `Pᵢ` on the members of `S`. -/
theorem Op_eq_of_mem {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) (i : Fin N)
    {Ψ : X N → ℝ} (hi : i ∈ S) :
    Op volA A S i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
  funext y
  rw [Op_apply, if_pos hi]

/-- The slot operator is `Qᵢ` on the complement of `S`. -/
theorem Op_eq_of_notMem {N : ℕ} (volA : ℝ) (A : Set E3) (S : Finset (Fin N)) (i : Fin N)
    {Ψ : X N → ℝ} (hi : i ∉ S) :
    Op volA A S i Ψ = UBBInputs8.boxQInd volA A i Ψ := by
  funext y
  rw [Op_apply, if_neg hi]

/-! ## 2. Self-adjointness of a single slot operator -/

theorem Op_self_adjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (i : Fin N)
    {Φ Ψ : X N → ℝ} (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    (∫ x in abox N ℓ, Op volA A S i Φ x * Ψ x)
      = ∫ x in abox N ℓ, Φ x * Op volA A S i Ψ x := by
  obtain ⟨hΦm, CΦ, hΦb⟩ := hΦ
  obtain ⟨hΨm, CΨ, hΨb⟩ := hΨ
  by_cases hi : i ∈ S
  · rw [Op_eq_of_mem volA A S i (Ψ := Φ) hi, Op_eq_of_mem volA A S i (Ψ := Ψ) hi]
    exact boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΨm hΨb
  · rw [Op_eq_of_notMem volA A S i (Ψ := Φ) hi, Op_eq_of_notMem volA A S i (Ψ := Ψ) hi]
    exact boxQIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΨm hΨb

/-! ## 3. Pairwise commutation of the slot operators -/

/-- `QⱼQᵢ = QᵢQⱼ` on the box, for `i ≠ j` and a state measurable and bounded on the box.
Direct expansion: both sides equal `σᵢσⱼΨ − σⱼPᵢΨ − σᵢPⱼΨ + PᵢPⱼΨ` (uses `Pᵢ(σⱼΦ) = σⱼPᵢΦ`
and `PⱼPᵢ = PᵢPⱼ`). -/
theorem boxQInd_boxQInd_comm_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ, UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Ψ) x
      = UBBInputs8.boxQInd volA A i (UBBInputs8.boxQInd volA A j Ψ) x := by
  obtain ⟨hm, C, hb⟩ := hΨ
  have hgood : GoodState ℓ Ψ := ⟨hm, C, hb⟩
  intro x hx
  have hPQ : UBBInputs8.boxPInd volA A j (UBBInputs8.boxQInd volA A i Ψ) x
      = UBBInputs8.boxQInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x :=
    boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hgood x hx
  have hQP : UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A j Ψ) x
      = UBBInputs8.boxQInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x :=
    boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij.symm hgood x hx
  have hPP : UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x
      = UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x :=
    (boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hgood x hx).symm
  have hL : UBBInputs8.boxQInd volA A j (UBBInputs8.boxQInd volA A i Ψ) x
      = Aind A (x j) * (Aind A (x i) * Ψ x - UBBInputs8.boxPInd volA A i Ψ x)
        - (Aind A (x i) * UBBInputs8.boxPInd volA A j Ψ x
            - UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x) := by
    rw [boxQInd_eq volA A j (UBBInputs8.boxQInd volA A i Ψ) x, hPQ,
      boxQInd_eq volA A i (UBBInputs8.boxPInd volA A j Ψ) x,
      boxQInd_eq volA A i Ψ x]
  have hR : UBBInputs8.boxQInd volA A i (UBBInputs8.boxQInd volA A j Ψ) x
      = Aind A (x i) * (Aind A (x j) * Ψ x - UBBInputs8.boxPInd volA A j Ψ x)
        - (Aind A (x j) * UBBInputs8.boxPInd volA A i Ψ x
            - UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x) := by
    rw [boxQInd_eq volA A i (UBBInputs8.boxQInd volA A j Ψ) x, hQP,
      boxQInd_eq volA A j (UBBInputs8.boxPInd volA A i Ψ) x,
      boxQInd_eq volA A j Ψ x]
  rw [hL, hR, hPP]
  ring

/-- Distinct-slot operators commute on the box. -/
theorem Op_comm_good {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) {i l : Fin N} (hil : i ≠ l)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      Op volA A S i (Op volA A S l Ψ) x = Op volA A S l (Op volA A S i Ψ) x := by
  intro x hx
  by_cases hi : i ∈ S
  · by_cases hl : l ∈ S
    · rw [Op_eq_of_mem volA A S i hi, Op_eq_of_mem volA A S l hl,
        Op_eq_of_mem volA A S l hl, Op_eq_of_mem volA A S i hi]
      exact boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hil.symm hΨ x hx
    · rw [Op_eq_of_mem volA A S i hi, Op_eq_of_notMem volA A S l hl,
        Op_eq_of_notMem volA A S l hl, Op_eq_of_mem volA A S i hi]
      exact boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hil.symm hΨ x hx
  · by_cases hl : l ∈ S
    · rw [Op_eq_of_notMem volA A S i hi, Op_eq_of_mem volA A S l hl,
        Op_eq_of_mem volA A S l hl, Op_eq_of_notMem volA A S i hi]
      exact (boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hil hΨ x hx).symm
    · rw [Op_eq_of_notMem volA A S i hi, Op_eq_of_notMem volA A S l hl,
        Op_eq_of_notMem volA A S l hl, Op_eq_of_notMem volA A S i hi]
      exact boxQInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hil.symm hΨ x hx

/-! ## 4. The slot class is preserved by the fold -/

theorem goodState_boxCompAux {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) :
    ∀ L : List (Fin N), ∀ Ψ : X N → ℝ, GoodState ℓ Ψ →
      GoodState ℓ (boxCompAux volA A S L Ψ) := by
  intro L
  induction L with
  | nil => intro Ψ hΨ; simpa [boxCompAux_nil] using hΨ
  | cons i l ih =>
    intro Ψ hΨ
    rw [boxCompAux_cons_Op]
    exact ih (Op volA A S i Ψ) (goodState_Op hℓ hvol hA hvolA hAc S i hΨ)

/-! ## 5. Commutation of a slot operator with the fold -/

theorem Op_comm_fold {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) :
    ∀ L : List (Fin N), ∀ i : Fin N, i ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ →
      ∀ x ∈ abox N ℓ, Op volA A S i (boxCompAux volA A S L Ψ) x
        = boxCompAux volA A S L (Op volA A S i Ψ) x := by
  intro L
  induction L with
  | nil => intro i _ Ψ _ x _; rw [boxCompAux_nil, boxCompAux_nil]
  | cons l l' ih =>
    intro i hi Ψ hΨ x hx
    simp only [List.mem_cons, not_or] at hi
    obtain ⟨hil, hiL⟩ := hi
    rw [boxCompAux_cons_Op, boxCompAux_cons_Op]
    have hΨl : GoodState ℓ (Op volA A S l Ψ) := goodState_Op hℓ hvol hA hvolA hAc S l hΨ
    have hfun : ∀ y ∈ abox N ℓ,
        (Op volA A S i (Op volA A S l Ψ)) y = (Op volA A S l (Op volA A S i Ψ)) y :=
      Op_comm_good hℓ hvol hA hvolA hAc S hil hΨ
    rw [← agreeBox_boxCompAux hA hAc S l' hfun x hx]
    exact ih i hiL (Op volA A S l Ψ) hΨl x hx

/-! ## 6. Self-adjointness of the fold -/

theorem boxCompAux_self_adjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) :
    ∀ L : List (Fin N), L.Nodup → ∀ Φ Ψ : X N → ℝ, GoodState ℓ Φ → GoodState ℓ Ψ →
      (∫ x in abox N ℓ, boxCompAux volA A S L Φ x * Ψ x)
        = ∫ x in abox N ℓ, Φ x * boxCompAux volA A S L Ψ x := by
  intro L
  induction L with
  | nil => intro _ Φ Ψ _ _; simp [boxCompAux_nil]
  | cons i L ih =>
    intro hnd Φ Ψ hΦ hΨ
    obtain ⟨hiL, hLnd⟩ := List.nodup_cons.mp hnd
    rw [boxCompAux_cons_Op volA A S i L Φ, boxCompAux_cons_Op volA A S i L Ψ]
    have hgi : GoodState ℓ (Op volA A S i Φ) := goodState_Op hℓ hvol hA hvolA hAc S i hΦ
    rw [ih hLnd (Op volA A S i Φ) Ψ hgi hΨ]
    have hgF : GoodState ℓ (boxCompAux volA A S L Ψ) :=
      goodState_boxCompAux hℓ hvol hA hvolA hAc S L Ψ hΨ
    rw [Op_self_adjoint hℓ hvol hA hvolA hAc S i hΦ hgF]
    rw [show (∫ x in abox N ℓ, Φ x * Op volA A S i (boxCompAux volA A S L Ψ) x)
        = ∫ x in abox N ℓ, Φ x * boxCompAux volA A S L (Op volA A S i Ψ) x from by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (abox_measurable N ℓ)] with x hx
      rw [Op_comm_fold hℓ hvol hA hvolA hAc S L i hiL Ψ hΨ x hx]]

/-! ## 7. The target -/

theorem boxComp_self_adjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S : Finset (Fin N))
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1S.boxComp volA A S Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ, Φ x * Work.BoseFixB1S.boxComp volA A S Ψ x := by
  obtain ⟨CΦ, _hCΦ0, hCΦ⟩ := exists_abox_bound hℓ hΦc
  obtain ⟨CΨ, _hCΨ0, hCΨ⟩ := exists_abox_bound hℓ hΨc
  have hΦ : GoodState ℓ Φ := ⟨hΦc.measurable, CΦ, hCΦ⟩
  have hΨ : GoodState ℓ Ψ := ⟨hΨc.measurable, CΨ, hCΨ⟩
  rw [boxComp_eq_aux volA A S Φ, boxComp_eq_aux volA A S Ψ]
  exact boxCompAux_self_adjoint hℓ hvol hA hvolA hAc S (List.finRange N)
    (List.nodup_finRange N) Φ Ψ hΦ hΨ

end Work.BoseFixB1S
