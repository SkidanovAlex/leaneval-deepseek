import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.flatPiece_eigen
import Submission.Work.BoseFixB1S.boxComp_self_adjoint
import Submission.Work.BoseFixB1S.boxPInd_boxCompT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxQInd_boxCompT`

The **mean-free** slot component of the three-way joint component

    boxCompT volA A S T Φ = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ

(see `BoxSpectralDefs`) of the commuting family of FS box projections
`Pᵢ = UBBInputs8.boxPInd volA A i`, `Qᵢ = UBBInputs8.boxQInd volA A i`, together with the
"outside" multiplication operator `Rᵢ = boxOut A i` (multiplication by `1 − 1_A(x_i)`), is an
**eigenvector of every `Qⱼ`**:

    Qⱼ (boxCompT S T Φ) = if j ∈ T then boxCompT S T Φ else 0      (pointwise on the box),

the single-slot form of "the eigenvalue of `n₊ = ΣⱼQⱼ` on the range of `boxCompT S T Φ` is
`T.card`".  This is the companion of `Work.BoseFixB1S.boxPInd_boxCompT`, which gives the
eigenvalue of every `Pⱼ`.

## Math

`boxCompT` is a `List.foldl` over `List.finRange N` of the slot operators
`OpT i Ψ = if i ∈ S then PᵢΨ else if i ∈ T then QᵢΨ else RᵢΨ`.  The slot-operator facts used are

* `QⱼQⱼ = Qⱼ` (`Work.BoseFixB1.boxQInd_self_idem`, unconditional) — the box indicator is an
  idempotent multiplier and `PⱼQⱼ = 0`;
* `QⱼPⱼ = 0` (`boxQInd_boxPInd_self`, unconditional) and `QⱼRⱼ = 0`
  (`boxQInd_boxOut_self`, unconditional: `Rⱼ` annihilates the box indicator and `PⱼRⱼ = 0`);
* for `i ≠ j`: `QⱼQᵢ = QᵢQⱼ` (`boxQInd_boxQInd_comm_good`), `QⱼPᵢ = PᵢQⱼ`
  (`boxPInd_boxQInd_comm_good`) and the new `QⱼRᵢ = RᵢQⱼ` (`boxQInd_boxOut_comm`, again
  unconditional: `Rᵢ` is multiplication by a function of the *other* slot).

The fold is handled by the same mutual induction as in `boxPInd_boxCompT` (`boxCompTAux_indQ`),
the states staying in the class `GoodState` because each slot operator preserves it
(`goodState_OpT`), and with the agreement lemma `agreeBox_boxCompTAux` (the fold reads only the
box values of its argument) taking care of the `P`/`R` branches, where the fold is applied to a
state vanishing on the box.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. `Qᵢ Rᵢ = 0` and `Qⱼ Rᵢ = Rᵢ Qⱼ` -/

/-- **`QᵢRᵢ = 0`**, pointwise, with no hypothesis on `Ψ`: `Rᵢ` annihilates the box indicator (so
the first term of `Qᵢ = 1_A(·_i)· − Pᵢ` vanishes) and `PᵢRᵢ = 0`
(`boxPInd_boxOut_self_zero`). -/
theorem boxQInd_boxOut_self {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (i : Fin N) (Ψ : X N → ℝ) :
    UBBInputs8.boxQInd volA A i (boxOut A i Ψ) = 0 := by
  funext x
  rw [show UBBInputs8.boxQInd volA A i (boxOut A i Ψ) x
      = Aind A (x i) * boxOut A i Ψ x
        - UBBInputs8.boxPInd volA A i (boxOut A i Ψ) x from rfl,
    boxPInd_boxOut_self_zero volA A hA i Ψ x, sub_zero, boxOut_apply]
  have h1 : Aind A (x i) * (1 - Aind A (x i)) = 0 := by
    rw [mul_sub, mul_one, Aind_mul_self, sub_self]
  rw [← mul_assoc, h1, zero_mul]
  simp

/-- **`QⱼRᵢ = RᵢQⱼ`** for `i ≠ j`, pointwise, with no hypothesis on `Ψ`: `Rᵢ` is multiplication
by a function of the slot `i ≠ j`, hence commutes with the indicator factor of `Qⱼ` and with `Pⱼ`
(`boxPInd_boxOut_comm`). -/
theorem boxQInd_boxOut_comm {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxQInd volA A j (boxOut A i Ψ) x
      = boxOut A i (UBBInputs8.boxQInd volA A j Ψ) x := by
  have hL : UBBInputs8.boxQInd volA A j (boxOut A i Ψ) x
      = Aind A (x j) * ((1 - Aind A (x i)) * Ψ x)
        - (1 - Aind A (x i)) * UBBInputs8.boxPInd volA A j Ψ x := by
    rw [show UBBInputs8.boxQInd volA A j (boxOut A i Ψ) x
        = Aind A (x j) * boxOut A i Ψ x
          - UBBInputs8.boxPInd volA A j (boxOut A i Ψ) x from rfl,
      boxOut_apply, boxPInd_boxOut_comm volA A hij Ψ x, boxOut_apply]
  have hR : boxOut A i (UBBInputs8.boxQInd volA A j Ψ) x
      = (1 - Aind A (x i)) * (Aind A (x j) * Ψ x - UBBInputs8.boxPInd volA A j Ψ x) := by
    rw [boxOut_apply, show UBBInputs8.boxQInd volA A j Ψ x
        = Aind A (x j) * Ψ x - UBBInputs8.boxPInd volA A j Ψ x from rfl]
  rw [hL, hR]
  ring

/-! ## 2. The fold induction -/

theorem boxCompTAux_indQ {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (hST : Disjoint S T) (j : Fin N) :
    ∀ L : List (Fin N), L.Nodup →
      ((j ∈ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxQInd volA A j (boxCompTAux volA A S T L Ψ) x
            = (if j ∈ T then boxCompTAux volA A S T L Ψ x else 0))
        ∧ (j ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxQInd volA A j (boxCompTAux volA A S T L Ψ) x
            = boxCompTAux volA A S T L (UBBInputs8.boxQInd volA A j Ψ) x)) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨?_, ?_⟩
    · intro hj
      exact absurd hj (by simp)
    · intro _ Ψ _ x hx
      simp
  | cons i l ih =>
    intro hnd
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hnd
    obtain ⟨ihC, ihD⟩ := ih hl
    refine ⟨?_, ?_⟩
    · intro hj Ψ hΨ x hx
      rw [boxCompTAux_cons_OpT]
      have hΨ' : GoodState ℓ (OpT volA A S T i Ψ) := goodState_OpT hℓ hvol hA hvolA hAc S T i hΨ
      rcases (List.mem_cons).mp hj with hji | hjl
      · rw [hji] at ihD ⊢
        have hd := ihD hi (OpT volA A S T i Ψ) hΨ' x hx
        by_cases hS : i ∈ S
        · have hzero : UBBInputs8.boxQInd volA A i (UBBInputs8.boxPInd volA A i Ψ) = 0 :=
            funext (fun y => Work.BoseFixB1.boxQInd_self_boxPInd hvol hA hvolA i Ψ y)
          have hiT : i ∉ T := Finset.disjoint_left.mp hST hS
          rw [hd, OpT_eq_P hS Ψ, hzero, boxCompTAux_zero]
          simp [hiT]
        · by_cases hT : i ∈ T
          · have hidem : UBBInputs8.boxQInd volA A i (UBBInputs8.boxQInd volA A i Ψ)
                = UBBInputs8.boxQInd volA A i Ψ :=
              Work.BoseFixB1.boxQInd_self_idem hvol hA hvolA i Ψ
            rw [hd, OpT_eq_Q hS hT Ψ, hidem, if_pos hT]
          · have hzero : UBBInputs8.boxQInd volA A i (boxOut A i Ψ) = 0 :=
              boxQInd_boxOut_self volA A hA i Ψ
            rw [hd, OpT_eq_R hS hT Ψ, hzero, boxCompTAux_zero]
            simp [hT]
      · exact ihC hjl (OpT volA A S T i Ψ) hΨ' x hx
    · intro hj Ψ hΨ x hx
      have hjl : j ∉ l := fun h => hj ((List.mem_cons).mpr (Or.inr h))
      have hij : i ≠ j := fun h => hj ((List.mem_cons).mpr (Or.inl h.symm))
      rw [boxCompTAux_cons_OpT, boxCompTAux_cons_OpT]
      have hΨ' : GoodState ℓ (OpT volA A S T i Ψ) := goodState_OpT hℓ hvol hA hvolA hAc S T i hΨ
      rw [ihD hjl (OpT volA A S T i Ψ) hΨ' x hx]
      refine agreeBox_boxCompTAux hA hAc S T l ?_ x hx
      intro y hy
      by_cases hS : i ∈ S
      · rw [OpT_eq_P hS Ψ, OpT_eq_P hS (UBBInputs8.boxQInd volA A j Ψ)]
        exact (boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc (i := j) (j := i) hij.symm
          hΨ y hy).symm
      · by_cases hT : i ∈ T
        · rw [OpT_eq_Q hS hT Ψ, OpT_eq_Q hS hT (UBBInputs8.boxQInd volA A j Ψ)]
          exact boxQInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy
        · rw [OpT_eq_R hS hT Ψ, OpT_eq_R hS hT (UBBInputs8.boxQInd volA A j Ψ)]
          exact boxQInd_boxOut_comm volA A hij Ψ y

/-! ## 3. The theorem -/

theorem boxQInd_boxCompT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {S T : Finset (Fin N)} (hST : Disjoint S T)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxQInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ T then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦgood : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  obtain ⟨hC, _⟩ :=
    boxCompTAux_indQ hℓ hvol hA hvolA hAc S T hST j (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦgood x hx
  rw [boxCompT_eq_aux]
  exact hres

end Work.BoseFixB1S
