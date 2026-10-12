import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxComp
import Submission.Work.BoseFixB1S.n0IterPowersetSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-! ## 0. `GoodState` is closed under the pointwise complement -/

/-- `GoodState` (measurable, bounded on the analysis box) is closed under pointwise subtraction. -/
theorem goodState_sub {N : ℕ} {ℓ : ℝ} {ψ φ : X N → ℝ}
    (hψ : GoodState ℓ ψ) (hφ : GoodState ℓ φ) : GoodState ℓ (ψ - φ) := by
  obtain ⟨hm₁, C, hC⟩ := hψ
  obtain ⟨hm₂, D, hD⟩ := hφ
  refine ⟨hm₁.sub hm₂, max C 0 + max D 0, fun x hx => ?_⟩
  calc |(ψ - φ) x| = |ψ x - φ x| := rfl
    _ ≤ |ψ x| + |φ x| := abs_sub _ _
    _ ≤ max C 0 + max D 0 := add_le_add (le_trans (hC x hx) (le_max_left _ _))
      (le_trans (hD x hx) (le_max_left _ _))

/-- `GoodState` is closed under the single-slot complement `1 − P_{B,i}`. -/
theorem goodState_oneSub {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) := by
  obtain ⟨hm, C, hb⟩ := hΨ
  obtain ⟨hmP, CP, hbP⟩ := goodState_boxPInd hℓ hvol hA hvolA hAc i ⟨hm, C, hb⟩
  refine ⟨hm.sub hmP, C + CP, fun x hx => ?_⟩
  calc |Ψ x - UBBInputs8.boxPInd volA A i Ψ x|
      ≤ |Ψ x| + |UBBInputs8.boxPInd volA A i Ψ x| := abs_sub _ _
    _ ≤ C + CP := add_le_add (hb x hx) (hbP x hx)

/-! ## 1. Additivity and the annihilation / commutation of the complement -/

/-- **`P_j` annihilates the complement in its own slot**: `P_j (Ψ − P_jΨ) = 0` pointwise on the
analysis box (idempotence of `P_j`). -/
theorem n0IterEigen_oneSub_self_zero {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (j : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A j
        (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A j Ψ y) x = 0 := by
  obtain ⟨hm, C, hb⟩ := hΨ
  intro x hx
  have hInt₁ : IntegrableOn (fun z : E3 => Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound hℓ hA hAc j x hx hm hb
  have hInt₂ : IntegrableOn
      (fun z : E3 => UBBInputs8.boxPInd volA A j Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound hℓ hA hAc j x hx (measurable_boxPInd volA A hA j hm)
      (abs_boxPInd_le hℓ hvol hA hvolA hAc j hb)
  have hsub : UBBInputs8.boxPInd volA A j
        (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A j Ψ y) x
      = UBBInputs8.boxPInd volA A j Ψ x
        - UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A j Ψ) x := by
    rw [show (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A j Ψ y)
        = Ψ - UBBInputs8.boxPInd volA A j Ψ from rfl,
      boxPInd_sub (Φ := Ψ) (Ψ := UBBInputs8.boxPInd volA A j Ψ) volA A j x hInt₁ hInt₂]
  rw [hsub, boxPInd_idem volA A hA hvolA (ne_of_gt hvol) j Ψ, sub_self]

/-- **`P_j` commutes with the complement in another slot**: for `i ≠ j`,
`P_j (Ψ − P_iΨ) = P_jΨ − P_i(P_jΨ)` pointwise on the analysis box. -/
theorem n0IterEigen_oneSub_comm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      UBBInputs8.boxPInd volA A j
          (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) x
        = UBBInputs8.boxPInd volA A j Ψ x
          - UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
  obtain ⟨hm, C, hb⟩ := hΨ
  intro x hx
  have hInt₁ : IntegrableOn (fun z : E3 => Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound hℓ hA hAc j x hx hm hb
  have hInt₂ : IntegrableOn
      (fun z : E3 => UBBInputs8.boxPInd volA A i Ψ (Function.update x j z)) A volume :=
    slotInt_of_bound hℓ hA hAc j x hx (measurable_boxPInd volA A hA i hm)
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hb)
  have hsub : UBBInputs8.boxPInd volA A j
        (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) x
      = UBBInputs8.boxPInd volA A j Ψ x
        - UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x := by
    rw [show (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y)
        = Ψ - UBBInputs8.boxPInd volA A i Ψ from rfl,
      boxPInd_sub (Φ := Ψ) (Ψ := UBBInputs8.boxPInd volA A i Ψ) volA A j x hInt₁ hInt₂]
  rw [hsub, boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij ⟨hm, C, hb⟩ x hx]

/-! ## 2. The list induction -/

/-- **The eigen-property for an arbitrary nodup slot list.**  With
`b := fun i => decide (i ∈ S)` and `Ψ` measurable and bounded on the analysis box, the iteration
`n0Iter volA A b L Ψ` (which at the slots of `L` applies, in list order, either `P_{B,i}` — when
`i ∈ S` — or the complement `1 − P_{B,i}` — when `i ∉ S`) is an eigenvector of every `P_{B,j}`:

* if the slot `j` occurs in `L`, then `P_j` acts as the eigenvalue `1` (when `j ∈ S`) or `0`
  (when `j ∉ S`);
* if the slot `j` does not occur in `L`, then `P_j` commutes with the whole iteration. -/
theorem n0Iter_ind {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S : Finset (Fin N)) (j : Fin N) :
    ∀ L : List (Fin N), L.Nodup →
      ((j ∈ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (n0Iter volA A (fun i => decide (i ∈ S)) L Ψ) x
            = (if j ∈ S then n0Iter volA A (fun i => decide (i ∈ S)) L Ψ x else 0))
        ∧ (j ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (n0Iter volA A (fun i => decide (i ∈ S)) L Ψ) x
            = n0Iter volA A (fun i => decide (i ∈ S)) L
                (UBBInputs8.boxPInd volA A j Ψ) x)) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨?_, ?_⟩
    · intro hj
      exact absurd hj (by simp)
    · intro _ Ψ _ x _
      rfl
  | cons i l ih =>
    intro hnd
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hnd
    obtain ⟨ihC, ihD⟩ := ih hl
    refine ⟨?_, ?_⟩
    · -- (C): the slot `j` occurs in the list
      intro hj Ψ hΨ x hx
      by_cases hS : i ∈ S
      · -- the head applies `P_i`
        have hb : (fun i' : Fin N => decide (i' ∈ S)) i = true := by simp [hS]
        rw [n0IterPowersetSum_cons_true volA A (fun i' : Fin N => decide (i' ∈ S)) i l Ψ hb]
        have hΨ' : GoodState ℓ (fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) :=
          goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
        rcases List.mem_cons.mp hj with hji | hjl
        · -- `j = i`: `P_i` acts as `1`
          rw [hji] at ihD ⊢
          rw [ihD hi (fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx, if_pos hS]
          exact n0Iter_eq_of_eqOn_box hA hAc (fun i' : Fin N => decide (i' ∈ S))
            (fun y hy => congrFun (boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i Ψ) y) l x hx
        · -- `j ∈ l`: the induction hypothesis for the tail
          exact ihC hjl (fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx
      · -- the head applies the complement `1 − P_i`
        have hb : (fun i' : Fin N => decide (i' ∈ S)) i = false := by simp [hS]
        rw [n0IterPowersetSum_cons_false volA A (fun i' : Fin N => decide (i' ∈ S)) i l Ψ hb]
        have hΨ' : GoodState ℓ (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) :=
          goodState_oneSub hℓ hvol hA hvolA hAc i hΨ
        rcases List.mem_cons.mp hj with hji | hjl
        · -- `j = i`: the complement `1 − P_i` is annihilated by `P_i`
          rw [hji] at ihD ⊢
          rw [ihD hi (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx,
            if_neg hS]
          rw [n0Iter_eq_of_eqOn_box hA hAc (fun i' : Fin N => decide (i' ∈ S))
              (f := fun z : X N => UBBInputs8.boxPInd volA A i
                (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) z)
              (g := (0 : X N → ℝ))
              (fun y hy => n0IterEigen_oneSub_self_zero hℓ hvol hA hvolA hAc i hΨ y hy) l x hx,
            n0Iter_zero volA A (fun i' : Fin N => decide (i' ∈ S)) l]
          rfl
        · -- `j ∈ l`
          exact ihC hjl (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx
    · -- (D): the slot `j` does not occur in the list
      intro hj Ψ hΨ x hx
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
      have hij : i ≠ j := fun h => hj (by rw [← h]; exact List.mem_cons_self)
      by_cases hS : i ∈ S
      · have hb : (fun i' : Fin N => decide (i' ∈ S)) i = true := by simp [hS]
        rw [n0IterPowersetSum_cons_true volA A (fun i' : Fin N => decide (i' ∈ S)) i l Ψ hb,
          n0IterPowersetSum_cons_true volA A (fun i' : Fin N => decide (i' ∈ S)) i l
            (UBBInputs8.boxPInd volA A j Ψ) hb]
        have hΨ' : GoodState ℓ (fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) :=
          goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
        rw [ihD hjl (fun y : X N => UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx]
        exact n0Iter_eq_of_eqOn_box hA hAc (fun i' : Fin N => decide (i' ∈ S))
          (fun y hy => boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy) l x hx
      · have hb : (fun i' : Fin N => decide (i' ∈ S)) i = false := by simp [hS]
        rw [n0IterPowersetSum_cons_false volA A (fun i' : Fin N => decide (i' ∈ S)) i l Ψ hb,
          n0IterPowersetSum_cons_false volA A (fun i' : Fin N => decide (i' ∈ S)) i l
            (UBBInputs8.boxPInd volA A j Ψ) hb]
        have hΨ' : GoodState ℓ (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) :=
          goodState_oneSub hℓ hvol hA hvolA hAc i hΨ
        rw [ihD hjl (fun y : X N => Ψ y - UBBInputs8.boxPInd volA A i Ψ y) hΨ' x hx]
        exact n0Iter_eq_of_eqOn_box hA hAc (fun i' : Fin N => decide (i' ∈ S))
          (fun y hy => n0IterEigen_oneSub_comm hℓ hvol hA hvolA hAc hij hΨ y hy) l x hx

/-! ## 3. The requested lemma -/

theorem n0IterEigen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S : Finset (Fin N))
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x
        = (if j ∈ S then Work.BoseFixB1S.n0ProjOp volA A S Ψ x else 0) := by
  intro x hx
  obtain ⟨hC, _⟩ :=
    n0Iter_ind hℓ hvol hA hvolA hAc S j (List.ofFn (fun i : Fin N => i))
      (List.nodup_ofFn.mpr (fun a b hab => hab))
  have hres := hC (List.mem_ofFn.mpr ⟨j, rfl⟩) Ψ hΨ x hx
  unfold n0ProjOp
  exact hres

end Work.BoseFixB1S
