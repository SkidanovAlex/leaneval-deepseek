import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxPInd_boxCompT`

The **three-way** joint component

    boxCompT volA A S T Φ = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ

(see `BoxSpectralDefs`) of the commuting family of FS box projections
`Pᵢ = UBBInputs8.boxPInd volA A i`, `Qᵢ = UBBInputs8.boxQInd volA A i`, together with the
"outside" multiplication operator `Rᵢ = boxOut A i` (multiplication by `1 − 1_A(x_i)`), is an
**eigenvector of every `Pⱼ`**:

    Pⱼ (boxCompT S T Φ) = if j ∈ S then boxCompT S T Φ else 0      (pointwise on the box),

the single-slot form of "the eigenvalue of `n₀ = ΣⱼPⱼ` on the range of `boxCompT S T` is
`S.card`".  This is the three-way companion of `Work.BoseFixB1S.boxPInd_boxComp`.

## Math

The proof is the exact analogue of `boxPInd_boxComp`, with the extra slot case `Rᵢ = boxOut A i`
(the branch `i ∉ S ∪ T` of the fold).  The slot-operator facts are

* `PⱼPⱼ = Pⱼ` (`boxPInd_idem`), `PⱼQⱼ = 0` on the box (`boxPInd_boxQInd_self_zero`), and
  `PⱼRⱼ = 0` **everywhere** (`boxPInd_boxOut_self_zero` — the slot integrand of `Rⱼ` vanishes
  identically on `A`, so no hypothesis is needed);
* for `i ≠ j`: `PⱼPᵢ = PᵢPⱼ`, `PⱼQᵢ = QᵢPⱼ` (`boxPInd_boxPInd_comm_good`,
  `boxPInd_boxQInd_comm_good`) and the new `PⱼRᵢ = RᵢPⱼ` (`boxPInd_boxOut_comm`, again
  unconditional: `Rᵢ` is multiplication by a function of the *other* slot).

The fold is handled by the same mutual induction as in `boxPInd_boxComp`
(`boxCompTAux_ind`), the states staying in the class `GoodState` because each slot operator
preserves it (`goodState_OpT`, with `goodState_boxOut` the new case), and with the agreement
lemma `agreeBox_boxCompTAux` (the fold reads only the box values of its argument) taking care of
the `Q`/`R` branches, where the fold is applied to a state vanishing on the box.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The "outside" operator `Rᵢ = 1 − 1_A(x_i)` -/

/-- `Rᵢ` is multiplication by `1 − 1_A(x_i)`. -/
theorem boxOut_apply {N : ℕ} (A : Set E3) (i : Fin N) (Ψ : X N → ℝ) (x : X N) :
    boxOut A i Ψ x = (1 - Aind A (x i)) * Ψ x := rfl

theorem boxOut_zero {N : ℕ} (A : Set E3) (i : Fin N) :
    boxOut A i (0 : X N → ℝ) = 0 := by
  funext y
  rw [boxOut_apply]
  show (1 - Aind A (y i)) * (0 : ℝ) = 0
  ring

theorem measurable_boxOut {N : ℕ} {A : Set E3} (hA : MeasurableSet A) (i : Fin N)
    {Ψ : X N → ℝ} (hm : Measurable Ψ) : Measurable (boxOut A i Ψ) := by
  rw [show boxOut A i Ψ = fun y : X N => (1 - Aind A (y i)) * Ψ y from rfl]
  exact (measurable_const.sub (measurable_sigAt A hA i)).mul hm

/-- `|1 − 1_A(y)| ≤ 1` (the values of `1_A` lie in `{0,1}`). -/
theorem abs_one_sub_Aind_le_one (A : Set E3) (y : E3) : |1 - Aind A y| ≤ 1 := by
  have h1 : Aind A y ≤ 1 := (abs_le.mp (Aind_abs_le_one A y)).2
  have h0 : 0 ≤ Aind A y := Aind_nonneg A y
  rw [abs_le]
  constructor <;> linarith

theorem goodState_boxOut {N : ℕ} {ℓ : ℝ} {A : Set E3} (hA : MeasurableSet A) (i : Fin N)
    {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) : GoodState ℓ (boxOut A i Ψ) := by
  obtain ⟨hm, C, hb⟩ := hΨ
  refine ⟨measurable_boxOut hA i hm, C, ?_⟩
  intro x hx
  rw [boxOut_apply, abs_mul]
  calc |1 - Aind A (x i)| * |Ψ x| ≤ 1 * C :=
        mul_le_mul (abs_one_sub_Aind_le_one A (x i)) (hb x hx) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

/-! ## 2. `Pⱼ Rⱼ = 0` (everywhere) and `Pⱼ Rᵢ = Rᵢ Pⱼ` (for `i ≠ j`) -/

/-- The `j`-slot mean of `RⱼΨ` vanishes: the slot integrand is identically zero on `A`. -/
theorem oneMean_boxOut_self {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (j : Fin N) (Ψ : X N → ℝ) (x : X N) :
    oneMean volA A j (boxOut A j Ψ) x = 0 := by
  unfold oneMean
  have hzero : (∫ z in A, boxOut A j Ψ (Function.update x j z)) = ∫ z in A, (0 : ℝ) := by
    apply MeasureTheory.setIntegral_congr_fun hA
    intro z hz
    show boxOut A j Ψ (Function.update x j z) = 0
    rw [boxOut_apply, Function.update_self]
    have hAz : Aind A z = 1 := Set.indicator_of_mem hz (fun _ => (1 : ℝ))
    rw [hAz]
    ring
  rw [hzero, MeasureTheory.integral_zero, mul_zero]

/-- **`PⱼRⱼ = 0`**, pointwise, with no hypothesis on `Ψ`. -/
theorem boxPInd_boxOut_self_zero {N : ℕ} (volA : ℝ) (A : Set E3) (hA : MeasurableSet A)
    (j : Fin N) (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxPInd volA A j (boxOut A j Ψ) x = 0 := by
  rw [boxPInd_eq volA A j (boxOut A j Ψ) x, oneMean_boxOut_self volA A hA j Ψ x]
  ring

/-- **`PⱼRᵢ = RᵢPⱼ`** for `i ≠ j`, pointwise, with no hypothesis on `Ψ`. -/
theorem boxPInd_boxOut_comm {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxPInd volA A j (boxOut A i Ψ) x
      = boxOut A i (UBBInputs8.boxPInd volA A j Ψ) x := by
  have hone : oneMean volA A j (boxOut A i Ψ) x
      = (1 - Aind A (x i)) * oneMean volA A j Ψ x := by
    unfold oneMean
    have hcongr : (∫ z in A, boxOut A i Ψ (Function.update x j z))
        = ∫ z in A, (1 - Aind A (x i)) * Ψ (Function.update x j z) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [boxOut_apply, Function.update_apply, if_neg hij]
    rw [hcongr, MeasureTheory.integral_const_mul]
    ring
  rw [boxPInd_eq volA A j (boxOut A i Ψ) x, hone, boxOut_apply,
    boxPInd_eq volA A j Ψ x]
  ring

/-! ## 3. The slot operator of `boxCompT` and its fold -/

/-- The operator that `boxCompT` applies in slot `i`: `Pᵢ` on `S`, `Qᵢ` on `T`, `Rᵢ` outside. -/
noncomputable def OpT {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N)) (i : Fin N)
    (Ψ : X N → ℝ) : X N → ℝ :=
  if i ∈ S then UBBInputs8.boxPInd volA A i Ψ
  else if i ∈ T then UBBInputs8.boxQInd volA A i Ψ
  else boxOut A i Ψ

theorem OpT_eq_P {N : ℕ} {volA : ℝ} {A : Set E3} {S T : Finset (Fin N)} {i : Fin N}
    (hS : i ∈ S) (Ψ : X N → ℝ) :
    OpT volA A S T i Ψ = UBBInputs8.boxPInd volA A i Ψ := by
  unfold OpT
  rw [if_pos hS]

theorem OpT_eq_Q {N : ℕ} {volA : ℝ} {A : Set E3} {S T : Finset (Fin N)} {i : Fin N}
    (hS : i ∉ S) (hT : i ∈ T) (Ψ : X N → ℝ) :
    OpT volA A S T i Ψ = UBBInputs8.boxQInd volA A i Ψ := by
  unfold OpT
  rw [if_neg hS, if_pos hT]

theorem OpT_eq_R {N : ℕ} {volA : ℝ} {A : Set E3} {S T : Finset (Fin N)} {i : Fin N}
    (hS : i ∉ S) (hT : i ∉ T) (Ψ : X N → ℝ) :
    OpT volA A S T i Ψ = boxOut A i Ψ := by
  unfold OpT
  rw [if_neg hS, if_neg hT]

theorem OpT_apply {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N)) (i : Fin N)
    (Ψ : X N → ℝ) (y : X N) :
    OpT volA A S T i Ψ y
      = if i ∈ S then UBBInputs8.boxPInd volA A i Ψ y
        else if i ∈ T then UBBInputs8.boxQInd volA A i Ψ y
        else boxOut A i Ψ y := by
  by_cases hS : i ∈ S
  · rw [OpT_eq_P hS Ψ]; simp only [hS, if_true]
  · by_cases hT : i ∈ T
    · rw [OpT_eq_Q hS hT Ψ]; simp only [hS, hT, if_false, if_true]
    · rw [OpT_eq_R hS hT Ψ]; simp only [hS, hT, if_false]

/-- The fold realising `∏_{i∈S}Pᵢ ∏_{j∈T}Qⱼ ∏_{k∉S∪T}Rₖ`. -/
noncomputable def boxCompTAux {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N)) :
    List (Fin N) → (X N → ℝ) → (X N → ℝ)
  | [], Ψ => Ψ
  | i :: l, Ψ => boxCompTAux volA A S T l
      ((if i ∈ S then UBBInputs8.boxPInd volA A i
        else if i ∈ T then UBBInputs8.boxQInd volA A i
        else boxOut A i) Ψ)

@[simp] theorem boxCompTAux_nil {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (Φ : X N → ℝ) : boxCompTAux volA A S T [] Φ = Φ := rfl

theorem boxCompTAux_cons {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (i : Fin N) (l : List (Fin N)) (Φ : X N → ℝ) :
    boxCompTAux volA A S T (i :: l) Φ
      = boxCompTAux volA A S T l ((if i ∈ S then UBBInputs8.boxPInd volA A i
          else if i ∈ T then UBBInputs8.boxQInd volA A i
          else boxOut A i) Φ) := rfl

/-- The one-step unfolding of `boxCompTAux` in terms of `OpT`. -/
theorem boxCompTAux_cons_OpT {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (i : Fin N) (L : List (Fin N)) (Ψ : X N → ℝ) :
    boxCompTAux volA A S T (i :: L) Ψ = boxCompTAux volA A S T L (OpT volA A S T i Ψ) := by
  rw [boxCompTAux_cons]
  congr 1
  funext y
  rw [OpT_apply]
  by_cases hS : i ∈ S
  · simp only [hS, if_true]
  · by_cases hT : i ∈ T
    · simp only [hS, hT, if_false, if_true]
    · simp only [hS, hT, if_false]

/-- `OpT` in a slot is the zero operator. -/
theorem OpT_zero {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N)) (i : Fin N) :
    OpT volA A S T i (0 : X N → ℝ) = 0 := by
  by_cases hS : i ∈ S
  · rw [OpT_eq_P hS (0 : X N → ℝ), boxPInd_zero]
  · by_cases hT : i ∈ T
    · rw [OpT_eq_Q hS hT (0 : X N → ℝ), boxQInd_zero]
    · rw [OpT_eq_R hS hT (0 : X N → ℝ), boxOut_zero]

theorem boxCompTAux_zero {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (L : List (Fin N)) :
    boxCompTAux volA A S T L (0 : X N → ℝ) = 0 := by
  induction L with
  | nil => rfl
  | cons i l ih =>
    rw [boxCompTAux_cons_OpT, OpT_zero]
    exact ih

/-! ## 4. `boxCompT` is the fold, and `OpT` respects the `GoodState` class and the box -/

theorem boxCompT_eq_aux {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (Φ : X N → ℝ) :
    boxCompT volA A S T Φ = boxCompTAux volA A S T (List.finRange N) Φ := by
  unfold boxCompT
  induction List.finRange N generalizing Φ with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih ((if i ∈ S then UBBInputs8.boxPInd volA A i
      else if i ∈ T then UBBInputs8.boxQInd volA A i
      else boxOut A i) Φ)

theorem goodState_OpT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (i : Fin N) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) : GoodState ℓ (OpT volA A S T i Ψ) := by
  by_cases hS : i ∈ S
  · rw [OpT_eq_P hS Ψ]
    exact goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  · by_cases hT : i ∈ T
    · rw [OpT_eq_Q hS hT Ψ]
      exact goodState_boxQInd hℓ hvol hA hvolA hAc i hΨ
    · rw [OpT_eq_R hS hT Ψ]
      exact goodState_boxOut hA i hΨ

theorem agreeBox_boxOut {N : ℕ} {ℓ : ℝ} (A : Set E3) (i : Fin N) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, boxOut A i Ψ₁ y = boxOut A i Ψ₂ y := by
  intro y hy
  rw [boxOut_apply, boxOut_apply, h y hy]

theorem agreeBox_OpT {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (i : Fin N) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, OpT volA A S T i Ψ₁ y = OpT volA A S T i Ψ₂ y := by
  intro y hy
  by_cases hS : i ∈ S
  · rw [OpT_eq_P hS Ψ₁, OpT_eq_P hS Ψ₂]
    exact agreeBox_boxPInd hA hAc i h y hy
  · by_cases hT : i ∈ T
    · rw [OpT_eq_Q hS hT Ψ₁, OpT_eq_Q hS hT Ψ₂]
      exact agreeBox_boxQInd hA hAc i h y hy
    · rw [OpT_eq_R hS hT Ψ₁, OpT_eq_R hS hT Ψ₂]
      exact agreeBox_boxOut A i h y hy

/-! ## 5. The fold only reads the box values of its argument -/

theorem agreeBox_boxCompTAux {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (L : List (Fin N)) {Ψ₁ Ψ₂ : X N → ℝ}
    (h : ∀ y ∈ abox N ℓ, Ψ₁ y = Ψ₂ y) :
    ∀ y ∈ abox N ℓ, boxCompTAux volA A S T L Ψ₁ y = boxCompTAux volA A S T L Ψ₂ y := by
  induction L generalizing Ψ₁ Ψ₂ with
  | nil => simpa using h
  | cons i l ih =>
    intro y hy
    rw [boxCompTAux_cons_OpT, boxCompTAux_cons_OpT]
    exact ih (agreeBox_OpT hA hAc S T i h) y hy

/-! ## 6. The fold induction -/

theorem boxCompTAux_ind {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) (j : Fin N) :
    ∀ L : List (Fin N), L.Nodup →
      ((j ∈ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (boxCompTAux volA A S T L Ψ) x
            = (if j ∈ S then boxCompTAux volA A S T L Ψ x else 0))
        ∧ (j ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
          UBBInputs8.boxPInd volA A j (boxCompTAux volA A S T L Ψ) x
            = boxCompTAux volA A S T L (UBBInputs8.boxPInd volA A j Ψ) x)) := by
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
        · have hidem := boxPInd_idem volA A hA hvolA (ne_of_gt hvol) i Ψ
          rw [hd, OpT_eq_P hS Ψ, hidem, if_pos hS]
        · by_cases hT : i ∈ T
          · have hzero := boxPInd_boxQInd_self_zero hℓ hvol hA hvolA hAc i hΨ
            rw [hd, OpT_eq_Q hS hT Ψ, if_neg hS]
            have hagree : ∀ y ∈ abox N ℓ,
                UBBInputs8.boxPInd volA A i (UBBInputs8.boxQInd volA A i Ψ) y
                  = (0 : X N → ℝ) y := by
              intro y hy; rw [hzero y hy]; rfl
            rw [agreeBox_boxCompTAux hA hAc S T l hagree x hx, boxCompTAux_zero]
            simp
          · have hzero := boxPInd_boxOut_self_zero volA A hA i Ψ
            rw [hd, OpT_eq_R hS hT Ψ, if_neg hS]
            have hagree : ∀ y ∈ abox N ℓ,
                UBBInputs8.boxPInd volA A i (boxOut A i Ψ) y = (0 : X N → ℝ) y := by
              intro y hy; rw [hzero y]; rfl
            rw [agreeBox_boxCompTAux hA hAc S T l hagree x hx, boxCompTAux_zero]
            simp
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
      · rw [OpT_eq_P hS Ψ, OpT_eq_P hS (UBBInputs8.boxPInd volA A j Ψ)]
        exact boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy
      · by_cases hT : i ∈ T
        · rw [OpT_eq_Q hS hT Ψ, OpT_eq_Q hS hT (UBBInputs8.boxPInd volA A j Ψ)]
          exact boxPInd_boxQInd_comm_good hℓ hvol hA hvolA hAc hij hΨ y hy
        · rw [OpT_eq_R hS hT Ψ, OpT_eq_R hS hT (UBBInputs8.boxPInd volA A j Ψ)]
          exact boxPInd_boxOut_comm volA A hij Ψ y

/-! ## 7. The theorem -/

theorem boxPInd_boxCompT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (S T : Finset (Fin N))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (j : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.boxCompT volA A S T Φ) x
        = (if j ∈ S then Work.BoseFixB1S.boxCompT volA A S T Φ x else 0) := by
  intro x hx
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  have hΦgood : GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  obtain ⟨hC, _⟩ :=
    boxCompTAux_ind hℓ hvol hA hvolA hAc S T j (List.finRange N) (List.nodup_finRange N)
  have hres := hC (List.mem_finRange j) Φ hΦgood x hx
  rw [boxCompT_eq_aux]
  exact hres

end Work.BoseFixB1S
