import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPInd_boxCompT
import Submission.Work.BoseFixB1S.boxQIndSelfAdjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxCompT_orth` — orthogonality of the three-way box components

The three-way joint components

    boxCompT volA A S T Φ = (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ

(`S`, `T` the disjoint index sets of the `P`- and `Q`-slots, `Rₖ = boxOut A k` the
multiplication by `1 − 1_A(x_k)`; see `BoxSpectralDefs`) of the commuting family of FS box
projections are **pairwise orthogonal on the box**:

    ∫_{abox N ℓ} (boxCompT S T Φ)·(boxCompT S' T' Ψ) = 0      for (S,T) ≠ (S',T').

## Math

Two ingredients.

* **Support.**  If `j ∈ S ∪ T`, the operator applied in slot `j` is `Pⱼ` or `Qⱼ`, both of which
  carry the factor `1_A(x_j)`, so `boxCompT S T Φ` vanishes on `{x_j ∉ A}`; if `j ∉ S ∪ T` the
  operator is `Rⱼ = 1 − 1_A(x_j)`, so it vanishes on `{x_j ∈ A}`.  Both properties are preserved
  by the operators in every *other* slot (an average over `A` in a slot `i ≠ j` of a function
  vanishing for `x_j ∉ A` is zero because every point of the slice has `j`-th coordinate `x_j`),
  which gives the two `vanish` lemmas below.
* **The `P`-block spectral rule** (`boxPInd_boxCompT`, proved in the sibling module): the
  component `boxCompT S T Φ` is an eigenvector of every `Pⱼ`, with eigenvalue `[j ∈ S]`.

Now let `(S,T) ≠ (S',T')` be two disjoint pairs.  Their *slot types*
(`0` on `S`, `1` on `T`, `2` outside `S ∪ T`) cannot agree in every slot, so there is a slot `j`
where they differ.  Four cases:

* `j ∈ S`, `j ∉ S'`: `boxCompT S T Φ = Pⱼ(boxCompT S T Φ)` and `Pⱼ(boxCompT S' T' Ψ) = 0`; the
  pairing is `⟨PⱼX, Y⟩ = ⟨X, PⱼY⟩ = 0` by self-adjointness of `Pⱼ` (`boxPIndSelfAdjoint`).
* `j ∉ S`, `j ∈ S'`: the same with the two factors exchanged (the product is commutative).
* one slot type is `2` and the other is not: the two functions are supported on the complementary
  half-spaces `{x_j ∈ A}` / `{x_j ∉ A}`, so the product vanishes pointwise and the integral is `0`.
* the remaining coincidences of slot types contradict the choice of `j`.

The statement is the orthogonality of the joint spectral components that the sharp (operator-`√`)
completion of squares of FS `lm:appinteractionestimate` (FS l.3726–3740) needs: with it,
`⟨Φ, g(n₀)Φ⟩ = Σ_{S,T} g(|S|)·‖boxCompT S T Φ‖²` for every `g : ℕ → ℝ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The slot type of a pair `(S,T)` -/

/-- The slot type of the pair `(S,T)`: `0` on `S`, `1` on `T`, `2` outside `S ∪ T`. -/
def orthSlotType {N : ℕ} (S T : Finset (Fin N)) (j : Fin N) : ℕ :=
  if j ∈ S then 0 else if j ∈ T then 1 else 2

theorem orthSlotType_eq_zero_iff {N : ℕ} (S T : Finset (Fin N)) (j : Fin N) :
    orthSlotType S T j = 0 ↔ j ∈ S := by
  unfold orthSlotType
  by_cases hS : j ∈ S
  · simp [hS]
  · by_cases hT : j ∈ T <;> simp [hS, hT]

theorem orthSlotType_eq_one_iff {N : ℕ} {S T : Finset (Fin N)} (hST : Disjoint S T)
    (j : Fin N) : orthSlotType S T j = 1 ↔ j ∉ S ∧ j ∈ T := by
  unfold orthSlotType
  by_cases hS : j ∈ S
  · have hT : j ∉ T := Finset.disjoint_left.mp hST hS
    simp [hS, hT]
  · by_cases hT : j ∈ T <;> simp [hS, hT]

theorem orthSlotType_eq_two_iff {N : ℕ} (S T : Finset (Fin N)) (j : Fin N) :
    orthSlotType S T j = 2 ↔ j ∉ S ∧ j ∉ T := by
  unfold orthSlotType
  by_cases hS : j ∈ S
  · simp [hS]
  · by_cases hT : j ∈ T <;> simp [hS, hT]

/-- Two disjoint pairs with the same slot type in every slot are equal. -/
theorem orth_eq_of_slotType_eq {N : ℕ} {S T S' T' : Finset (Fin N)}
    (hST : Disjoint S T) (hST' : Disjoint S' T')
    (h : ∀ j : Fin N, orthSlotType S T j = orthSlotType S' T' j) :
    S = S' ∧ T = T' := by
  have hS : S = S' := by
    ext j
    rw [← orthSlotType_eq_zero_iff S T j, ← orthSlotType_eq_zero_iff S' T' j, h j]
  have hT : T = T' := by
    ext j
    constructor
    · intro hj
      have h1 : orthSlotType S T j = 1 :=
        (orthSlotType_eq_one_iff hST j).mpr ⟨Finset.disjoint_right.mp hST hj, hj⟩
      rw [h j] at h1
      exact ((orthSlotType_eq_one_iff hST' j).mp h1).2
    · intro hj
      have h1 : orthSlotType S' T' j = 1 :=
        (orthSlotType_eq_one_iff hST' j).mpr ⟨Finset.disjoint_right.mp hST' hj, hj⟩
      rw [← h j] at h1
      exact ((orthSlotType_eq_one_iff hST j).mp h1).2
  exact ⟨hS, hT⟩

/-! ## 2. The slot-vanishing predicate and its preservation -/

/-- `Ψ` vanishes at every configuration whose `j`-th slot lies in `B`. -/
def orthVanish {N : ℕ} (j : Fin N) (B : Set E3) (Ψ : X N → ℝ) : Prop :=
  ∀ x : X N, x j ∈ B → Ψ x = 0

theorem orthVanish_boxOut {N : ℕ} (A : Set E3) (i : Fin N) {j : Fin N} {B : Set E3}
    {Ψ : X N → ℝ} (hΨ : orthVanish j B Ψ) : orthVanish j B (boxOut A i Ψ) := by
  intro x hx
  rw [boxOut_apply, hΨ x hx, mul_zero]

theorem orthVanish_boxPInd {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    {B : Set E3} {Ψ : X N → ℝ} (hΨ : orthVanish j B Ψ) :
    orthVanish j B (UBBInputs8.boxPInd volA A i Ψ) := by
  intro x hx
  rw [boxPInd_eq volA A i Ψ x]
  have hzero : (∫ z in A, Ψ (Function.update x i z)) = 0 := by
    have hpt : ∀ z : E3, Ψ (Function.update x i z) = 0 := fun z => by
      apply hΨ
      rw [Function.update_apply, if_neg (Ne.symm hij)]
      exact hx
    rw [show (∫ z in A, Ψ (Function.update x i z)) = ∫ z in A, (0 : ℝ) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp
  unfold oneMean
  rw [hzero]
  ring

theorem orthVanish_boxQInd {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    {B : Set E3} {Ψ : X N → ℝ} (hΨ : orthVanish j B Ψ) :
    orthVanish j B (UBBInputs8.boxQInd volA A i Ψ) := by
  intro x hx
  have hP : UBBInputs8.boxPInd volA A i Ψ x = 0 := orthVanish_boxPInd volA A hij hΨ x hx
  rw [boxQInd_eq, hΨ x hx, mul_zero, hP, sub_zero]

/-- The operator applied in a slot different from `j` preserves slot-vanishing in slot `j`. -/
theorem orthVanish_OpT {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N)) {i j : Fin N}
    (hij : i ≠ j) {B : Set E3} {Ψ : X N → ℝ} (hΨ : orthVanish j B Ψ) :
    orthVanish j B (OpT volA A S T i Ψ) := by
  by_cases hS : i ∈ S
  · rw [OpT_eq_P hS Ψ]
    exact orthVanish_boxPInd volA A hij hΨ
  · by_cases hT : i ∈ T
    · rw [OpT_eq_Q hS hT Ψ]
      exact orthVanish_boxQInd volA A hij hΨ
    · rw [OpT_eq_R hS hT Ψ]
      exact orthVanish_boxOut A i hΨ

/-! ## 3. The seeds: the operator applied in the slot `j` itself -/

theorem orthVanish_boxPInd_self {N : ℕ} (volA : ℝ) (A : Set E3) (j : Fin N)
    (Ψ : X N → ℝ) : orthVanish j Aᶜ (UBBInputs8.boxPInd volA A j Ψ) := by
  intro x hx
  rw [boxPInd_eq volA A j Ψ x]
  have h0 : Aind A (x j) = 0 := by
    unfold Aind
    exact Set.indicator_of_notMem hx _
  rw [h0, zero_mul]

theorem orthVanish_boxQInd_self {N : ℕ} (volA : ℝ) (A : Set E3) (j : Fin N)
    (Ψ : X N → ℝ) : orthVanish j Aᶜ (UBBInputs8.boxQInd volA A j Ψ) := by
  intro x hx
  have hP : UBBInputs8.boxPInd volA A j Ψ x = 0 := orthVanish_boxPInd_self volA A j Ψ x hx
  have h0 : Aind A (x j) = 0 := by
    unfold Aind
    exact Set.indicator_of_notMem hx _
  rw [boxQInd_eq, h0, zero_mul, hP, sub_zero]

theorem orthVanish_boxOut_self {N : ℕ} (A : Set E3) (j : Fin N) (Ψ : X N → ℝ) :
    orthVanish j A (boxOut A j Ψ) := by
  intro x hx
  rw [boxOut_apply]
  have h1 : Aind A (x j) = 1 := by
    unfold Aind
    exact Set.indicator_of_mem hx _
  rw [h1, sub_self, zero_mul]

/-! ## 4. Preservation along a fold avoiding `j` -/

/-- Folding a list of slots none of which is `j` preserves slot-vanishing in slot `j`. -/
theorem orthVanish_boxCompTAux {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (j : Fin N) : ∀ (l : List (Fin N)), j ∉ l → ∀ {B : Set E3} {Ψ : X N → ℝ},
      orthVanish j B Ψ → orthVanish j B (boxCompTAux volA A S T l Ψ) := by
  intro l
  induction l with
  | nil => intro _ B Ψ hΨ; simpa using hΨ
  | cons i l ih =>
    intro hj B Ψ hΨ
    have hj' : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
    have hij : i ≠ j := fun h => hj (by rw [← h]; exact List.mem_cons_self)
    rw [boxCompTAux_cons_OpT]
    exact ih hj' (orthVanish_OpT volA A S T hij hΨ)

/-! ## 5. Slot-vanishing of the components -/

/-- The seed of the fold: the operator applied in the slot `j` itself gives slot-vanishing,
with the side (`A` or `Aᶜ`) determined by the slot type. -/
theorem orthVanish_boxCompTAux_self {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (j : Fin N) :
    ∀ (l : List (Fin N)), l.Nodup → ∀ Ψ : X N → ℝ,
      (j ∈ l → (j ∈ S ∪ T → orthVanish j Aᶜ (boxCompTAux volA A S T l Ψ))
          ∧ (j ∉ S ∪ T → orthVanish j A (boxCompTAux volA A S T l Ψ))) := by
  intro l
  induction l with
  | nil => intro _ Ψ hj; exact absurd hj (by simp)
  | cons i l ih =>
    intro hnd Ψ hj
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hnd
    rw [boxCompTAux_cons_OpT]
    rcases List.mem_cons.mp hj with hji | hjl
    · subst hji
      constructor
      · intro hST
        refine orthVanish_boxCompTAux volA A S T j l hi ?_
        by_cases hS : j ∈ S
        · rw [OpT_eq_P hS Ψ]
          exact orthVanish_boxPInd_self volA A j Ψ
        · have hT : j ∈ T := by
            rcases Finset.mem_union.mp hST with h | h
            · exact absurd h hS
            · exact h
          rw [OpT_eq_Q hS hT Ψ]
          exact orthVanish_boxQInd_self volA A j Ψ
      · intro hST
        refine orthVanish_boxCompTAux volA A S T j l hi ?_
        have hS : j ∉ S := fun h => hST (Finset.mem_union_left T h)
        have hT : j ∉ T := fun h => hST (Finset.mem_union_right S h)
        rw [OpT_eq_R hS hT Ψ]
        exact orthVanish_boxOut_self A j Ψ
    · exact ih hl (OpT volA A S T i Ψ) hjl

/-- **Off-`A` support**: if `j ∈ S ∪ T`, the component vanishes at every configuration whose
`j`-th slot lies outside `A`. -/
theorem boxComponent_vanish_off {N : ℕ} (volA : ℝ) (A : Set E3) {S T : Finset (Fin N)}
    {j : Fin N} (hj : j ∈ S ∪ T) (Φ : X N → ℝ) :
    ∀ x : X N, x j ∉ A → boxCompT volA A S T Φ x = 0 := by
  rw [boxCompT_eq_aux (N := N) volA A S T Φ]
  exact (orthVanish_boxCompTAux_self volA A S T j (List.finRange N) (List.nodup_finRange N)
    Φ (List.mem_finRange j)).1 hj

/-- **On-`A` support**: if `j ∉ S ∪ T`, the component vanishes at every configuration whose
`j`-th slot lies in `A`. -/
theorem boxComponent_vanish_on {N : ℕ} (volA : ℝ) (A : Set E3) {S T : Finset (Fin N)}
    {j : Fin N} (hj : j ∉ S ∪ T) (Φ : X N → ℝ) :
    ∀ x : X N, x j ∈ A → boxCompT volA A S T Φ x = 0 := by
  rw [boxCompT_eq_aux (N := N) volA A S T Φ]
  exact (orthVanish_boxCompTAux_self volA A S T j (List.finRange N) (List.nodup_finRange N)
    Φ (List.mem_finRange j)).2 hj

/-! ## 6. Good state, and vanishing against the complementary half-space -/

/-- A continuous state is a `GoodState` (measurable, bounded on the box). -/
theorem goodState_of_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) : GoodState ℓ Φ := by
  obtain ⟨C, hC0, hCb⟩ := exists_abox_bound hℓ hΦc
  exact ⟨hΦc.measurable, C, hCb⟩

/-- The components of a `GoodState` are `GoodState`s. -/
theorem goodState_boxCompT {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N)) {Φ : X N → ℝ} (hΦ : GoodState ℓ Φ) :
    GoodState ℓ (boxCompT volA A S T Φ) := by
  rw [boxCompT_eq_aux (N := N) volA A S T Φ]
  induction List.finRange N generalizing Φ with
  | nil => simpa using hΦ
  | cons i l ih =>
    rw [boxCompTAux_cons_OpT]
    exact ih (goodState_OpT hℓ hvol hA hvolA hAc S T i hΦ)

/-- Two functions that are supported on the complementary half-spaces `{x_j ∉ A}` and
`{x_j ∈ A}` have vanishing pairing on the box. -/
theorem integral_mul_eq_zero_of_vanish {N : ℕ} {ℓ : ℝ} {A : Set E3} {j : Fin N}
    {F G : X N → ℝ} (hF : ∀ x : X N, x j ∉ A → F x = 0)
    (hG : ∀ x : X N, x j ∈ A → G x = 0) :
    (∫ x in abox N ℓ, F x * G x) = 0 := by
  have hz : (∫ x in abox N ℓ, F x * G x) = ∫ x in abox N ℓ, (0 : X N → ℝ) x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    by_cases h : x j ∈ A
    · simp only [hG x h, mul_zero, Pi.zero_apply]
    · simp only [hF x h, zero_mul, Pi.zero_apply]
  rw [hz]
  simp

/-! ## 7. The `P`-slot case -/

/-- If `j ∈ S` and `j ∉ S'` then the two components are orthogonal. -/
theorem orth_of_mem_S {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {S T S' T' : Finset (Fin N)} {j : Fin N}
    (hjS : j ∈ S) (hjS' : j ∉ S')
    {Φ Ψ : X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, boxCompT volA A S T Φ x * boxCompT volA A S' T' Ψ x) = 0 := by
  obtain ⟨hXm, CX, hXb⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc S T (goodState_of_continuous hℓ hΦc)
  obtain ⟨hYm, CY, hYb⟩ :=
    goodState_boxCompT hℓ hvol hA hvolA hAc S' T' (goodState_of_continuous hℓ hΨc)
  have h1 : ∀ x ∈ abox N ℓ, boxCompT volA A S T Φ x
      = UBBInputs8.boxPInd volA A j (boxCompT volA A S T Φ) x := by
    intro x hx
    rw [boxPInd_boxCompT hℓ hvol hA hvolA hAc S T hΦc j x hx, if_pos hjS]
  have h2 : ∀ x ∈ abox N ℓ, UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x = 0 := by
    intro x hx
    rw [boxPInd_boxCompT hℓ hvol hA hvolA hAc S' T' hΨc j x hx, if_neg hjS']
  have hAB : (∫ x in abox N ℓ, UBBInputs8.boxPInd volA A j (boxCompT volA A S T Φ) x
        * boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, boxCompT volA A S T Φ x
          * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x :=
    boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hXm hXb hYm hYb
  calc (∫ x in abox N ℓ, boxCompT volA A S T Φ x * boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A j (boxCompT volA A S T Φ) x
          * boxCompT volA A S' T' Ψ x := by
        apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
        intro x hx
        simp only [h1 x hx]
    _ = ∫ x in abox N ℓ, boxCompT volA A S T Φ x
          * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x := hAB
    _ = 0 := by
        have hz : (∫ x in abox N ℓ, boxCompT volA A S T Φ x
              * UBBInputs8.boxPInd volA A j (boxCompT volA A S' T' Ψ) x)
            = ∫ x in abox N ℓ, (0 : X N → ℝ) x := by
          apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
          intro x hx
          simp only [h2 x hx, mul_zero, Pi.zero_apply]
        rw [hz]
        simp

/-! ## 8. The orthogonality theorem -/

theorem boxCompT_orth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T S' T' : Finset (Fin N)} (hST : Disjoint S T) (hST' : Disjoint S' T')
    (hne : S ≠ S' ∨ T ≠ T')
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (hΨc : Continuous Ψ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.boxCompT volA A S T Φ x
          * Work.BoseFixB1S.boxCompT volA A S' T' Ψ x) = 0 := by
  have hex : ∃ j : Fin N, orthSlotType S T j ≠ orthSlotType S' T' j := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := orth_eq_of_slotType_eq hST hST' hcon
    rcases hne with h | h
    · exact h h1
    · exact h h2
  obtain ⟨j, hjdif⟩ := hex
  have hswap : (∫ x in abox N ℓ, boxCompT volA A S T Φ x * boxCompT volA A S' T' Ψ x)
      = ∫ x in abox N ℓ, boxCompT volA A S' T' Ψ x * boxCompT volA A S T Φ x := by
    apply MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
    intro x hx
    ring
  by_cases hS : j ∈ S
  · by_cases hS' : j ∈ S'
    · exact absurd (by unfold orthSlotType; rw [if_pos hS, if_pos hS']) hjdif
    · exact orth_of_mem_S hℓ hvol hA hvolA hAc hS hS' hΦc hΨc
  · by_cases hS' : j ∈ S'
    · rw [hswap]
      exact orth_of_mem_S hℓ hvol hA hvolA hAc hS' hS hΨc hΦc
    · by_cases hT : j ∈ T
      · have hT' : j ∉ T' := fun h =>
          hjdif (by unfold orthSlotType; rw [if_neg hS, if_pos hT, if_neg hS', if_pos h])
        have hnot : j ∉ S' ∪ T' := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS', hT'⟩
        exact integral_mul_eq_zero_of_vanish
          (boxComponent_vanish_off volA A (Finset.mem_union_right S hT) Φ)
          (boxComponent_vanish_on volA A hnot Ψ)
      · have hT' : j ∈ T' := by
          by_contra h
          exact hjdif (by unfold orthSlotType; rw [if_neg hS, if_neg hT, if_neg hS', if_neg h])
        have hnot : j ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨hS, hT⟩
        rw [hswap]
        exact integral_mul_eq_zero_of_vanish
          (boxComponent_vanish_off volA A (Finset.mem_union_right S' hT') Ψ)
          (boxComponent_vanish_on volA A hnot Φ)

end Work.BoseFixB1S
