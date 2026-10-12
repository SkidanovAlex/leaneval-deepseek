import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxFlatAux
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
import Submission.Work.BoseFixB1S.n0ExclFunOp
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.exclFunOpAux` — the operator algebra of `exclFunOp`

Auxiliary lemmas for `Work.BoseFixB1S.exclFunOpPropsB1` (the algebraic properties of the
slot-`i`-excluded functional calculus `exclFunOp volA A i g`).  Everything here is about the
list iteration `n0Iter` (the building block of the subset idempotents `n0ProjOp`) and the FS box
projection `P_{B,i} = UBBInputs8.boxPInd volA A i`:

* `n0IterAdd` — additivity of the iteration on `GoodState` states (on the box);
* `boxPInd_slot_fib`, `n0Slot_slot_fib`, `n0IterFibComm` — the box projection in a slot `j ≠ i`
  commutes with multiplication by a function of the fibre `i`, hence so does any iteration over a
  slot list avoiding `i`;
* `n0SlotSelfAdj`, `n0IterSelfAdj` — self-adjointness of the single slot operator and of the
  iteration on `L²(abox N ℓ)`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Closure of the state class -/

/-- `GoodState` is closed under addition. -/
theorem goodState_add {N : ℕ} {ℓ : ℝ} {Φ Ψ : X N → ℝ}
    (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) : GoodState ℓ (Φ + Ψ) := by
  obtain ⟨hm₁, C, hC⟩ := hΦ
  obtain ⟨hm₂, D, hD⟩ := hΨ
  refine ⟨hm₁.add hm₂, max C 0 + max D 0, fun x hx => ?_⟩
  calc |(Φ + Ψ) x| = |Φ x + Ψ x| := rfl
    _ ≤ |Φ x| + |Ψ x| := abs_add_le _ _
    _ ≤ max C 0 + max D 0 :=
        add_le_add (le_trans (hC x hx) (le_max_left _ _))
          (le_trans (hD x hx) (le_max_left _ _))

/-- `GoodState` is closed under multiplication by a constant. -/
theorem goodState_const_mul {N : ℕ} {ℓ : ℝ} {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) (c : ℝ) :
    GoodState ℓ (fun y => c * Ψ y) := by
  obtain ⟨hm, C, hC⟩ := hΨ
  refine ⟨hm.const_mul c, |c| * max C 0, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (le_trans (hC x hx) (le_max_left _ _)) (abs_nonneg c)

/-- `GoodState` is closed under finite sums. -/
theorem goodState_finset_sum {N : ℕ} {ℓ : ℝ} {ι : Type*} (s : Finset ι)
    {F : ι → X N → ℝ} (hF : ∀ a ∈ s, GoodState ℓ (F a)) :
    GoodState ℓ (fun y => ∑ a ∈ s, F a y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨measurable_const, 0, fun x hx => by simp⟩
  | insert a s ha ih =>
    have h1 : GoodState ℓ (F a) := hF a (Finset.mem_insert_self a s)
    have h2 : GoodState ℓ (fun y => ∑ a ∈ s, F a y) :=
      ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
    have h3 : GoodState ℓ (fun y => F a y + ∑ b ∈ s, F b y) := goodState_add h1 h2
    have hfun : (fun y => ∑ b ∈ insert a s, F b y)
        = fun y => F a y + ∑ b ∈ s, F b y := by
      funext y
      rw [Finset.sum_insert ha]
    rw [hfun]
    exact h3

/-! ## 2. The box projection in another slot commutes with a fibre weight -/

/-- **The box projection does not see a fibre weight in a *different* slot.**  For `j ≠ i` the
integrand `fib ((x|j↦z) i) = fib (x i)` is constant in the integration variable, so it factors
out of the slot mean (`integral_const_mul`).  Pointwise, for every `x`. -/
theorem boxPInd_slot_fib {N : ℕ} (volA : ℝ) (A : Set E3) {i j : Fin N} (hij : i ≠ j)
    (fib : E3 → ℝ) (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxPInd volA A j (fun y => fib (y i) * Ψ y) x
      = fib (x i) * UBBInputs8.boxPInd volA A j Ψ x := by
  have h : (∫ z in A, fib ((Function.update x j z) i) * Ψ (Function.update x j z))
      = fib (x i) * ∫ z in A, Ψ (Function.update x j z) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    have h1 : (Function.update x j z) i = x i := by
      rw [Function.update_apply, if_neg]
      exact fun hc => hij hc
    rw [h1]
  rw [Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxPInd, h]
  ring

/-- The same statement at the level of the single-slot operator `n0Slot`. -/
theorem n0Slot_slot_fib {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) {i j : Fin N}
    (hij : j ≠ i) (fib : E3 → ℝ) (Ψ : X N → ℝ) (x : X N) :
    n0Slot volA A b j (fun y => fib (y i) * Ψ y) x
      = fib (x i) * n0Slot volA A b j Ψ x := by
  by_cases hbj : b j = true
  · rw [n0Slot_apply_true volA A b j (fun y => fib (y i) * Ψ y) hbj x,
      n0Slot_apply_true volA A b j Ψ hbj x]
    exact boxPInd_slot_fib volA A hij.symm fib Ψ x
  · have hbf : b j = false := by cases hb : b j <;> simp_all
    rw [n0Slot_apply_false volA A b j (fun y => fib (y i) * Ψ y) hbf x,
      n0Slot_apply_false volA A b j Ψ hbf x]
    show fib (x i) * Ψ x - UBBInputs8.boxPInd volA A j (fun y => fib (y i) * Ψ y) x
      = fib (x i) * (Ψ x - UBBInputs8.boxPInd volA A j Ψ x)
    rw [boxPInd_slot_fib volA A hij.symm fib Ψ x]
    ring

/-! ## 3. Additivity of the iteration -/

/-- The single-slot operator is additive (pointwise on the box). -/
theorem n0Slot_add {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (b : Fin N → Bool) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0Slot volA A b i (Φ + Ψ) x = n0Slot volA A b i Φ x + n0Slot volA A b i Ψ x := by
  intro x hx
  by_cases hbi : b i = true
  · rw [n0Slot_apply_true volA A b i (Φ + Ψ) hbi x,
      n0Slot_apply_true volA A b i Φ hbi x,
      n0Slot_apply_true volA A b i Ψ hbi x]
    exact boxPInd_add volA A i x
      (slotInt_of_bound hℓ hA hAc i x hx hΦ.1 hΦ.2.choose_spec)
      (slotInt_of_bound hℓ hA hAc i x hx hΨ.1 hΨ.2.choose_spec)
  · have hbf : b i = false := by cases hb : b i <;> simp_all
    rw [n0Slot_apply_false volA A b i (Φ + Ψ) hbf x,
      n0Slot_apply_false volA A b i Φ hbf x,
      n0Slot_apply_false volA A b i Ψ hbf x]
    show Φ x + Ψ x - UBBInputs8.boxPInd volA A i (Φ + Ψ) x
      = (Φ x - UBBInputs8.boxPInd volA A i Φ x) + (Ψ x - UBBInputs8.boxPInd volA A i Ψ x)
    rw [boxPInd_add volA A i x
      (slotInt_of_bound hℓ hA hAc i x hx hΦ.1 hΦ.2.choose_spec)
      (slotInt_of_bound hℓ hA hAc i x hx hΨ.1 hΨ.2.choose_spec)]
    ring

/-- The single-slot operator only depends on the value of the branch function at its own slot. -/
theorem n0Slot_congr {N : ℕ} (volA : ℝ) (A : Set E3) {b b' : Fin N → Bool} {i : Fin N}
    {Ψ : X N → ℝ} (h : b i = b' i) : n0Slot volA A b i Ψ = n0Slot volA A b' i Ψ := by
  by_cases hb : b i = true
  · rw [n0Slot_eq_true volA A b i Ψ hb,
      n0Slot_eq_true volA A b' i Ψ (by rw [← h]; exact hb)]
  · have hf : b i = false := by cases hh : b i <;> simp_all
    rw [n0Slot_eq_false volA A b i Ψ hf,
      n0Slot_eq_false volA A b' i Ψ (by rw [← h]; exact hf)]

/-- **Additivity of the slot iteration** on the analysis box. -/
theorem n0IterAdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (b : Fin N → Bool) :
    ∀ (L : List (Fin N)) (Φ Ψ : X N → ℝ), GoodState ℓ Φ → GoodState ℓ Ψ →
      ∀ x ∈ abox N ℓ, n0Iter volA A b L (Φ + Ψ) x
        = n0Iter volA A b L Φ x + n0Iter volA A b L Ψ x := by
  intro L
  induction L with
  | nil => intro Φ Ψ _ _ x _; rfl
  | cons i l ih =>
    intro Φ Ψ hΦ hΨ x hx
    rw [n0Iter_cons, n0Iter_cons, n0Iter_cons]
    have hΦ' : GoodState ℓ (n0Slot volA A b i Φ) :=
      goodState_n0Slot hℓ hvol hA hvolA hAc b i hΦ
    have hΨ' : GoodState ℓ (n0Slot volA A b i Ψ) :=
      goodState_n0Slot hℓ hvol hA hvolA hAc b i hΨ
    have hagree : ∀ y ∈ abox N ℓ,
        n0Slot volA A b i (Φ + Ψ) y
          = (n0Slot volA A b i Φ + n0Slot volA A b i Ψ) y :=
      fun y hy => n0Slot_add hℓ hvol hA hvolA hAc b i hΦ hΨ y hy
    rw [n0Iter_eq_of_eqOn_box hA hAc b
      (f := n0Slot volA A b i (Φ + Ψ))
      (g := n0Slot volA A b i Φ + n0Slot volA A b i Ψ) hagree l x hx,
      ih (n0Slot volA A b i Φ) (n0Slot volA A b i Ψ) hΦ' hΨ' x hx]

/-! ## 4. Fibre commutation for a slot-`i`-free list -/

/-- **The fibre weight `fib (· i)` passes through an iteration that avoids the slot `i`.** -/
theorem n0IterFibComm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : E3 → ℝ} (hfibm : Measurable fib) {Cf : ℝ}
    (hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf)
    (i : Fin N) (b : Fin N → Bool) :
    ∀ (L : List (Fin N)), i ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ →
      ∀ x ∈ abox N ℓ, n0Iter volA A b L (fun y => fib (y i) * Ψ y) x
        = fib (x i) * n0Iter volA A b L Ψ x := by
  intro L
  induction L with
  | nil => intro _ Ψ _ x _; rfl
  | cons j l ih =>
    intro hj Ψ hΨ x hx
    have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
    have hil : i ∉ l := fun h => hj (List.mem_of_mem_tail h)
    rw [n0Iter_cons, n0Iter_cons]
    have hagree : ∀ y ∈ abox N ℓ,
        n0Slot volA A b j (fun y => fib (y i) * Ψ y) y
          = (fun y => fib (y i) * n0Slot volA A b j Ψ y) y :=
      fun y hy => n0Slot_slot_fib volA A b hji fib Ψ y
    rw [n0Iter_eq_of_eqOn_box hA hAc b
      (f := n0Slot volA A b j (fun y => fib (y i) * Ψ y))
      (g := fun y => fib (y i) * n0Slot volA A b j Ψ y) hagree l x hx]
    exact ih hil (n0Slot volA A b j Ψ)
      (goodState_n0Slot hℓ hvol hA hvolA hAc b j hΨ) x hx

/-! ## 5. Linearity of the iteration over a weighted finite sum -/

/-- The box projection is homogeneous (unconditional). -/
theorem boxPInd_const_mul {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (c : ℝ)
    (Ψ : X N → ℝ) (x : X N) :
    UBBInputs8.boxPInd volA A i (fun y => c * Ψ y) x
      = c * UBBInputs8.boxPInd volA A i Ψ x := by
  have h : (∫ z in A, (fun y : X N => c * Ψ y) (Function.update x i z))
      = c * ∫ z in A, Ψ (Function.update x i z) := by
    simp only []
    rw [MeasureTheory.integral_const_mul]
  rw [Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxPInd, h]
  ring

/-- The single-slot operator is homogeneous. -/
theorem n0Slot_const_mul {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (c : ℝ) (Ψ : X N → ℝ) (x : X N) :
    n0Slot volA A b i (fun y => c * Ψ y) x = c * n0Slot volA A b i Ψ x := by
  by_cases hbi : b i = true
  · rw [n0Slot_apply_true volA A b i (fun y => c * Ψ y) hbi x,
      n0Slot_apply_true volA A b i Ψ hbi x]
    exact boxPInd_const_mul volA A i c Ψ x
  · have hbf : b i = false := by cases hb : b i <;> simp_all
    rw [n0Slot_apply_false volA A b i (fun y => c * Ψ y) hbf x,
      n0Slot_apply_false volA A b i Ψ hbf x]
    show c * Ψ x - UBBInputs8.boxPInd volA A i (fun y => c * Ψ y) x
      = c * (Ψ x - UBBInputs8.boxPInd volA A i Ψ x)
    rw [boxPInd_const_mul volA A i c Ψ x]
    ring

/-- The single-slot operator is linear over a weighted finite sum (pointwise on the box). -/
theorem n0Slot_finset_sum {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {F : ι → X N → ℝ} (hF : ∀ a ∈ s, GoodState ℓ (F a)) :
    ∀ x ∈ abox N ℓ, n0Slot volA A b i (fun y => ∑ a ∈ s, c a * F a y) x
      = ∑ a ∈ s, c a * n0Slot volA A b i (F a) x := by
  intro x hx
  by_cases hbi : b i = true
  · rw [n0Slot_apply_true volA A b i (fun y => ∑ a ∈ s, c a * F a y) hbi x]
    have hcongr : (∑ a ∈ s, c a * n0Slot volA A b i (F a) x)
        = ∑ a ∈ s, c a * UBBInputs8.boxPInd volA A i (F a) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [n0Slot_apply_true volA A b i (F a) hbi x]
    rw [hcongr]
    have hP : UBBInputs8.boxPInd volA A i (fun y => ∑ a ∈ s, c a * F a y) x
        = ∑ a ∈ s, UBBInputs8.boxPInd volA A i (fun y => c a * F a y) x :=
      boxPInd_finset_sum_gen volA A i x s (fun a => fun y => c a * F a y)
        (fun a ha => slotInt_of_bound hℓ hA hAc i x hx
          (goodState_const_mul (hF a ha) (c a)).1
          (goodState_const_mul (hF a ha) (c a)).2.choose_spec)
    rw [hP]
    apply Finset.sum_congr rfl
    intro a ha
    rw [boxPInd_const_mul volA A i (c a) (F a) x]
  · have hbf : b i = false := by cases hb : b i <;> simp_all
    rw [n0Slot_apply_false volA A b i (fun y => ∑ a ∈ s, c a * F a y) hbf x]
    have hcongr : (∑ a ∈ s, c a * n0Slot volA A b i (F a) x)
        = ∑ a ∈ s, c a * (F a x - UBBInputs8.boxPInd volA A i (F a) x) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [n0Slot_apply_false volA A b i (F a) hbf x]
    rw [hcongr]
    have hP : UBBInputs8.boxPInd volA A i (fun y => ∑ a ∈ s, c a * F a y) x
        = ∑ a ∈ s, c a * UBBInputs8.boxPInd volA A i (F a) x := by
      rw [boxPInd_finset_sum_gen volA A i x s (fun a => fun y => c a * F a y)
        (fun a ha => slotInt_of_bound hℓ hA hAc i x hx
          (goodState_const_mul (hF a ha) (c a)).1
          (goodState_const_mul (hF a ha) (c a)).2.choose_spec)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [boxPInd_const_mul volA A i (c a) (F a) x]
    show (∑ a ∈ s, c a * F a x) - UBBInputs8.boxPInd volA A i (fun y => ∑ a ∈ s, c a * F a y) x
      = ∑ a ∈ s, c a * (F a x - UBBInputs8.boxPInd volA A i (F a) x)
    rw [hP]
    have hR : (∑ a ∈ s, c a * (F a x - UBBInputs8.boxPInd volA A i (F a) x))
        = ∑ a ∈ s, (c a * F a x - c a * UBBInputs8.boxPInd volA A i (F a) x) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    rw [hR, Finset.sum_sub_distrib]

/-- **Linearity of the slot iteration over a weighted finite sum** (pointwise on the box). -/
theorem n0IterFinsetSum {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (b : Fin N → Bool) :
    ∀ (L : List (Fin N)) (F : ι → X N → ℝ), (∀ a ∈ s, GoodState ℓ (F a)) →
      ∀ x ∈ abox N ℓ, n0Iter volA A b L (fun y => ∑ a ∈ s, c a * F a y) x
        = ∑ a ∈ s, c a * n0Iter volA A b L (F a) x := by
  intro L
  induction L with
  | nil => intro F _ x _; rfl
  | cons i l ih =>
    intro F hF x hx
    rw [n0Iter_cons]
    have hpt : ∀ y ∈ abox N ℓ,
        n0Slot volA A b i (fun y => ∑ a ∈ s, c a * F a y) y
          = (fun y => ∑ a ∈ s, c a * n0Slot volA A b i (F a) y) y :=
      fun y hy => n0Slot_finset_sum hℓ hvol hA hvolA hAc b i s c hF y hy
    rw [n0Iter_eq_of_eqOn_box hA hAc b
      (f := n0Slot volA A b i (fun y => ∑ a ∈ s, c a * F a y))
      (g := fun y => ∑ a ∈ s, c a * n0Slot volA A b i (F a) y) hpt l x hx]
    have hB : (∑ a ∈ s, c a * n0Iter volA A b (i :: l) (F a) x)
        = ∑ a ∈ s, c a * n0Iter volA A b l (n0Slot volA A b i (F a)) x := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [n0Iter_cons]
    rw [hB]
    exact ih (fun a => n0Slot volA A b i (F a))
      (fun a ha => goodState_n0Slot hℓ hvol hA hvolA hAc b i (hF a ha)) x hx

/-! ## 6. Self-adjointness of the iteration -/

/-- **Commutation of two slot operators at distinct slots.** -/
theorem n0Slot_comm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ}
    (hΨ : GoodState ℓ Ψ) :
    ∀ x ∈ abox N ℓ,
      n0Slot volA A b i (n0Slot volA A b j Ψ) x = n0Slot volA A b j (n0Slot volA A b i Ψ) x := by
  intro x hx
  have hPi : GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  have hPj : GoodState ℓ (UBBInputs8.boxPInd volA A j Ψ) :=
    goodState_boxPInd hℓ hvol hA hvolA hAc j hΨ
  have hcomm : UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x
      = UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x :=
    boxPInd_boxPInd_comm_good hℓ hvol hA hvolA hAc hij.symm hΨ x hx
  by_cases hi : b i = true
  · by_cases hj : b j = true
    · have hL : n0Slot volA A b i (n0Slot volA A b j Ψ) x
          = UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
        rw [n0Slot_apply_true volA A b i (n0Slot volA A b j Ψ) hi x,
          n0Slot_eq_true volA A b j Ψ hj]
      have hR : n0Slot volA A b j (n0Slot volA A b i Ψ) x
          = UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x := by
        rw [n0Slot_apply_true volA A b j (n0Slot volA A b i Ψ) hj x,
          n0Slot_eq_true volA A b i Ψ hi]
      rw [hL, hR, hcomm]
    · have hj' : b j = false := by cases h : b j <;> simp_all
      have hL : n0Slot volA A b i (n0Slot volA A b j Ψ) x
          = UBBInputs8.boxPInd volA A i (Ψ - UBBInputs8.boxPInd volA A j Ψ) x := by
        rw [n0Slot_apply_true volA A b i (n0Slot volA A b j Ψ) hi x,
          n0Slot_eq_false volA A b j Ψ hj']
      have hR : n0Slot volA A b j (n0Slot volA A b i Ψ) x
          = UBBInputs8.boxPInd volA A i Ψ x
            - UBBInputs8.boxPInd volA A j (UBBInputs8.boxPInd volA A i Ψ) x := by
        rw [n0Slot_apply_false volA A b j (n0Slot volA A b i Ψ) hj' x,
          n0Slot_eq_true volA A b i Ψ hi]
      rw [hL, hR,
        boxPInd_sub volA A i x
          (slotInt_of_bound hℓ hA hAc i x hx hΨ.1 hΨ.2.choose_spec)
          (slotInt_of_bound hℓ hA hAc i x hx hPj.1 hPj.2.choose_spec),
        hcomm]
  · have hi' : b i = false := by cases h : b i <;> simp_all
    by_cases hj : b j = true
    · have hL : n0Slot volA A b i (n0Slot volA A b j Ψ) x
          = UBBInputs8.boxPInd volA A j Ψ x
            - UBBInputs8.boxPInd volA A i (UBBInputs8.boxPInd volA A j Ψ) x := by
        rw [n0Slot_apply_false volA A b i (n0Slot volA A b j Ψ) hi' x,
          n0Slot_eq_true volA A b j Ψ hj]
      have hR : n0Slot volA A b j (n0Slot volA A b i Ψ) x
          = UBBInputs8.boxPInd volA A j (Ψ - UBBInputs8.boxPInd volA A i Ψ) x := by
        rw [n0Slot_apply_true volA A b j (n0Slot volA A b i Ψ) hj x,
          n0Slot_eq_false volA A b i Ψ hi']
      rw [hL, hR,
        boxPInd_sub volA A j x
          (slotInt_of_bound hℓ hA hAc j x hx hΨ.1 hΨ.2.choose_spec)
          (slotInt_of_bound hℓ hA hAc j x hx hPi.1 hPi.2.choose_spec),
        hcomm]
    · have hj' : b j = false := by cases h : b j <;> simp_all
      have hLf : n0Slot volA A b i (n0Slot volA A b j Ψ)
          = (Ψ - UBBInputs8.boxPInd volA A j Ψ)
            - UBBInputs8.boxPInd volA A i (Ψ - UBBInputs8.boxPInd volA A j Ψ) := by
        rw [n0Slot_eq_false volA A b i (n0Slot volA A b j Ψ) hi',
          n0Slot_eq_false volA A b j Ψ hj']
      have hL : n0Slot volA A b i (n0Slot volA A b j Ψ) x
          = (Ψ x - UBBInputs8.boxPInd volA A j Ψ x)
            - UBBInputs8.boxPInd volA A i (Ψ - UBBInputs8.boxPInd volA A j Ψ) x :=
        congrFun hLf x
      have hRf : n0Slot volA A b j (n0Slot volA A b i Ψ)
          = (Ψ - UBBInputs8.boxPInd volA A i Ψ)
            - UBBInputs8.boxPInd volA A j (Ψ - UBBInputs8.boxPInd volA A i Ψ) := by
        rw [n0Slot_eq_false volA A b j (n0Slot volA A b i Ψ) hj',
          n0Slot_eq_false volA A b i Ψ hi']
      have hR : n0Slot volA A b j (n0Slot volA A b i Ψ) x
          = (Ψ x - UBBInputs8.boxPInd volA A i Ψ x)
            - UBBInputs8.boxPInd volA A j (Ψ - UBBInputs8.boxPInd volA A i Ψ) x :=
        congrFun hRf x
      rw [hL, hR,
        boxPInd_sub volA A i x
          (slotInt_of_bound hℓ hA hAc i x hx hΨ.1 hΨ.2.choose_spec)
          (slotInt_of_bound hℓ hA hAc i x hx hPj.1 hPj.2.choose_spec),
        boxPInd_sub volA A j x
          (slotInt_of_bound hℓ hA hAc j x hx hΨ.1 hΨ.2.choose_spec)
          (slotInt_of_bound hℓ hA hAc j x hx hPi.1 hPi.2.choose_spec),
        hcomm]
      ring

/-- **Commutation of a slot operator with an iteration avoiding its slot.** -/
theorem n0IterSlotComm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) :
    ∀ (L : List (Fin N)), i ∉ L → ∀ Ψ : X N → ℝ, GoodState ℓ Ψ →
      ∀ x ∈ abox N ℓ, n0Iter volA A b L (n0Slot volA A b i Ψ) x
        = n0Slot volA A b i (n0Iter volA A b L Ψ) x := by
  intro L
  induction L with
  | nil => intro _ Ψ _ x _; rfl
  | cons k l ih =>
    intro hk Ψ hΨ x hx
    have hik : i ≠ k := fun h => hk (List.mem_cons.mpr (Or.inl h))
    have hil : i ∉ l := fun h => hk (List.mem_of_mem_tail h)
    rw [n0Iter_cons, n0Iter_cons]
    have hswap : ∀ y ∈ abox N ℓ,
        n0Slot volA A b k (n0Slot volA A b i Ψ) y = n0Slot volA A b i (n0Slot volA A b k Ψ) y :=
      fun y hy => (n0Slot_comm hℓ hvol hA hvolA hAc b hik hΨ y hy).symm
    rw [n0Iter_eq_of_eqOn_box hA hAc b
      (f := n0Slot volA A b k (n0Slot volA A b i Ψ))
      (g := n0Slot volA A b i (n0Slot volA A b k Ψ)) hswap l x hx]
    exact ih hil (n0Slot volA A b k Ψ)
      (goodState_n0Slot hℓ hvol hA hvolA hAc b k hΨ) x hx

/-- **Self-adjointness of the single-slot operator.** -/
theorem n0SlotSelfAdj {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦ : GoodState ℓ Φ) (hΨ : GoodState ℓ Ψ) :
    (∫ x in abox N ℓ, n0Slot volA A b i Φ x * Ψ x)
      = ∫ x in abox N ℓ, Φ x * n0Slot volA A b i Ψ x := by
  by_cases hbi : b i = true
  · rw [n0Slot_eq_true volA A b i Φ hbi, n0Slot_eq_true volA A b i Ψ hbi]
    exact boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦ.1 hΦ.2.choose_spec hΨ.1 hΨ.2.choose_spec
  · have hbf : b i = false := by cases hb : b i <;> simp_all
    rw [n0Slot_eq_false volA A b i Φ hbf, n0Slot_eq_false volA A b i Ψ hbf]
    have hPΦ : GoodState ℓ (UBBInputs8.boxPInd volA A i Φ) :=
      goodState_boxPInd hℓ hvol hA hvolA hAc i hΦ
    have hPΨ : GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) :=
      goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
    have hI1 : IntegrableOn (fun x : X N => Φ x * Ψ x) (abox N ℓ) volume :=
      integrableOn_mul_goodState hℓ hΦ hΨ
    have hI2 : IntegrableOn (fun x : X N => UBBInputs8.boxPInd volA A i Φ x * Ψ x)
        (abox N ℓ) volume := integrableOn_mul_goodState hℓ hPΦ hΨ
    have hI3 : IntegrableOn (fun x : X N => Φ x * UBBInputs8.boxPInd volA A i Ψ x)
        (abox N ℓ) volume := integrableOn_mul_goodState hℓ hΦ hPΨ
    have hL : (∫ x in abox N ℓ, (Φ - UBBInputs8.boxPInd volA A i Φ) x * Ψ x)
        = (∫ x in abox N ℓ, Φ x * Ψ x)
          - ∫ x in abox N ℓ, UBBInputs8.boxPInd volA A i Φ x * Ψ x := by
      rw [← MeasureTheory.integral_sub hI1 hI2]
      apply setIntegral_congr_fun (abox_measurable N ℓ)
      intro x _
      simp only [Pi.sub_apply]
      ring
    have hR : (∫ x in abox N ℓ, Φ x * (Ψ - UBBInputs8.boxPInd volA A i Ψ) x)
        = (∫ x in abox N ℓ, Φ x * Ψ x)
          - ∫ x in abox N ℓ, Φ x * UBBInputs8.boxPInd volA A i Ψ x := by
      rw [← MeasureTheory.integral_sub hI1 hI3]
      apply setIntegral_congr_fun (abox_measurable N ℓ)
      intro x _
      simp only [Pi.sub_apply]
      ring
    rw [hL, hR,
      boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦ.1 hΦ.2.choose_spec hΨ.1 hΨ.2.choose_spec]

/-- **Self-adjointness of the slot iteration.** -/
theorem n0IterSelfAdj {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) :
    ∀ (L : List (Fin N)), L.Nodup → ∀ Φ Ψ : X N → ℝ, GoodState ℓ Φ → GoodState ℓ Ψ →
      (∫ x in abox N ℓ, n0Iter volA A b L Φ x * Ψ x)
        = ∫ x in abox N ℓ, Φ x * n0Iter volA A b L Ψ x := by
  intro L
  induction L with
  | nil => intro _ Φ Ψ _ _; rfl
  | cons k l ih =>
    intro hnd Φ Ψ hΦ hΨ
    obtain ⟨hkl, hl⟩ := List.nodup_cons.mp hnd
    rw [n0Iter_cons, n0Iter_cons]
    have hΦ' : GoodState ℓ (n0Slot volA A b k Φ) :=
      goodState_n0Slot hℓ hvol hA hvolA hAc b k hΦ
    have hΨl : GoodState ℓ (n0Iter volA A b l Ψ) :=
      goodState_n0Iter hℓ hvol hA hvolA hAc b l hΨ
    rw [ih hl (n0Slot volA A b k Φ) Ψ hΦ' hΨ,
      n0SlotSelfAdj hℓ hvol hA hvolA hAc b k hΦ hΨl]
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    show Φ x * n0Slot volA A b k (n0Iter volA A b l Ψ) x
      = Φ x * n0Iter volA A b l (n0Slot volA A b k Ψ) x
    rw [n0IterSlotComm hℓ hvol hA hvolA hAc b k l hkl Ψ hΨ x hx]

/-! ## 7. Regrouping a sum over all subsets into `{T, T ∪ {i}}` pairs -/

/-- **The powerset reorganisation.**  Summing a function of the subset over *all* subsets can be
regrouped into a sum over the subsets `T` avoiding `i` of the pair `{T, T ∪ {i}}`: the two subsets
of the pair receive the same coefficient. -/
theorem powersetErasePairSum {N : ℕ} (i : Fin N) (g : ℝ → ℝ) (f : Finset (Fin N) → ℝ) :
    (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0)) * f S)
      = ∑ T ∈ (Finset.univ.erase i).powerset,
          g ((T.card : ℝ)) * (f T + f (insert i T)) := by
  classical
  have hsplit := Finset.sum_powerset_insert (s := (Finset.univ.erase i : Finset (Fin N)))
    (a := i) (Finset.notMem_erase i (Finset.univ : Finset (Fin N)))
    (fun S : Finset (Fin N) => g ((S.card : ℝ) - (if i ∈ S then 1 else 0)) * f S)
  rw [Finset.insert_erase (Finset.mem_univ i), Finset.powerset_univ] at hsplit
  have hmain : (∑ S : Finset (Fin N), g ((S.card : ℝ) - (if i ∈ S then 1 else 0)) * f S)
      = (∑ T ∈ (Finset.univ.erase i).powerset, g ((T.card : ℝ)) * f T)
        + ∑ T ∈ (Finset.univ.erase i).powerset, g ((T.card : ℝ)) * f (insert i T) := by
    rw [hsplit]
    congr 1
    · apply Finset.sum_congr rfl
      intro T hT
      have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
      rw [if_neg hiT, sub_zero]
    · apply Finset.sum_congr rfl
      intro T hT
      have hiT : i ∉ T := fun h => Finset.notMem_erase i _ ((Finset.mem_powerset.mp hT) h)
      have hcard : ((insert i T).card : ℝ) = (T.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hiT, Nat.cast_add, Nat.cast_one]
      rw [if_pos (Finset.mem_insert_self i T), hcard]
      congr 1
      ring
  rw [hmain, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

/-! ## 8. Orthogonality and idempotence of the subset idempotents -/

/-- **The subset idempotents are mutually orthogonal and idempotent.** -/
theorem n0ProjOpEigenOrth {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) (S T : Finset (Fin N)) :
    ∀ x ∈ abox N ℓ,
      n0ProjOp volA A T (n0ProjOp volA A S Ψ) x
        = if T = S then n0ProjOp volA A S Ψ x else 0 := by
  have hP : GoodState ℓ (n0ProjOp volA A S Ψ) :=
    goodState_n0Iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S))
      (List.ofFn (fun i : Fin N => i)) hΨ
  have hmain : ∀ (L : List (Fin N)), L.Nodup → ∀ x ∈ abox N ℓ,
      n0Iter volA A (fun i => decide (i ∈ T)) L (n0ProjOp volA A S Ψ) x
        = if (∀ j ∈ L, (j ∈ T ↔ j ∈ S)) then n0ProjOp volA A S Ψ x else 0 := by
    intro L
    induction L with
    | nil => intro _ x _; simp only [n0Iter]; simp
    | cons k l ih =>
      intro hnd x hx
      obtain ⟨hkl, hl⟩ := List.nodup_cons.mp hnd
      have heig : UBBInputs8.boxPInd volA A k (n0ProjOp volA A S Ψ) x
          = (if k ∈ S then n0ProjOp volA A S Ψ x else 0) :=
        n0IterEigen hℓ hvol hA hvolA hAc S hΨ k x hx
      rw [n0Iter_cons]
      by_cases hks : k ∈ T ↔ k ∈ S
      · have hfix : ∀ y ∈ abox N ℓ,
            n0Slot volA A (fun i => decide (i ∈ T)) k (n0ProjOp volA A S Ψ) y
              = n0ProjOp volA A S Ψ y := by
          intro y hy
          have hb := n0IterEigen hℓ hvol hA hvolA hAc S hΨ k y hy
          by_cases hkT : k ∈ T
          · have hkS : k ∈ S := hks.mp hkT
            rw [n0Slot_apply_true volA A (fun i => decide (i ∈ T)) k _ (by simp [hkT]) y, hb,
              if_pos hkS]
          · have hkS : k ∉ S := fun h => hkT (hks.mpr h)
            rw [n0Slot_apply_false volA A (fun i => decide (i ∈ T)) k _ (by simp [hkT]) y, hb,
              if_neg hkS, sub_zero]
        rw [n0Iter_eq_of_eqOn_box hA hAc (fun i => decide (i ∈ T))
          (f := n0Slot volA A (fun i => decide (i ∈ T)) k (n0ProjOp volA A S Ψ))
          (g := n0ProjOp volA A S Ψ) hfix l x hx, ih hl x hx]
        by_cases hcond : ∀ j ∈ l, (j ∈ T ↔ j ∈ S)
        · have hcond' : ∀ j ∈ k :: l, (j ∈ T ↔ j ∈ S) := by
            intro j hj
            rcases List.mem_cons.mp hj with h | h
            · subst h; exact hks
            · exact hcond j h
          rw [if_pos hcond', if_pos hcond]
        · have hcond' : ¬ (∀ j ∈ k :: l, (j ∈ T ↔ j ∈ S)) :=
            fun h => hcond (fun j hj => h j (List.mem_cons_of_mem k hj))
          rw [if_neg hcond', if_neg hcond]
      · have hzero : ∀ y ∈ abox N ℓ,
            n0Slot volA A (fun i => decide (i ∈ T)) k (n0ProjOp volA A S Ψ) y = 0 := by
          intro y hy
          have hb := n0IterEigen hℓ hvol hA hvolA hAc S hΨ k y hy
          by_cases hkT : k ∈ T
          · have hkS : k ∉ S := fun h => hks ⟨fun _ => h, fun _ => hkT⟩
            rw [n0Slot_apply_true volA A (fun i => decide (i ∈ T)) k _ (by simp [hkT]) y, hb,
              if_neg hkS]
          · have hkS : k ∈ S := by
              by_contra h
              exact hks ⟨fun h' => absurd h' hkT, fun h' => absurd h' h⟩
            rw [n0Slot_apply_false volA A (fun i => decide (i ∈ T)) k _ (by simp [hkT]) y, hb,
              if_pos hkS, sub_self]
        rw [n0Iter_eq_of_eqOn_box hA hAc (fun i => decide (i ∈ T))
          (f := n0Slot volA A (fun i => decide (i ∈ T)) k (n0ProjOp volA A S Ψ))
          (g := 0) hzero l x hx, n0Iter_zero]
        rw [if_neg (fun h => hks (h k List.mem_cons_self))]
        rfl
  intro x hx
  have hnd : (List.ofFn (fun i : Fin N => i)).Nodup :=
    List.nodup_ofFn.mpr (fun a b h => h)
  have hcond : (∀ j ∈ List.ofFn (fun i : Fin N => i), (j ∈ T ↔ j ∈ S)) ↔ T = S := by
    constructor
    · intro h
      ext j
      exact h j (List.mem_ofFn.mpr ⟨j, rfl⟩)
    · intro h
      subst h
      intro j _
      exact Iff.rfl
  change n0Iter volA A (fun i => decide (i ∈ T)) (List.ofFn (fun i : Fin N => i))
      (n0ProjOp volA A S Ψ) x = if T = S then n0ProjOp volA A S Ψ x else 0
  rw [hmain _ hnd x hx]
  by_cases hc : (∀ j ∈ List.ofFn (fun i : Fin N => i), (j ∈ T ↔ j ∈ S))
  · rw [if_pos hc, if_pos (hcond.mp hc)]
  · rw [if_neg hc, if_neg (fun hh => hc (hcond.mpr hh))]

/-! ## 9. The paired fibre commutation -/

/-- The product of a fibre weight with a `GoodState` is a `GoodState`. -/
theorem goodState_fib_slot {N : ℕ} {ℓ : ℝ} {fib : E3 → ℝ} (hfibm : Measurable fib) {Cf : ℝ}
    (hfibb : ∀ z ∈ acube ℓ, |fib z| ≤ Cf) (i : Fin N) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    GoodState ℓ (fun y => fib (y i) * Ψ y) := by
  obtain ⟨hm, C, hb⟩ := hΨ
  refine ⟨(hfibm.comp (measurable_pi_apply i)).mul hm, max Cf 0 * max C 0, fun x hx => ?_⟩
  rw [abs_mul]
  have h1 : |fib (x i)| ≤ max Cf 0 := le_trans (hfibb _ (hx i)) (le_max_left _ _)
  have h2 : |Ψ x| ≤ max C 0 := le_trans (hb x hx) (le_max_left _ _)
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

/-- **The paired fibre commutation.**  If the two patterns `b`, `b'` agree outside the slot `i` and
take opposite branches at `i` (`b i = false`, `b' i = true`), then applying the two iterations to
`fib (· i) · Ψ` and summing is the same as multiplying the sum of the two iterations on `Ψ` by the
fibre weight.  This is what makes the `T ↔ T ∪ {i}` regrouping of `exclFunOp` commute with the
fibre weight, even though the slot-`i` projection itself does not. -/
theorem n0IterFibPair {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {fib : E3 → ℝ} (hfibm : Measurable fib) {Cf : ℝ}
    (hfibb : ∀ z ∈ acube ℓ, |fib z| ≤ Cf) (i : Fin N) {b b' : Fin N → Bool}
    (hb0 : b i = false) (hb1 : b' i = true) :
    ∀ (L : List (Fin N)), L.Nodup → (∀ j ∈ L, j ≠ i → b j = b' j) →
      ∀ Ψ : X N → ℝ, GoodState ℓ Ψ → ∀ x ∈ abox N ℓ,
        n0Iter volA A b L (fun y => fib (y i) * Ψ y) x
            + n0Iter volA A b' L (fun y => fib (y i) * Ψ y) x
          = fib (x i) * (n0Iter volA A b L Ψ x + n0Iter volA A b' L Ψ x) := by
  intro L
  induction L with
  | nil => intro _ _ Ψ _ x _; simp only [n0Iter]; ring
  | cons k l ih =>
    intro hnd hagr Ψ hΨ x hx
    obtain ⟨hkl, hl⟩ := List.nodup_cons.mp hnd
    have hagrl : ∀ j ∈ l, j ≠ i → b j = b' j :=
      fun j hj hne => hagr j (List.mem_cons_of_mem k hj) hne
    have hstate : GoodState ℓ (fun y => fib (y i) * Ψ y) :=
      goodState_fib_slot hfibm hfibb i hΨ
    by_cases hki : k = i
    · -- the head is the marked slot: its projection cancels between the two patterns
      rw [hki] at hkl ⊢
      have hbcongr : ∀ X : X N → ℝ, n0Iter volA A b' l X = n0Iter volA A b l X :=
        fun X => (n0Iter_congr volA A l X
          (fun j hj => hagrl j hj (fun h => hkl (by rw [← h]; exact hj)))).symm
      have hRHS : fib (x i) * (n0Iter volA A b (i :: l) Ψ x + n0Iter volA A b' (i :: l) Ψ x)
          = fib (x i) * (n0Iter volA A b l (n0Slot volA A b i Ψ) x
              + n0Iter volA A b' l (n0Slot volA A b' i Ψ) x) := by
        rw [n0Iter_cons, n0Iter_cons]
      rw [hRHS]
      have hS1 : GoodState ℓ ((fun y => fib (y i) * Ψ y)
          - UBBInputs8.boxPInd volA A i (fun y => fib (y i) * Ψ y)) :=
        goodState_sub hstate (goodState_boxPInd hℓ hvol hA hvolA hAc i hstate)
      have hS2 : GoodState ℓ (UBBInputs8.boxPInd volA A i (fun y => fib (y i) * Ψ y)) :=
        goodState_boxPInd hℓ hvol hA hvolA hAc i hstate
      have hT1 : GoodState ℓ (Ψ - UBBInputs8.boxPInd volA A i Ψ) :=
        goodState_sub hΨ (goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ)
      have hT2 : GoodState ℓ (UBBInputs8.boxPInd volA A i Ψ) :=
        goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
      have hL : n0Iter volA A b l (n0Slot volA A b i (fun y => fib (y i) * Ψ y)) x
            + n0Iter volA A b' l (n0Slot volA A b' i (fun y => fib (y i) * Ψ y)) x
            = fib (x i) * n0Iter volA A b l Ψ x := by
        rw [n0Slot_eq_false volA A b i _ hb0, n0Slot_eq_true volA A b' i _ hb1, hbcongr]
        rw [← n0IterAdd hℓ hvol hA hvolA hAc b l
          ((fun y => fib (y i) * Ψ y) - UBBInputs8.boxPInd volA A i (fun y => fib (y i) * Ψ y))
          (UBBInputs8.boxPInd volA A i (fun y => fib (y i) * Ψ y)) hS1 hS2 x hx]
        rw [sub_add_cancel]
        exact n0IterFibComm hℓ hvol hA hvolA hAc hfibm hfibb i b l hkl Ψ hΨ x hx
      have hR : fib (x i) * (n0Iter volA A b l (n0Slot volA A b i Ψ) x
            + n0Iter volA A b' l (n0Slot volA A b' i Ψ) x)
            = fib (x i) * n0Iter volA A b l Ψ x := by
        rw [n0Slot_eq_false volA A b i Ψ hb0, n0Slot_eq_true volA A b' i Ψ hb1, hbcongr]
        rw [← n0IterAdd hℓ hvol hA hvolA hAc b l
          (Ψ - UBBInputs8.boxPInd volA A i Ψ) (UBBInputs8.boxPInd volA A i Ψ) hT1 hT2 x hx]
        rw [sub_add_cancel]
      conv_lhs => rw [n0Iter_cons, n0Iter_cons]
      rw [hL, hR]
    · -- the head is an ordinary slot: it commutes with the fibre weight
      have hneq : k ≠ i := hki
      have hRHS : fib (x i) * (n0Iter volA A b (k :: l) Ψ x + n0Iter volA A b' (k :: l) Ψ x)
          = fib (x i) * (n0Iter volA A b l (n0Slot volA A b k Ψ) x
              + n0Iter volA A b' l (n0Slot volA A b k Ψ) x) := by
        rw [n0Iter_cons, n0Iter_cons,
          show n0Slot volA A b' k Ψ = n0Slot volA A b k Ψ from
            (n0Slot_congr volA A (hagr k List.mem_cons_self hneq)).symm]
      have hbk : b k = b' k := hagr k List.mem_cons_self hneq
      have hX : GoodState ℓ (n0Slot volA A b k Ψ) :=
        goodState_n0Slot hℓ hvol hA hvolA hAc b k hΨ
      have hswap1 : ∀ y ∈ abox N ℓ,
          n0Slot volA A b k (fun y => fib (y i) * Ψ y) y
            = (fun y => fib (y i) * n0Slot volA A b k Ψ y) y :=
        fun y hy => n0Slot_slot_fib volA A b hneq fib Ψ y
      have hswap2 : ∀ y ∈ abox N ℓ,
          n0Slot volA A b' k (fun y => fib (y i) * Ψ y) y
            = (fun y => fib (y i) * n0Slot volA A b k Ψ y) y := by
        intro y hy
        rw [show n0Slot volA A b' k (fun y => fib (y i) * Ψ y) y
              = fib (y i) * n0Slot volA A b' k Ψ y from
            n0Slot_slot_fib volA A b' hneq fib Ψ y,
          show n0Slot volA A b' k Ψ = n0Slot volA A b k Ψ from
            (n0Slot_congr volA A hbk).symm]
      rw [hRHS]
      conv_lhs => rw [n0Iter_cons, n0Iter_cons]
      rw [n0Iter_eq_of_eqOn_box hA hAc b
          (f := n0Slot volA A b k (fun y => fib (y i) * Ψ y))
          (g := fun y => fib (y i) * n0Slot volA A b k Ψ y) hswap1 l x hx,
        n0Iter_eq_of_eqOn_box hA hAc b'
          (f := n0Slot volA A b' k (fun y => fib (y i) * Ψ y))
          (g := fun y => fib (y i) * n0Slot volA A b k Ψ y) hswap2 l x hx]
      exact ih hl hagrl (n0Slot volA A b k Ψ) hX x hx

end Work.BoseFixB1S
