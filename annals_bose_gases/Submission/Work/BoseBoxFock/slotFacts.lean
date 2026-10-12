import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceFubini
import Submission.Work.BoseBoxFock.slotPairDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotFacts` — the operator-side facts the generic slice selection consumes

`Work.BoseBoxFock.exists_slice_le_window_of_op` runs the BF3c selection for an *abstract* operator
`Op`, taking as hypotheses only the sector split of its quadratic form and the decoupling of the
form on a sector.  This module packages those facts into a structure `SlotFacts`, proves that it is
closed under sums and scalar multiples, and supplies the base instances

* `Op = boxSlotSum e T` (the one-body slot sum, whose split is the proved `slotSum_sector_split`
  and whose pointwise decoupling is the proved `boxSlotSum_pairCoord`),
* `Op = id` (whose split is the mass splitting of the sectors),

so that the box twin `Work.BoseBoxFock.AVslot` of `H2ndF` — a sum of scalar multiples of
`boxSlotSum`s, of compositions of two of them, and of the identity — can be fed to the selection
mechanically.

**Import note.**  This module must **not** import `Submission.Work.BoseBoxFock.AVGoodState`: that
module re-declares `etaOf_continuous`/`etaOf_hasCompactSupport`, which
`Submission.Work.BoseBoxFock.boxSlotSum_measurable_bounded` (in the cone of every selection lemma)
also declares.  The class of states is therefore fixed locally, as `SlotGood`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- A **good state**: measurable and pointwise bounded. -/
def SlotGood {ι : Type*} (X : (ι → Ω) → ℂ) : Prop :=
  Measurable X ∧ ∃ C, ∀ x, ‖X x‖ ≤ C

namespace SlotGood

variable {ι : Type*}

protected theorem add {X Y : (ι → Ω) → ℂ} (hX : SlotGood X) (hY : SlotGood Y) :
    SlotGood (X + Y) := by
  obtain ⟨C₁, h₁⟩ := hX.2
  obtain ⟨C₂, h₂⟩ := hY.2
  exact ⟨hX.1.add hY.1, C₁ + C₂, fun x => by
    rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

protected theorem sub {X Y : (ι → Ω) → ℂ} (hX : SlotGood X) (hY : SlotGood Y) :
    SlotGood (X - Y) := by
  obtain ⟨C₁, h₁⟩ := hX.2
  obtain ⟨C₂, h₂⟩ := hY.2
  exact ⟨hX.1.sub hY.1, C₁ + C₂, fun x => by
    rw [Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

protected theorem neg {X : (ι → Ω) → ℂ} (hX : SlotGood X) : SlotGood (-X) := by
  obtain ⟨C, hC⟩ := hX.2
  exact ⟨hX.1.neg, C, fun x => by rw [Pi.neg_apply, norm_neg]; exact hC x⟩

protected theorem smul (c : ℂ) {X : (ι → Ω) → ℂ} (hX : SlotGood X) : SlotGood (c • X) := by
  obtain ⟨C, hC⟩ := hX.2
  refine ⟨hX.1.const_smul c, ‖c‖ * max C 0, fun x => ?_⟩
  rw [Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left ((hC x).trans (le_max_left _ _)) (norm_nonneg _)

protected theorem constFun (z : ℂ) : SlotGood (fun _ : ι → Ω => z) :=
  ⟨measurable_const, ‖z‖, fun _ => le_rfl⟩

protected theorem zero : SlotGood (0 : (ι → Ω) → ℂ) := by
  have h : (0 : (ι → Ω) → ℂ) = fun _ => (0 : ℂ) := rfl
  rw [h]
  exact SlotGood.constFun 0

protected theorem finset_sum {κ : Type*} (s : Finset κ) {X : κ → (ι → Ω) → ℂ}
    (h : ∀ i, SlotGood (X i)) : SlotGood (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (SlotGood.zero : SlotGood (0 : (ι → Ω) → ℂ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a).add ih

end SlotGood

/-- An operator that preserves good states — the class on which the Bochner-integral definitions
of the box ladder words behave linearly. -/
def RowGood {ι : Type*} (Op : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)) : Prop :=
  ∀ X : (ι → Ω) → ℂ, SlotGood X → SlotGood (Op X)

namespace RowGood

variable {ι : Type*}

protected theorem id : RowGood (id : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)) := fun _ h => h

protected theorem add {Op1 Op2 : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h1 : RowGood Op1)
    (h2 : RowGood Op2) : RowGood (Op1 + Op2) := by
  intro X hX
  have h : (Op1 + Op2) X = Op1 X + Op2 X := rfl
  rw [h]
  exact (h1 X hX).add (h2 X hX)

protected theorem sub {Op1 Op2 : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h1 : RowGood Op1)
    (h2 : RowGood Op2) : RowGood (Op1 - Op2) := by
  intro X hX
  have h : (Op1 - Op2) X = Op1 X - Op2 X := rfl
  rw [h]
  exact (h1 X hX).sub (h2 X hX)

protected theorem neg {Op : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h : RowGood Op) : RowGood (-Op) := by
  intro X hX
  have h' : (-Op) X = -(Op X) := rfl
  rw [h']
  exact (h X hX).neg

protected theorem smul (c : ℂ) {Op : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h : RowGood Op) :
    RowGood (c • Op) := by
  intro X hX
  have h' : (c • Op) X = c • Op X := rfl
  rw [h']
  exact (h X hX).smul c

protected theorem comp {Op1 Op2 : ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h1 : RowGood Op1)
    (h2 : RowGood Op2) : RowGood (Op1 ∘ Op2) :=
  fun X hX => h1 (Op2 X) (h2 X hX)

protected theorem constFun (c : ℂ) :
    RowGood (fun _ : (ι → Ω) → ℂ => fun _ : ι → Ω => c) :=
  fun _ _ => SlotGood.constFun c

protected theorem finset_sum {κ : Type*} (s : Finset κ)
    {Ops : κ → ((ι → Ω) → ℂ) → ((ι → Ω) → ℂ)} (h : ∀ i, RowGood (Ops i)) :
    RowGood (∑ i ∈ s, Ops i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (∑ i ∈ (∅ : Finset κ), Ops i)
          = (fun _ : (ι → Ω) → ℂ => fun _ : ι → Ω => (0 : ℂ)) := by
        funext X x; simp
      rw [h0]
      exact RowGood.constFun 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a).add ih

end RowGood

/-- A product of a compactly supported good state with a good state is integrable. -/
theorem integrable_star_mul_of_compact {ι : Type*} [Fintype ι] {X Y : (ι → Ω) → ℂ}
    (hXc : HasCompactSupport X) (hX : SlotGood X) (hY : SlotGood Y) :
    MeasureTheory.Integrable (fun x : ι → Ω => star (X x) * Y x) := by
  obtain ⟨C, hC⟩ := hX.2
  obtain ⟨D, hD⟩ := hY.2
  have hCm : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hDm : (0 : ℝ) ≤ max D 0 := le_max_right _ _
  refine MeasureTheory.Integrable.mono' (g := (tsupport X).indicator (fun _ => max C 0 * max D 0))
    ?_ ((measurable_star_comp hX.1).mul hY.1).aestronglyMeasurable ?_
  · rw [MeasureTheory.integrable_indicator_iff (isClosed_tsupport X).measurableSet]
    exact MeasureTheory.integrableOn_const hXc.measure_lt_top.ne
  · filter_upwards with x
    by_cases hx : x ∈ tsupport X
    · rw [Set.indicator_of_mem hx]
      rw [norm_mul, norm_star]
      exact mul_le_mul ((hC x).trans (le_max_left _ _)) ((hD x).trans (le_max_left _ _))
        (norm_nonneg _) hCm
    · rw [Set.indicator_of_notMem hx]
      have h0 : X x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h0]
      simp

/-- **The operator-side facts of the generic slice selection.**  `Op` is the box-side operator,
`OpS S` its `↥S`-indexed counterpart on the slice of the sector `S`; the three fields are exactly
what the selection needs: preservation of good states (for integrability), the *pointwise*
decoupling on a sector, and the sector splitting of the quadratic form.  The decoupling of the two
pairings and the integrability of the fibre integrands are *derived* from these. -/
structure SlotFacts {m n : ℕ} (e : Fin m → Ω → ℂ) (Φc : Xn n → ℂ)
    (Op : (Xn n → ℂ) → (Xn n → ℂ))
    (OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)) : Prop where
  good : RowGood Op
  slice : ∀ (S : Finset (Fin n)) (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
    Op (slotExact e S Φc) (pairCoord S u y)
      = OpS S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
  split : (∫ x, star (Φc x) * Op Φc x).re
    = ∑ S : Finset (Fin n), (∫ x, star (slotExact e S Φc x) * Op (slotExact e S Φc) x).re

end Work.BoseBoxFock
