import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.bqPotsplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.bqPotsplitBdd` — the potential split at `L^∞`-states

This module is the **Measurable + bounded** clone of the potential-split chain of
`Submission.Work.BoseFixB1.bqPotsplit` (FS `lem:potsplit`, localised form).  Every lemma of that
chain is stated for a `Continuous` state; continuity is used there in exactly two ways:

* `hΦc.measurable`, to get the measurability of the slot means and of the slot integrands;
* `exists_bound_of_continuousOn` on the compact box (and on compact images of it), to get a
  numerical bound of the state *and* of the box projections whenever they are evaluated at
  configurations obtained from a box configuration by replacing coordinates by points of `A`.

Both are supplied verbatim by the `L^∞`-currency `Measurable Φ` + `∀ x ∈ abox N ℓ, |Φ x| ≤ B`
(cf. `Submission/Work/BoseFixB1B/peelBdd.lean`, which did the same for the one-slot peels).

## What is proved here

The four orientation swaps and the pattern sum of the box projections (`BoxPotOper`) at the
`L^∞`-hypotheses, the pointwise fourteen-fragment identity (`BoxPotFrag.boxPairPointwise`), the
two half-identities of the potential word (`muPart_dlBox`, the pair telescoping), and finally the
assembled split `bqPotsplitBdd`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1C

open Submission.BoseGases
open Work.BoseFixB1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Local copies of the two orientation swaps of `OscFibDefs`

`Submission.Work.BoseFixB1S.OscFibDefs` is the only module of the `bqPotsplitBdd` cone that
imports `Submission.Work.BoseFixB1S.exclFunOpAux`, which declares a `goodState_finset_sum`
duplicating the one of `Submission.Work.BoseFixB1S.boxQCount_eq_sum_compT`; the two cones are
mutually unimportable.  The only two declarations used from `OscFibDefs` here are the two
orientation swaps below, so they are copied verbatim (with `Work.BoseFixB1S.twoMean` /
`Work.BoseFixB1S.boxPInd_twoMean` qualified). -/

/-- The two-slot mean is symmetric (Fubini), with the joint integrability as hypothesis. -/
theorem twoMean_comm_int {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ}
    (hint : ∀ x ∈ abox N ℓ, Integrable
      (fun p : E3 × E3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A))) :
    ∀ x ∈ abox N ℓ,
      Work.BoseFixB1S.twoMean volA A i j Ψ x = Work.BoseFixB1S.twoMean volA A j i Ψ x := by
  intro x hx
  have hInt : Integrable
      (Function.uncurry (fun z w : E3 => Ψ (Function.update (Function.update x i z) j w)))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := hint x hx
  have hswap : (∫ z in A, ∫ w in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w) :=
    MeasureTheory.integral_integral_swap hInt
  have h2 : (∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x i z) j w))
      = ∫ w in A, ∫ z in A, Ψ (Function.update (Function.update x j w) i z) := by
    apply integral_congr_ae; filter_upwards with w
    apply integral_congr_ae; filter_upwards with z
    rw [Function.update_comm hij]
  unfold Work.BoseFixB1S.twoMean
  rw [hswap, h2]

/-- The box projections in two different slots commute, with the joint integrability as
hypothesis. -/
theorem boxPInd_boxPInd_comm_int {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {i j : Fin N} (hij : i ≠ j) {Ψ : X N → ℝ}
    (hint : ∀ x ∈ abox N ℓ, Integrable
      (fun p : E3 × E3 => Ψ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A))) :
    ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Ψ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Ψ) x := by
  intro x hx
  rw [Work.BoseFixB1S.boxPInd_twoMean volA A hij.symm Ψ x,
    Work.BoseFixB1S.boxPInd_twoMean volA A hij Ψ x,
    (twoMean_comm_int hℓ hA hAc hij hint x hx)]
  ring

/-! ## 0. Integrability of the two-slot pull-back of an `L^∞`-state -/

/-- The two-slot pull-back of a measurable, box-bounded state is jointly integrable (over
`A × A`, `A ⊆ acube ℓ` of finite measure). -/
theorem integrable_twoMean_pullback {N : ℕ} {ℓ : ℝ} {A : Set E3}
    (hℓ : 0 < ℓ) (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦm : Measurable Φ) {B : ℝ}
    (hB : ∀ x ∈ abox N ℓ, |Φ x| ≤ B) (i j : Fin N) (x : X N) (hx : x ∈ abox N ℓ) :
    Integrable (fun p : E3 × E3 => Φ (Function.update (Function.update x i p.1) j p.2))
      (((volume : Measure E3).restrict A).prod ((volume : Measure E3).restrict A)) := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict A) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
  refine MeasureTheory.Integrable.of_bound ?_ B ?_
  · exact (hΦm.comp (by fun_prop : Measurable (fun p : E3 × E3 =>
      Function.update (Function.update x i p.1) j p.2))).aestronglyMeasurable
  · have hae : ∀ᵐ p ∂(((volume : Measure E3).restrict A).prod
        ((volume : Measure E3).restrict A)), p ∈ A ×ˢ A := by
      rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.ae_restrict_iff' (hA.prod hA)]
      exact Filter.Eventually.of_forall (fun p hp => hp)
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact hB _ (Work.BoseFixB1S.update_mem_abox' (N := N) (ℓ := ℓ) (A := A) hAc
      (Work.BoseFixB1S.update_mem_abox' (N := N) (ℓ := ℓ) (A := A) hAc hx i hp.1) j hp.2)

/-! ## 1. The bounded projections and the two-slot integrand -/

/-- `|Q_iΨ| ≤ 2B` on the box whenever `|Ψ| ≤ B` there (and `B ≥ 0`). -/
theorem abs_boxQInd_le_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Ψ : X N → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ B) :
    ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * B := by
  intro x hx
  have hP := Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc i (C := B) hb x hx
  rw [Work.BoseFixB1S.boxQInd_eq volA A i Ψ x]
  calc |Work.BoseFixB1S.Aind A (x i) * Ψ x - Work.UBBInputs8.boxPInd volA A i Ψ x|
      ≤ |Work.BoseFixB1S.Aind A (x i) * Ψ x| + |Work.UBBInputs8.boxPInd volA A i Ψ x| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (Work.BoseFixB1S.Aind A (x i) * Ψ x)
            (-(Work.UBBInputs8.boxPInd volA A i Ψ x))
    _ ≤ 1 * B + B := by
        refine add_le_add ?_ hP
        rw [abs_mul]
        exact mul_le_mul (Work.BoseFixB1S.Aind_abs_le_one A (x i)) (hb x hx)
          (abs_nonneg _) (by norm_num)
    _ = 2 * B := by ring

/-- The two-slot slot integral of a measurable, box-bounded state is integrable. -/
theorem slotInt2_of_bound_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) (i j : Fin N) (x : X N) (hx : x ∈ abox N ℓ)
    {Φ : X N → ℝ} (hΦm : Measurable Φ) {C : ℝ} (hC : ∀ y ∈ abox N ℓ, |Φ y| ≤ C) :
    IntegrableOn (fun z => (1 / volA) * ∫ w in A,
      Φ (Function.update (Function.update x i z) j w)) A volume := by
  have hfin : (volume : Measure E3) A < ⊤ := Work.BoseFixB1S.volume_A_lt_top hℓ hAc
  have hm1 : Measurable (fun y : X N =>
      ∫ w in A, Φ (Function.update y j w)) :=
    Work.BoseFixB1S.measurable_fibreMean A hA j hΦm
  have hm2 : Measurable (fun z : E3 =>
      ∫ w in A, Φ (Function.update (Function.update x i z) j w)) :=
    hm1.comp (by fun_prop : Measurable (fun z : E3 => Function.update x i z))
  refine IntegrableOn.of_bound hfin ((hm2.const_mul (1 / volA)).aestronglyMeasurable) C ?_
  rw [ae_restrict_iff' hA]
  apply Filter.Eventually.of_forall
  intro z hz
  rw [Real.norm_eq_abs]
  have hInt : |∫ w in A, Φ (Function.update (Function.update x i z) j w)| ≤ C * volA := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure E3)) hfin (s := A)
      (f := fun w : E3 => Φ (Function.update (Function.update x i z) j w)) (C := C) (fun w hw => by
        rw [Real.norm_eq_abs]
        exact hC _ (Work.BoseFixB1S.update_mem_abox' (N := N) (ℓ := ℓ) (A := A) hAc
          (Work.BoseFixB1S.update_mem_abox' (N := N) (ℓ := ℓ) (A := A) hAc hx i hz) j hw))
    rw [Real.norm_eq_abs, MeasureTheory.Measure.real_def, ← hvolA] at h
    exact h
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol)]
  calc (1 / volA) * |∫ w in A, Φ (Function.update (Function.update x i z) j w)|
      ≤ (1 / volA) * (C * volA) :=
        mul_le_mul_of_nonneg_left hInt (by positivity)
    _ = C := by field_simp

/-! ## 2. The mean form of the mixed patterns at `L^∞`-states -/

/-- `P_iQ_jΨ = 1_A(x_i)·1_A(x_j)·(oneMeanᵢ − twoMeanᵢⱼ)` for measurable, box-bounded `Ψ`. -/
theorem boxPInd_boxQInd_twoMean_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
        * (Work.BoseFixB1S.oneMean volA A i Φ x - Work.BoseFixB1S.twoMean volA A i j Φ x) := by
  have hinner : ∀ z : E3, Work.UBBInputs8.boxQInd volA A j Φ (Function.update x i z)
      = Work.BoseFixB1S.Aind A (x j) * (Φ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    intro z
    rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    have h1 : (Function.update x i z) j = x j := by
      rw [Function.update_apply, if_neg]
      exact fun h => hij h.symm
    rw [h1]
    unfold Work.BoseFixB1S.Aind
    ring
  rw [Work.UBBInputs8.boxPInd]
  rw [show (∫ z in A, Work.UBBInputs8.boxQInd volA A j Φ (Function.update x i z))
      = ∫ z in A, Work.BoseFixB1S.Aind A (x j) * (Φ (Function.update x i z)
          - (1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) from by
    apply integral_congr_ae; filter_upwards with z; exact hinner z]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub
    (Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx hΦm hB)
    (slotInt2_of_bound_bdd hℓ hvol hA hvolA hAc i j x hx hΦm hB)]
  rw [MeasureTheory.integral_const_mul]
  unfold Work.BoseFixB1S.oneMean Work.BoseFixB1S.twoMean Work.BoseFixB1S.Aind
  ring

/-- `Q_iQ_jΨ = 1_A(x_i)·1_A(x_j)·(Ψ − oneMeanᵢ − oneMeanⱼ + twoMeanᵢⱼ)` for measurable,
box-bounded `Ψ`. -/
theorem boxQInd_boxQInd_twoMean_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
        * (Φ x - Work.BoseFixB1S.oneMean volA A i Φ x - Work.BoseFixB1S.oneMean volA A j Φ x
            + Work.BoseFixB1S.twoMean volA A i j Φ x) := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxQInd,
    boxPInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx,
    Work.BoseFixB1S.boxPInd_eq volA A j Φ x]
  unfold Work.BoseFixB1S.Aind
  ring

/-! ## 3. The pattern sum and the four orientation swaps at `L^∞`-states -/

/-- `P_iP_jΨ + P_iQ_jΨ + Q_iP_jΨ + Q_iQ_jΨ = 1_A(x_i)·1_A(x_j)·Ψ` for measurable, box-bounded
`Ψ`. -/
theorem boxPatternSum_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * Φ x := by
  have hPb : ∀ k : Fin N, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A k Φ y| ≤ B :=
    fun k y hy => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol hA hvolA hAc k hB y hy
  have hQb : ∀ k : Fin N, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A k Φ y| ≤ 2 * B :=
    fun k y hy => abs_boxQInd_le_bdd hℓ hvol hA hvolA hAc k hB0 hB y hy
  have hPi : Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x :=
    Work.BoseFixB1S.boxPInd_add volA A i x
      (Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm) (hPb j))
      (Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
        (Work.SlotWord.measurable_boxQInd volA A hA j hΦm) (hQb j))
  have hQi : Work.UBBInputs8.boxQInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x :=
    Work.BoseFixB1S.boxQInd_add volA A i x
      (Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
        (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm) (hPb j))
      (Work.BoseFixB1S.slotInt_of_bound hℓ hA hAc i x hx
        (Work.SlotWord.measurable_boxQInd volA A hA j hΦm) (hQb j))
  have hsum : (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ)
      = fun y => Work.BoseFixB1S.Aind A (y j) * Φ y := by
    funext y
    show Work.UBBInputs8.boxPInd volA A j Φ y + Work.UBBInputs8.boxQInd volA A j Φ y
      = Work.BoseFixB1S.Aind A (y j) * Φ y
    unfold Work.UBBInputs8.boxQInd Work.BoseFixB1S.Aind
    ring
  calc Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        + (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
          + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) := by ring
    _ = Work.UBBInputs8.boxPInd volA A i
          (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x
        + Work.UBBInputs8.boxQInd volA A i
          (Work.UBBInputs8.boxPInd volA A j Φ + Work.UBBInputs8.boxQInd volA A j Φ) x := by
          rw [hPi, hQi]
    _ = Work.UBBInputs8.boxPInd volA A i (fun y => Work.BoseFixB1S.Aind A (y j) * Φ y) x
        + Work.UBBInputs8.boxQInd volA A i (fun y => Work.BoseFixB1S.Aind A (y j) * Φ y) x := by
          rw [hsum]
    _ = Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x
        + (Work.BoseFixB1S.Aind A (x i) * (Work.BoseFixB1S.Aind A (x j) * Φ x)
          - Work.BoseFixB1S.Aind A (x j) * Work.UBBInputs8.boxPInd volA A i Φ x) := by
          rw [Work.BoseFixB1S.boxPInd_smul volA A hij Φ x,
            Work.BoseFixB1S.boxQInd_smul volA A hij Φ x]
    _ = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * Φ x := by ring

/-- Orientation swap of the `PP` pattern at `L^∞`-states. -/
theorem boxPPswap_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x :=
  boxPInd_boxPInd_comm_int hℓ hvol hA hvolA hAc hij
    (fun y hy => integrable_twoMean_pullback hℓ hA hAc hΦm hB i j y hy) x hx

/-- Orientation swap of the `PQ` pattern at `L^∞`-states. -/
theorem boxPQswap_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
  rw [boxPInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij.symm hΦm hB0 hB x hx,
    Work.BoseFixB1S.boxQInd_boxPInd_twoMean volA A hij Φ x,
    twoMean_comm_int hℓ hA hAc hij
      (fun y hy => integrable_twoMean_pullback hℓ hA hAc hΦm hB i j y hy) x hx]
  ring

/-- Orientation swap of the `QP` pattern at `L^∞`-states. -/
theorem boxQPswap_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
  rw [Work.BoseFixB1S.boxQInd_boxPInd_twoMean volA A hij.symm Φ x,
    boxPInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx,
    twoMean_comm_int hℓ hA hAc hij
      (fun y hy => integrable_twoMean_pullback hℓ hA hAc hΦm hB i j y hy) x hx]
  ring

/-- Orientation swap of the `QQ` pattern at `L^∞`-states. -/
theorem boxQQswap_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B) (x : X N) (hx : x ∈ abox N ℓ) :
    Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
      = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x := by
  rw [boxQInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij.symm hΦm hB0 hB x hx,
    boxQInd_boxQInd_twoMean_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx,
    twoMean_comm_int hℓ hA hAc hij
      (fun y hy => integrable_twoMean_pullback hℓ hA hAc hΦm hB i j y hy) x hx]
  ring

/-! ## 4. The pointwise fourteen-fragment identity at `L^∞`-states -/

/-- The box-pair pointwise identity at the `L^∞`-hypotheses: the sum of the fourteen pair
fragments of the five box words equals `1_A(x_i)·1_A(x_j)·Φ(x)²·w(x_i,x_j)`.  Continuity of `Φ`
in `BoxPotFrag.boxPairPointwise` is replaced by `Measurable Φ` + the bound on `abox`. -/
theorem boxPairPointwise_bdd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = ((volume : Measure E3) A).toReal)
    (hAc : A ⊆ acube ℓ)
    {w w1 w2 om : E3 → E3 → ℝ}
    (hwsym : ∀ x y : E3, w x y = w y x) (homsym : ∀ x y : E3, om x y = om y x)
    (hw1rel : ∀ x y : E3, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : E3, w2 x y = w x y * (1 - om x y ^ 2))
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦm : Measurable Φ)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ B)
    (x : X N) (hx : x ∈ abox N ℓ) :
    Work.BoseFixB1S.fgsum volA A w w1 w2 om Φ i j x
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * (Φ x) ^ 2
        * w (x i) (x j) := by
  unfold Work.BoseFixB1S.fgsum Work.BoseFixB1S.fg0 Work.BoseFixB1S.fg1 Work.BoseFixB1S.fg2a
    Work.BoseFixB1S.fg2b Work.BoseFixB1S.fg2c Work.BoseFixB1S.fg3 Work.BoseFixB1S.fg4
  let Aa : ℝ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let Bb : ℝ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
  let Cc : ℝ := Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let Dd : ℝ := Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
  let W : ℝ := w (x i) (x j)
  let O : ℝ := om (x i) (x j)
  let W1 : ℝ := w1 (x i) (x j)
  let W2 : ℝ := w2 (x i) (x j)
  have hW1rel : W1 = W * (1 - O) := by simp only [W1, W, O, hw1rel]
  have hW2rel : W2 = W * (1 - O ^ 2) := by simp only [W2, W, O, hw2rel]
  -- the pattern sum
  have hpat : Aa + Bb + Cc + Dd
      = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * Φ x := by
    simp only [Aa, Bb, Cc, Dd]
    exact boxPatternSum_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx
  -- the orientation swaps
  have hA' : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x = Aa := by
    simp only [Aa]
    exact boxPPswap_bdd hℓ hvol hA hvolA hAc hij hΦm hB x hx
  have hB' : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x = Cc := by
    simp only [Cc]
    exact boxPQswap_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx
  have hC' : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x = Bb := by
    simp only [Bb]
    exact boxQPswap_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx
  have hD' : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x = Dd := by
    simp only [Dd]
    exact boxQQswap_bdd hℓ hvol hA hvolA hAc hij hΦm hB0 hB x hx
  -- the kernel symmetries at the swapped slots
  have hWsym : w (x j) (x i) = W := by simp only [W]; exact (hwsym (x i) (x j)).symm
  have hOsym : om (x j) (x i) = O := by simp only [O]; exact (homsym (x i) (x j)).symm
  have hW1sym : w1 (x j) (x i) = W1 := by
    simp only [W1]
    rw [hw1rel (x j) (x i), hw1rel (x i) (x j), hwsym (x i) (x j), homsym (x i) (x j)]
  have hW2sym : w2 (x j) (x i) = W2 := by
    simp only [W2]
    rw [hw2rel (x j) (x i), hw2rel (x i) (x j), hwsym (x i) (x j), homsym (x i) (x j)]
  -- the two `Q₄` brackets, in explicit form
  have hB4ij : Work.BoseFixB1S.boxQ4B volA A om Φ (i, j) x
      = Dd + om (x i) (x j) * (Aa + Bb + Cc) := by
    have h1 : Work.BoseFixB1S.boxQ4B volA A om Φ (i, j) x
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + om (x i) (x j)
            * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) := rfl
    rw [h1, hD', hA', hB', hC']
    try ring
  have hB4ji : Work.BoseFixB1S.boxQ4B volA A om Φ (j, i) x
      = Dd + om (x i) (x j) * (Aa + Bb + Cc) := by
    have h1 : Work.BoseFixB1S.boxQ4B volA A om Φ (j, i) x
        = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
          + om (x j) (x i)
            * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
              + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) := rfl
    rw [h1, hOsym]
  -- the fourteen fragment values
  have h0ij : (1 / 2) * (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 * w2 (x i) (x j)
      = (1 / 2) * Aa ^ 2 * W2 := by
    simp only [Aa, W2]; try ring
  have h1ij : 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * w2 (x i) (x j) = 2 * Bb * Aa * W2 := by
    simp only [Aa, Bb, W2]; try ring
  have h2aij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w2 (x i) (x j) = Bb * Cc * W2 := by
    simp only [hB', Bb, Cc, W2]; try ring
  have h2bij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * w2 (x i) (x j) = Bb * Bb * W2 := by
    simp only [hC', Bb, W2]; try ring
  have h2cij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w1 (x i) (x j) = Aa * Dd * W1 := by
    simp only [hD', Aa, Dd, W1]; try ring
  have h3ij : 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w1 (x i) (x j) = 2 * Bb * Dd * W1 := by
    simp only [hD', Bb, Dd, W1]; try ring
  have h4ij : (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A om Φ (i, j) x) ^ 2 * w (x i) (x j)
      = (1 / 2) * (Dd + om (x i) (x j) * (Aa + Bb + Cc)) ^ 2 * W := by
    simp only [hB4ij, W]; try ring
  have h0ji : (1 / 2) * (Work.UBBInputs8.boxPInd volA A j
        (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 * w2 (x j) (x i)
      = (1 / 2) * Aa ^ 2 * W2 := by
    simp only [hA', hW2sym, Aa, W2]; try ring
  have h1ji : 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * w2 (x j) (x i) = 2 * Cc * Aa * W2 := by
    simp only [hB', hA', hW2sym, Aa, Cc, W2]; try ring
  have h2aji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w2 (x j) (x i) = Cc * Bb * W2 := by
    simp only [hB', hW2sym, Bb, Cc, W2]; try ring
  have h2bji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * w2 (x j) (x i) = Cc * Cc * W2 := by
    simp only [hB', hW2sym, Cc, W2]; try ring
  have h2cji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w1 (x j) (x i) = Aa * Dd * W1 := by
    simp only [hA', hW1sym, Aa, Dd, W1]; try ring
  have h3ji : 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w1 (x j) (x i) = 2 * Cc * Dd * W1 := by
    simp only [hB', hW1sym, Cc, Dd, W1]; try ring
  have h4ji : (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A om Φ (j, i) x) ^ 2 * w (x j) (x i)
      = (1 / 2) * (Dd + om (x i) (x j) * (Aa + Bb + Cc)) ^ 2 * W := by
    simp only [hB4ji, hWsym, W]; try ring
  -- the target right-hand side in atom form
  have hRHS : Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * (Φ x) ^ 2
        * w (x i) (x j)
      = (Aa + Bb + Cc + Dd) ^ 2 * W := by
    have hσ : Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
          * (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j))
        = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) := by
      rw [show Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
            * (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j))
          = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x i)
            * (Work.BoseFixB1S.Aind A (x j) * Work.BoseFixB1S.Aind A (x j)) from by ring,
        Work.BoseFixB1S.Aind_mul_self A (x i), Work.BoseFixB1S.Aind_mul_self A (x j)]
    have hσΦ : (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * Φ x) ^ 2
        = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * (Φ x) ^ 2 := by
      calc (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * Φ x) ^ 2
          = (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)
              * (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j)))
              * ((Φ x) * (Φ x)) := by ring
        _ = (Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j))
              * ((Φ x) * (Φ x)) := by rw [hσ]
        _ = Work.BoseFixB1S.Aind A (x i) * Work.BoseFixB1S.Aind A (x j) * (Φ x) ^ 2 := by ring
    rw [hpat, hσΦ]
  rw [hRHS]
  rw [h0ij, h1ij, h2aij, h2bij, h2cij, h3ij, h4ij,
    h0ji, h1ji, h2aji, h2bji, h2cji, h3ji, h4ji]
  rw [hW1rel, hW2rel]
  ring


/-! ## 5. The localised kernel support helpers (copied from `Work.BoseFixB1`) -/

/-- `χ_{B(u)}(z) ≠ 0` forces `z ∈ B(u) = dlBox ℓ d u`. -/
theorem chiSmallB_mem_dlBox' {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) (hz : chiSmallB M ℓ d u z ≠ 0) : z ∈ dlBox ℓ d u := by
  rw [Work.SmallBoxSliding.mem_dlBox_iff_scaled hℓ hd]
  refine ⟨?_, ?_⟩
  · exact chiScale_mem_acube hℓ (fun h => hz (by rw [chiSmallB, h, zero_mul]))
  · rw [mem_acube_iff]
    intro j
    have h := chiSmall_support_mem_abs_le hM (fun h => hz (by rw [chiSmallB, h, mul_zero])) j
    rw [Set.mem_Icc]
    exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- `wSmallPair M ℓ d u f x y = 0` as soon as `x ∉ B(u)`. -/
theorem wSmallPair_eq_zero_of_notMem {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) (f : ℝ³ → ℝ) {x y : ℝ³} (hx : x ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  have hχ : chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_mem_dlBox' hM hℓ hd u x hne)
  simp only [wSmallPair, hχ, zero_mul]

/-- **The support of the localised kernel**: `wSmallPair M ℓ d u f x y ≠ 0` forces both
arguments into `B(u) = dlBox ℓ d u`. -/
theorem wSmallPair_support {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) (f : ℝ³ → ℝ) {x y : ℝ³} (hxy : wSmallPair M ℓ d u f x y ≠ 0) :
    x ∈ dlBox ℓ d u ∧ y ∈ dlBox ℓ d u := by
  have hx : chiSmallB M ℓ d u x ≠ 0 := by
    intro h
    exact hxy (by simp only [wSmallPair, h, zero_mul])
  have hy : chiSmallB M ℓ d u y ≠ 0 := by
    intro h
    exact hxy (by simp only [wSmallPair, h, mul_zero])
  exact ⟨chiSmallB_mem_dlBox' hM hℓ hd u x hx, chiSmallB_mem_dlBox' hM hℓ hd u y hy⟩

/-- The `w₁`-fibre vanishes outside the box. -/
theorem w1Fibre_eq_zero_of_notMem {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) (f : ℝ³ → ℝ) (z : ℝ³) (hz : z ∉ dlBox ℓ d u) :
    w1Fibre ℓ (wSmallPair M ℓ d u f) z = 0 := by
  unfold w1Fibre
  have h0 : (fun y : ℝ³ => wSmallPair M ℓ d u f z y) = fun _ : ℝ³ => (0 : ℝ) := by
    funext y
    exact wSmallPair_eq_zero_of_notMem hM hℓ hd u f hz
  rw [h0]
  simp

/-- The box indicator in a slot fixes the `w₁`-fibre. -/
theorem aind_mul_w1Fibre {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) (f : ℝ³ → ℝ) :
    Work.BoseFixB1S.Aind (dlBox ℓ d u) z * w1Fibre ℓ (wSmallPair M ℓ d u f) z
      = w1Fibre ℓ (wSmallPair M ℓ d u f) z := by
  by_cases hz : z ∈ dlBox ℓ d u
  · simp [Work.BoseFixB1S.Aind, Set.indicator_of_mem hz]
  · rw [w1Fibre_eq_zero_of_notMem hM hℓ hd u f z hz]
    simp [Work.BoseFixB1S.Aind, Set.indicator_of_notMem hz]

/-! ## 6. The pair-part assemblies at `L^∞`-states -/

/-- `boxQSum` unfolded: the pair parts of the five words reassemble into `pairRaw`, and the
`μ`-parts with coefficients `1, 2, 1` into the three `boxMu`-sums. -/
theorem boxQSum_eq' {N : ℕ} (volA ℓ μ : ℝ) (A : Set ℝ³)
    (w w1 w2 om : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) :
    Work.BoseFixB1S.boxQSum volA ℓ μ A w w1 w2 om Φ
      = Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
        - μ * ((∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
            + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
            + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)) := by
  unfold Work.BoseFixB1S.boxQSum Work.BoseFixB1S.boxQ0 Work.BoseFixB1S.boxQ1
    Work.BoseFixB1S.boxQ2 Work.BoseFixB1S.boxQ3 Work.BoseFixB1S.boxQ4
    Work.BoseFixB1S.pairRaw Work.BoseFixB1S.boxMuP Work.BoseFixB1S.boxMuQP
    Work.BoseFixB1S.boxMuQ
  ring
/-- `pairRaw` is the sum of the `pairInts` (pure `Finset` algebra; no integrability needed,
because each word's pair-summand integral carries its word coefficient already). -/
theorem pairRaw_eq_sum_pairInts {N : ℕ} (volA ℓ : ℝ) (A : Set ℝ³)
    (w w1 w2 om : ℝ³ → ℝ³ → ℝ) (Φ : X N → ℝ) :
    Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
      = ∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2 := by
  unfold Work.BoseFixB1S.pairRaw Work.BoseFixB1S.pairInts
  have h0 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg0 volA A w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
        * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg0
    ring
  have h1 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg1 volA A w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
        * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg1
    ring
  have h2a : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2a volA A w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2b : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
            * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2b volA A w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2c : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg2c volA A w1 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h3 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
            * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
            * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg3 volA A w1 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ)
      (fun x : X N => (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
        * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
        * w1 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg3
    ring
  have h4 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, Work.BoseFixB1S.fg4 volA A w om Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Work.BoseFixB1S.boxQ4B volA A om Φ p x) ^ 2 * w (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold Work.BoseFixB1S.fg4
    ring
  rw [h0, h1, h2a, h2b, h2c, h3, h4]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
/-- **The pair part.**  `pairRaw` at the sliding box equals `½ Σ_p ∫ Φ²·w(x_p.1,x_p.2)`. -/
theorem pairRaw_eq_dlBox_bdd {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} (hΦm : Measurable Φ) {Bb : ℝ} (hB0 : 0 ≤ Bb)
    (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ Bb) :
    Work.BoseFixB1S.pairRaw (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (dlBox ℓ d u)
        (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) (wSmallPair M ℓ d u (g2 v h))
        (omC (Classical.choose h)) Φ
      = (1 / 2) * (∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
  classical
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  set A : Set ℝ³ := dlBox ℓ d u with hAdef
  set W : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u v with hWdef
  set W1 : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u (g0 v h) with hW1def
  set W2 : ℝ³ → ℝ³ → ℝ := wSmallPair M ℓ d u (g2 v h) with hW2def
  set OM : ℝ³ → ℝ³ → ℝ := omC (Classical.choose h) with hOMdef
  have hvol' : 0 < volA := by rw [hvolAdef]; exact hvol
  have hA : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA : volA = ((volume : Measure ℝ³) A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  have hsupA : ∀ x y : ℝ³, W x y ≠ 0 → x ∈ A ∧ y ∈ A := by
    intro x y hxy
    have hw : wSmallPair M ℓ d u v x y ≠ 0 := by rwa [hWdef] at hxy
    obtain ⟨hx, hy⟩ := wSmallPair_support (M := M) hM hℓ hd u v hw
    exact ⟨by rwa [hAdef], by rwa [hAdef]⟩
  set C : ℝ := Bb with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact hB0
  have hCΦ : ∀ y ∈ abox N ℓ, |Φ y| ≤ C := fun y hy => by rw [hCdef]; exact hB y hy
  have hCP : ∀ i : Fin N, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ y| ≤ C :=
    fun i y hy => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol' hA hvolA hAc i hCΦ y hy
  have hCQ : ∀ i : Fin N, ∀ y ∈ abox N ℓ, |Work.UBBInputs8.boxQInd volA A i Φ y| ≤ 2 * C :=
    fun i y hy => abs_boxQInd_le_bdd hℓ hvol' hA hvolA hAc i hC0 hCΦ y hy
  -- measurability of the four two-slot patterns
  have hQmeas : ∀ (i : Fin N) {Ψ : X N → ℝ}, Measurable Ψ →
      Measurable (Work.UBBInputs8.boxQInd volA A i Ψ) := by
    intro i Ψ hΨ
    have heq : Work.UBBInputs8.boxQInd volA A i Ψ
        = fun x : X N => Work.BoseFixB1S.Aind A (x i) * Ψ x
            - Work.UBBInputs8.boxPInd volA A i Ψ x := by
      funext x; exact Work.BoseFixB1S.boxQInd_eq volA A i Ψ x
    rw [heq]
    exact ((Work.BoseFixB1S.measurable_sigAt A hA i).mul hΨ).sub
      (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΨ)
  have hPP : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) :=
    fun i j => Work.BoseFixB1S.measurable_boxPInd volA A hA i
      (Work.BoseFixB1S.measurable_boxPInd volA A hA j hΦm)
  have hPQ : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x) :=
    fun i j => Work.BoseFixB1S.measurable_boxPInd volA A hA i (hQmeas j hΦm)
  have hQP : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) :=
    fun i j => hQmeas j (Work.BoseFixB1S.measurable_boxPInd volA A hA i hΦm)
  have hQQ : ∀ i j : Fin N, Measurable (fun x : X N =>
      Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x) :=
    fun i j => hQmeas j (hQmeas i hΦm)
  -- pointwise bounds on the box
  have bPP : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ C :=
    fun i j => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol' hA hvolA hAc i (C := C) (hCP j)
  have bPQ : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x| ≤ 2 * C :=
    fun i j => Work.BoseFixB1S.abs_boxPInd_le hℓ hvol' hA hvolA hAc i (C := 2 * C) (hCQ j)
  have bQP : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| ≤ 2 * C := by
    intro i j x hx
    have := abs_boxQInd_le_bdd hℓ hvol' hA hvolA hAc j (B := C) hC0 (hCP i) x hx
    linarith
  have bQQ : ∀ (i j : Fin N) (x : X N), x ∈ abox N ℓ →
      |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| ≤ 4 * C := by
    intro i j x hx
    have := abs_boxQInd_le_bdd hℓ hvol' hA hvolA hAc j (B := 2 * C) (by linarith) (hCQ i) x hx
    linarith
  -- generic fragment integrability from the slot lemma
  have fragInt : ∀ (S : X N → ℝ) (B : ℝ), 0 ≤ B →
      (∀ᵐ x ∂(volume.restrict (abox N ℓ)), |S x| ≤ B) →
      AEStronglyMeasurable S (volume.restrict (abox N ℓ)) →
      ∀ (f : ℝ³ → ℝ), Integrable f → (∀ z : ℝ³, R0 ≤ ‖z‖ → f z = 0) →
      ∀ (i j : Fin N), i ≠ j →
      IntegrableOn (fun x : X N => S x * wSmallPair M ℓ d u f (x i) (x j)) (abox N ℓ) volume := by
    intro S B hB0 hSb hSm f hf hfsupp i j hij
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd hf hfsupp hM hR hRχ
      u hij hSm hB0 hSb
  have aeBound : ∀ (S : X N → ℝ) (B : ℝ), (∀ x ∈ abox N ℓ, |S x| ≤ B) →
      ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |S x| ≤ B :=
    fun S B hb => (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ hb)
  have hI0 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg0 volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(1 / 2) * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2|
          ≤ (1 / 2) * C ^ 2 := by
      intro x hx
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (bPP i j x hx) 2)
        (by norm_num)
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      (measurable_const.mul ((hPP i j).pow_const 2)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg0, hW2def] using hInt
  have hI1 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg1 volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)|
          = (2 * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|)
              * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (2 * C)) * C := mul_le_mul
            (mul_le_mul_of_nonneg_left (bPQ i j x hx) (by norm_num))
            (bPP i j x hx) (abs_nonneg _) (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((measurable_const.mul (hPQ i j)).mul (hPP i j)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg1, hW2def] using hInt
  have hI2a : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2a volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|
              * |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ (2 * C) * (2 * C) := mul_le_mul (bPQ i j x hx) (bPQ j i x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPQ i j).mul (hPQ j i)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2a, hW2def] using hInt
  have hI2b : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2b volA A W2 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ (2 * C) * (2 * C) := mul_le_mul (bPQ i j x hx) (bQP i j x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPQ i j).mul (hQP i j)).aestronglyMeasurable
      (g2 v h) (g2_integrable hR0 hv hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2b, hW2def] using hInt
  have hI2c : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg2c volA A W1 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 4 * C ^ 2 := by
      intro x hx
      calc |(Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x|
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| :=
            abs_mul _ _
        _ ≤ C * (4 * C) := mul_le_mul (bPP i j x hx) (bQQ i j x hx) (abs_nonneg _)
            (by linarith [hC0])
        _ = 4 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((hPP i j).mul (hQQ i j)).aestronglyMeasurable
      (g0 v h) (g0_integrable hR0 hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg2c, hW1def] using hInt
  have hI3 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg3 volA A W1 Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hb : ∀ x ∈ abox N ℓ,
        |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
            * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          ≤ 16 * C ^ 2 := by
      intro x hx
      calc |2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
              * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)|
          = (2 * |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x|)
              * |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 * (2 * C)) * (4 * C) := mul_le_mul
            (mul_le_mul_of_nonneg_left (bPQ i j x hx) (by norm_num))
            (bQQ i j x hx) (abs_nonneg _) (by linarith [hC0])
        _ = 16 * C ^ 2 := by ring
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) (aeBound _ _ hb)
      ((measurable_const.mul (hPQ i j)).mul (hQQ i j)).aestronglyMeasurable
      (g0 v h) (g0_integrable hR0 hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) i j hij
    simpa [Work.BoseFixB1S.fg3, hW1def] using hInt
  have hI4 : ∀ (i j : Fin N) (hij : i ≠ j), IntegrableOn (fun x : X N =>
      Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := by
    intro i j hij
    have hbnds := scattering_bounds_ae (w := Classical.choose h) hR0 hv hvrad hv_supp
      (w0_spec h).1 (w0_spec h).2
    have hom : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |OM (x i) (x j)| ≤ 1 := by
      have hfull : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
        filter_upwards [hbnds.1, hbnds.2] with z h1 h2
        rw [abs_of_nonneg h1]; exact h2
      have hpull := ae_pair_pullback (N := N) hℓ hij hfull
      filter_upwards [hpull] with x hx
      simpa [hOMdef, omC] using hx
    have hb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
        |(1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2|
          ≤ (1 / 2) * (9 * C) ^ 2 := by
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ), hom] with x hxmem homx
      have h4 : |Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x| ≤ 9 * C := by
        have h1 := bQQ i j x hxmem
        have h2 := bPP j i x hxmem
        have h3 := bPQ j i x hxmem
        have h5 := bQP i j x hxmem
        have hsum : |Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x|
            ≤ C + 2 * C + 2 * C :=
          le_trans (abs_add_le _ _)
            (add_le_add (le_trans (abs_add_le _ _) (add_le_add h2 h3)) h5)
        calc |Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x|
            = |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                + OM (x i) (x j)
                  * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                    + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                    + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)| := rfl
          _ ≤ |Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x|
                + |OM (x i) (x j)
                  * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                    + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                    + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)| :=
              abs_add_le _ _
          _ ≤ 4 * C + 1 * (C + 2 * C + 2 * C) := by
              refine add_le_add h1 ?_
              rw [abs_mul]
              exact mul_le_mul homx hsum (abs_nonneg _) (by norm_num)
          _ ≤ 9 * C := by linarith
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h4 2) (by norm_num)
    have homm : AEStronglyMeasurable (fun x : X N => OM (x i) (x j))
        (volume.restrict (abox N ℓ)) := by
      have hli : LocallyIntegrable (Classical.choose h) := (w0_spec h).2.lhs_integrable
      have hpull := w0_diff_aem (N := N) hℓ hij hli
      simpa [hOMdef, omC] using hpull
    have hmid : AEStronglyMeasurable (fun x : X N =>
        Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
          + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        (volume.restrict (abox N ℓ)) :=
      ((hPP j i).aestronglyMeasurable.add (hPQ j i).aestronglyMeasurable).add
        (hQP i j).aestronglyMeasurable
    have h4aem : AEStronglyMeasurable (fun x : X N =>
        Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) (volume.restrict (abox N ℓ)) := by
      have heq : (fun x : X N => Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x)
          = fun x : X N => Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + OM (x i) (x j)
                * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
                  + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
                  + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) := rfl
      rw [heq]
      exact (hQQ i j).aestronglyMeasurable.add (homm.mul hmid)
    have hS4aem : AEStronglyMeasurable (fun x : X N =>
        (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2)
        (volume.restrict (abox N ℓ)) := by
      have h1 := (h4aem.pow 2).const_mul (1 / 2 : ℝ)
      have hfe : (fun x : X N => (1 / 2) * ((fun y : X N =>
            Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) y) ^ 2) x)
          = fun x : X N => (1 / 2) * (Work.BoseFixB1S.boxQ4B volA A OM Φ (i, j) x) ^ 2 := by
        funext x
        rw [Pi.pow_apply]
      rwa [hfe] at h1
    have hInt := fragInt _ _ (by nlinarith [hC0, sq_nonneg C]) hb hS4aem
      (v) (v_integrable hv1) (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) i j hij
    simpa [Work.BoseFixB1S.fg4, hWdef, hOMdef] using hInt
  -- per-pair telescoping
  have hpair : ∀ (i j : Fin N), i ≠ j →
      Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
        + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
      = ∫ x in abox N ℓ, (Φ x) ^ 2 * W (x i) (x j) := by
    intro i j hij
    have ip1 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x) (abox N ℓ) volume :=
      (hI0 i j hij).add (hI1 i j hij)
    have ip2 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x) (abox N ℓ) volume := ip1.add (hI2a i j hij)
    have ip3 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x) (abox N ℓ) volume := ip2.add (hI2b i j hij)
    have ip4 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x) (abox N ℓ) volume := ip3.add (hI2c i j hij)
    have ip5 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x) (abox N ℓ) volume := ip4.add (hI3 i j hij)
    have ip6 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
        + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := ip5.add (hI4 i j hij)
    have iq1 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x) (abox N ℓ) volume :=
      (hI0 j i hij.symm).add (hI1 j i hij.symm)
    have iq2 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x) (abox N ℓ) volume := iq1.add (hI2a j i hij.symm)
    have iq3 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x) (abox N ℓ) volume := iq2.add (hI2b j i hij.symm)
    have iq4 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x) (abox N ℓ) volume := iq3.add (hI2c j i hij.symm)
    have iq5 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x) (abox N ℓ) volume := iq4.add (hI3 j i hij.symm)
    have iq6 : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
        + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) (abox N ℓ) volume := iq5.add (hI4 j i hij.symm)
    have hA' : Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
        = ∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ i j x
            + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
            + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
            + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
            + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) := by
      unfold Work.BoseFixB1S.pairInts
      rw [← integral_add (hI0 i j hij) (hI1 i j hij)]
      rw [← integral_add ip1 (hI2a i j hij)]
      rw [← integral_add ip2 (hI2b i j hij)]
      rw [← integral_add ip3 (hI2c i j hij)]
      rw [← integral_add ip4 (hI3 i j hij)]
      rw [← integral_add ip5 (hI4 i j hij)]
    have hB' : Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
        = ∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
            + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
            + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
            + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
            + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) := by
      unfold Work.BoseFixB1S.pairInts
      rw [← integral_add (hI0 j i hij.symm) (hI1 j i hij.symm)]
      rw [← integral_add iq1 (hI2a j i hij.symm)]
      rw [← integral_add iq2 (hI2b j i hij.symm)]
      rw [← integral_add iq3 (hI2c j i hij.symm)]
      rw [← integral_add iq4 (hI3 j i hij.symm)]
      rw [← integral_add iq5 (hI4 j i hij.symm)]
    have hF : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
        + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
        + Work.BoseFixB1S.fg4 volA A W OM Φ i j x) (abox N ℓ) volume := ip6
    have hG : IntegrableOn (fun x : X N => Work.BoseFixB1S.fg0 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
        + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
        + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
        + Work.BoseFixB1S.fg4 volA A W OM Φ j i x) (abox N ℓ) volume := iq6
    calc Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ i j
          + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ j i
        = (∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
              + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
              + Work.BoseFixB1S.fg4 volA A W OM Φ i j x))
            + (∫ x in abox N ℓ, (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
              + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
              + Work.BoseFixB1S.fg4 volA A W OM Φ j i x)) := by rw [hA', hB']
      _ = ∫ x in abox N ℓ, ((Work.BoseFixB1S.fg0 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg1 volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2a volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2b volA A W2 Φ i j x
              + Work.BoseFixB1S.fg2c volA A W1 Φ i j x
              + Work.BoseFixB1S.fg3 volA A W1 Φ i j x
              + Work.BoseFixB1S.fg4 volA A W OM Φ i j x)
            + (Work.BoseFixB1S.fg0 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg1 volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2a volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2b volA A W2 Φ j i x
              + Work.BoseFixB1S.fg2c volA A W1 Φ j i x
              + Work.BoseFixB1S.fg3 volA A W1 Φ j i x
              + Work.BoseFixB1S.fg4 volA A W OM Φ j i x)) := by
          rw [← integral_add hF hG]
      _ = ∫ x in abox N ℓ, Work.BoseFixB1S.fgsum volA A W W1 W2 OM Φ i j x := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Work.BoseFixB1S.fgsum]
          ring
      _ = ∫ x in abox N ℓ, (Φ x) ^ 2 * W (x i) (x j) := by
          apply integral_congr_ae
          filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
          rw [boxPairPointwise_bdd hℓ hvol' hA hvolA hAc
            (fun a b => by
              rw [hWdef]
              exact wSmallPair_symm hM u (fun z => radial_neg hvrad z) a b)
            (fun a b => by
              rw [hOMdef]; exact omC_chosen_sym h a b)
            (fun a b => by
              rw [hW1def, hWdef, hOMdef]
              simp only [wSmallPair, wSmallScaled, g0, omC]
              ring)
            (fun a b => by
              rw [hW2def, hWdef, hOMdef]
              simp only [wSmallPair, wSmallScaled, g2, omC]
              ring)
            hij hΦm hB0 hB x hx]
          by_cases hw : W (x i) (x j) = 0
          · rw [hw]; ring
          · obtain ⟨hxi, hxj⟩ := hsupA (x i) (x j) hw
            have h1 : Work.BoseFixB1S.Aind A (x i) = 1 := Set.indicator_of_mem hxi _
            have h2 : Work.BoseFixB1S.Aind A (x j) = 1 := Set.indicator_of_mem hxj _
            rw [h1, h2]; ring
  -- assemble
  rw [pairRaw_eq_sum_pairInts volA ℓ A W W1 W2 OM Φ]
  have hsym : (∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2)
      = (1 / 2) * ∑ p ∈ pairSet N,
          (Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2
            + Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.2 p.1) := by
    rw [Finset.sum_add_distrib,
      pairSet_swap_sum (fun p : Fin N × Fin N => Work.BoseFixB1S.pairInts volA ℓ A W W1 W2 OM Φ p.1 p.2)]
    ring
  rw [hsym]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact hpair p.1 p.2 (by simpa [pairSet] using hp)
/-- `pairRaw` at the sliding box equals `pairRaw`-free form (the mirror statement used by the
assembly): `pairRaw = ∫ Φ²·(½ Σ_p w)`. -/
theorem pairRaw_eq_integral_bdd {v : ℝ³ → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0)
    (u : ℝ³) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} (hΦm : Measurable Φ) {Bb : ℝ} (hB0 : 0 ≤ Bb)
    (hB : ∀ y ∈ abox N ℓ, |Φ y| ≤ Bb) :
    (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ pairSet N,
        wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = Work.BoseFixB1S.pairRaw (Work.SmallBoxSliding.boxMass ℓ d u) ℓ (dlBox ℓ d u)
          (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) (wSmallPair M ℓ d u (g2 v h))
          (omC (Classical.choose h)) Φ := by
  have h1 : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ pairSet N,
      wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N,
          wSmallPair M ℓ d u v (x p.1) (x p.2))) := by
    rw [← integral_const_mul (1 / 2 : ℝ)
      (fun x : X N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)))]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have h2 : (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N,
        wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2) := by
    rw [show (fun x : X N => (Φ x) ^ 2 * (∑ p ∈ pairSet N,
          wSmallPair M ℓ d u v (x p.1) (x p.2)))
        = fun x : X N => ∑ p ∈ pairSet N,
            (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2) from by
      funext x; rw [Finset.mul_sum]]
    exact integral_finsetSum (pairSet N) (fun p hp => by
      have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
      have hSb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |(Φ x) ^ 2| ≤ Bb ^ 2 :=
        (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ (fun x hx => by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2))
      exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd
        (v_integrable hv1) (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
        (hΦm.pow_const 2).aestronglyMeasurable (sq_nonneg Bb) hSb)
  rw [h1, h2, pairRaw_eq_dlBox_bdd hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦm hB0 hB]

/-! ## 7. The `μ`-part at `L^∞`-states -/

/-- Integrability on the box of a product `S x * F (x i)` where the slot factor `S` is a.e.
strongly measurable and a.e. bounded on `abox N ℓ`, and the fibre `F` is a.e. strongly
measurable on `acube ℓ` and bounded there. -/
theorem integrableOn_abox_slot_mul {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {F : ℝ³ → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |F z| ≤ C)
    {S : Submission.BoseGases.X N → ℝ}
    (hSm : AEStronglyMeasurable S (volume.restrict (Submission.BoseGases.abox N ℓ)))
    {B : ℝ} (hB : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox N ℓ)), |S x| ≤ B) :
    IntegrableOn (fun x : Submission.BoseGases.X N => S x * F (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
  have hAm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => S x * F (x i))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    hSm.mul (Submission.BoseGases.aem_comp_coord' i hFm)
  refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top N ℓ hℓ.le) hAm (B * C) ?_
  have hB' : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X N)),
      x ∈ Submission.BoseGases.abox N ℓ → |S x| ≤ B :=
    (ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)).mp hB
  rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
  filter_upwards [hB'] with x hx
  intro hmem
  have hFx : |F (x i)| ≤ C := hC (x i) (hmem i)
  have hSx : |S x| ≤ B := hx hmem
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hSx hFx (abs_nonneg _) (le_trans (abs_nonneg _) hSx)

/-- Pulling the constant `−μ` out of the integral and exchanging the finite slot sum with
the integral: the `μ`-part of the localised potential word is `−μ` times the slot sum of the
fibre weights. -/
theorem muPartFib_aux {N : ℕ} {ℓ μ : ℝ}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hInt : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i) := by
  have h1 : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (-μ) * ((Φ x) ^ 2 * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [h1, MeasureTheory.integral_const_mul]
  congr 1
  calc
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            ∑ i : Fin N, (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum]
      _ = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i) :=
          MeasureTheory.integral_finsetSum _
            (fun i _ => by simpa [IntegrableOn] using hInt i)
      _ = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
          simp only [Work.BoseFixB1S.boxMuPhi]

/-- The box-projection `μ`-sum identity: `Σᵢ boxMuP + 2 Σᵢ boxMuQP + Σᵢ boxMuQ = Σᵢ boxMuPhi`,
from the pointwise identity `(Pᵢ + Qᵢ)² = 1_A(xᵢ)·Φ²` and the vanishing of the fibre off `A`. -/
theorem boxMuSum_aux {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hvan : ∀ z : EuclideanSpace ℝ (Fin 3),
      z ∉ A → Submission.BoseGases.w1Fibre ℓ w1 z = 0)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hIntP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume)
    (hIntQP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume)
    (hIntQ : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      (Submission.BoseGases.abox N ℓ) volume) :
    (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
  have hper : ∀ i : Fin N,
      Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
        + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
        + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i
      = Work.BoseFixB1S.boxMuPhi (N := N) ℓ w1 Φ i := by
    intro i
    simp only [Work.BoseFixB1S.boxMuP, Work.BoseFixB1S.boxMuQP, Work.BoseFixB1S.boxMuQ,
      Work.BoseFixB1S.boxMuPhi]
    set fib : EuclideanSpace ℝ (Fin 3) → ℝ := Submission.BoseGases.w1Fibre ℓ w1 with hfibdef
    set P : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxPInd volA A i Φ with hPdef
    set Q : Submission.BoseGases.X N → ℝ := Work.UBBInputs8.boxQInd volA A i Φ with hQdef
    have hPt : ∀ x : Submission.BoseGases.X N,
        P x + Q x = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
      intro x
      rw [hPdef, hQdef]
      unfold Work.UBBInputs8.boxQInd
      ring
    have hkey : ∀ x : Submission.BoseGases.X N,
        P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)) + Q x ^ 2 * fib (x i)
          = Φ x ^ 2 * fib (x i) := by
      intro x
      have hind : A.indicator (fun _ => (1 : ℝ)) (x i) ^ 2
          = A.indicator (fun _ => (1 : ℝ)) (x i) := by
        by_cases hx : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have hsq : A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2
          = P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2 := by
        calc A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2
            = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) ^ 2 := by rw [mul_pow, hind]
          _ = (P x + Q x) ^ 2 := by rw [hPt x]
          _ = P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2 := by ring
      have hstep : (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2) * fib (x i)
          = Φ x ^ 2 * fib (x i) := by
        by_cases hx : x i ∈ A
        · rw [Set.indicator_of_mem hx, one_mul]
        · have hf0 : fib (x i) = 0 := hvan (x i) hx
          rw [Set.indicator_of_notMem hx, hf0]
          ring
      calc P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)) + Q x ^ 2 * fib (x i)
          = (P x ^ 2 + 2 * (Q x * P x) + Q x ^ 2) * fib (x i) := by ring
        _ = (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x ^ 2) * fib (x i) := by rw [hsq]
        _ = Φ x ^ 2 * fib (x i) := hstep
    have i1 : IntegrableOn (fun x : Submission.BoseGases.X N => P x ^ 2 * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hPdef, hfibdef] using hIntP i
    have i2 : IntegrableOn (fun x : Submission.BoseGases.X N => Q x * P x * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hPdef, hQdef, hfibdef] using hIntQP i
    have i2' : IntegrableOn (fun x : Submission.BoseGases.X N => 2 * (Q x * P x * fib (x i)))
        (Submission.BoseGases.abox N ℓ) volume := i2.const_mul 2
    have i3 : IntegrableOn (fun x : Submission.BoseGases.X N => Q x ^ 2 * fib (x i))
        (Submission.BoseGases.abox N ℓ) volume := by
      simpa only [hQdef, hfibdef] using hIntQ i
    have h12 : IntegrableOn (fun x : Submission.BoseGases.X N =>
        P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i)))
        (Submission.BoseGases.abox N ℓ) volume := i1.add i2'
    have h2G : 2 * (∫ x in Submission.BoseGases.abox N ℓ, Q x * P x * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ, 2 * (Q x * P x * fib (x i)) :=
      (MeasureTheory.integral_const_mul (2 : ℝ)
        (fun x : Submission.BoseGases.X N => Q x * P x * fib (x i))).symm
    have hA1 : (∫ x in Submission.BoseGases.abox N ℓ, P x ^ 2 * fib (x i))
          + (∫ x in Submission.BoseGases.abox N ℓ, 2 * (Q x * P x * fib (x i)))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) :=
      (MeasureTheory.integral_add i1 i2').symm
    have hA2 : (∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))))
          + (∫ x in Submission.BoseGases.abox N ℓ, Q x ^ 2 * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i) :=
      (MeasureTheory.integral_add h12 i3).symm
    have hA3 : (∫ x in Submission.BoseGases.abox N ℓ,
            (P x ^ 2 * fib (x i) + 2 * (Q x * P x * fib (x i))) + Q x ^ 2 * fib (x i))
        = ∫ x in Submission.BoseGases.abox N ℓ, Φ x ^ 2 * fib (x i) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact hkey x
    linarith [h2G, hA1, hA2, hA3]
  have hLHS : (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i)
        + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i)
        + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i)
      = ∑ i : Fin N, (Work.BoseFixB1S.boxMuP volA ℓ A w1 Φ i
          + 2 * Work.BoseFixB1S.boxMuQP volA ℓ A w1 Φ i
          + Work.BoseFixB1S.boxMuQ volA ℓ A w1 Φ i) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hLHS]
  exact Finset.sum_congr rfl (fun i _ => hper i)

theorem muPart_dlBox_bdd {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Bb : ℝ}
    (hB0 : 0 ≤ Bb) (hB : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Φ y| ≤ Bb) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 *
        (-μ * ∑ i : Fin N,
          Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmallPair M ℓ d u
            (Submission.BoseGases.g0 v h)) (x i)))
      = -μ * ((∑ i : Fin N, Work.BoseFixB1S.boxMuP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)
          + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)
          + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)) Φ i)) := by
  classical
  -- ### abbreviations for the localised kernel and the sliding box
  set W : ℝ³ → ℝ³ → ℝ := Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h)
    with hWdef
  set A : Set ℝ³ := Submission.BoseGases.dlBox ℓ d u with hAdef
  set volA : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hvolAdef
  have hAmeas : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvolA_eq : volA = (volume A).toReal := by
    rw [hvolAdef, hAdef, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  -- ### the localised fibre: a.e. strong measurability and uniform bound
  have hFm : AEStronglyMeasurable (Submission.BoseGases.w1Fibre ℓ W)
      (volume.restrict (Submission.BoseGases.acube ℓ)) := by
    have hint : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) volume :=
      Submission.BoseGases.g0_integrable hR0 hv_supp h
    have hm := Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (f := Submission.BoseGases.g0 v h) hint.aestronglyMeasurable.aemeasurable
    exact hm
  have hCb : ∀ z ∈ Submission.BoseGases.acube ℓ,
      |Submission.BoseGases.w1Fibre ℓ W z| ≤
        max 0 (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
          (2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) /
            Work.SmallBoxSliding.smallConvLower M * (8 * Real.pi * BoseGases.a v))) := by
    intro z _
    refine le_trans ?_ (le_max_right _ _)
    have h := Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      hM hℓ hd hR hRχ u z
    simpa only [hWdef, Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using h
  -- ### the fibre vanishes off the support box of the localised kernel
  have hvan : ∀ z : ℝ³, z ∉ A → Submission.BoseGases.w1Fibre ℓ W z = 0 := by
    intro z hz
    have hz0 : (fun y : ℝ³ => W z y) = fun _ => (0 : ℝ) := by
      funext y
      have hc : Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
        by_contra hne
        exact hz (by
          rw [hAdef]
          exact Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) hM hℓ hd (u := u) (x := z) hne)
      simp only [hWdef, Submission.BoseGases.wSmallPair, hc, zero_mul]
    simp only [Submission.BoseGases.w1Fibre, hz0, integral_zero]
  -- ### integrability of the four slot integrands on the box
  have hInt : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb (hΦm.pow_const 2).aestronglyMeasurable
      (B := Bb ^ 2) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Φ x) ^ 2| = |Φ x| ^ 2 := abs_pow _ 2
      _ ≤ Bb ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2
  set C : ℝ := Bb with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact hB0
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ C := fun x hx => by
    rw [hCdef]; exact hB x hx
  have hPb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C := by
    intro i x hx
    exact Work.BoseFixB1S.abs_boxPInd_le hℓ (by rw [hvolAdef]; exact hvol) hAmeas hvolA_eq hAc i hΦb x hx
  have hQb : ∀ i : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd volA A i Φ x| ≤ 2 * C := by
    intro i x hx
    have hQx : Work.UBBInputs8.boxQInd volA A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd volA A i Φ x := rfl
    rw [hQx]
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases hxi : x i ∈ A <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxi]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x - Work.UBBInputs8.boxPInd volA A i Φ x|
        ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd volA A i Φ x| := abs_sub _ _
      _ ≤ 1 * |Φ x| + C := by
          refine add_le_add ?_ (hPb i x hx)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hind (abs_nonneg _)
      _ ≤ 2 * C := by
          have h := hΦb x hx
          linarith
  have hIntP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      ((Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦm).pow_const 2).aestronglyMeasurable
      (B := C ^ 2) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2|
        = |Work.UBBInputs8.boxPInd volA A i Φ x| ^ 2 := abs_pow _ 2
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hPb i x hx) 2
  have hIntQP : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x
          * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      (((Work.SlotWord.measurable_boxQInd volA A hAmeas i hΦm).mul
        (Work.BoseFixB1S.measurable_boxPInd volA A hAmeas i hΦm)).aestronglyMeasurable)
      (B := (2 * C) * C) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    rw [abs_mul]
    exact mul_le_mul (hQb i x hx) (hPb i x hx) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hQb i x hx))
  have hIntQ : ∀ i : Fin N, IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ W (x i))
      (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hFm hCb
      ((Work.SlotWord.measurable_boxQInd volA A hAmeas i hΦm).pow_const 2).aestronglyMeasurable
      (B := (2 * C) ^ 2) ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2|
        = |Work.UBBInputs8.boxQInd volA A i Φ x| ^ 2 := abs_pow _ 2
      _ ≤ (2 * C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hQb i x hx) 2
  -- ### assembly: the two halves of the identity
  have hboxes : (∑ i : Fin N, Work.BoseFixB1S.boxMuP volA ℓ A W Φ i)
      + 2 * (∑ i : Fin N, Work.BoseFixB1S.boxMuQP volA ℓ A W Φ i)
      + (∑ i : Fin N, Work.BoseFixB1S.boxMuQ volA ℓ A W Φ i)
      = ∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ W Φ i :=
    boxMuSum_aux hvan hIntP hIntQP hIntQ
  have hfib : (∫ x in Submission.BoseGases.abox N ℓ,
        (Φ x) ^ 2 * (-μ * ∑ i : Fin N, Submission.BoseGases.w1Fibre ℓ W (x i)))
      = -μ * (∑ i : Fin N, Work.BoseFixB1S.boxMuPhi (N := N) ℓ W Φ i) :=
    muPartFib_aux hInt
  rw [hfib]
  congr 1
  rw [hWdef] at hboxes ⊢
  rw [hvolAdef, hAdef] at hboxes ⊢
  exact hboxes.symm



/-! ## 8. The assembled split at `L^∞`-states -/

theorem bqPotsplitBdd {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Bb : ℝ}
    (hB0 : 0 ≤ Bb) (hB : ∀ y ∈ Submission.BoseGases.abox N ℓ, |Φ y| ≤ Bb) :
    Submission.BoseGases.qLHSword (N := N) ℓ μ
        (Submission.BoseGases.wSmallPair M ℓ d u v)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
      = Work.BoseFixB1S.boxQSum (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ
          (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
          (Submission.BoseGases.omC (Classical.choose h)) Φ := by
  classical
  -- the two `μ`-free abbreviations used throughout
  set Cfib : ℝ := (chiSupAbs * chiSmallDecay M)
    * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
        * (8 * π * _root_.BoseGases.a v)) with hCfibdef
  have hfibb : ∀ z : ℝ³, |∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y| ≤ Cfib := by
    intro z
    rw [hCfibdef]
    exact wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hfibmeas : AEStronglyMeasurable
      (fun z : ℝ³ => ∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y)
      (volume.restrict (acube ℓ)) :=
    aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
      (g0_integrable hR0 hv_supp h).aemeasurable
  -- per-slot integrability of `Φ²·w₁-fibre`
  have hfibInt : ∀ i : Fin N, IntegrableOn (fun x : X N =>
      (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
      (abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_slot_mul hℓ i hfibmeas (fun z _ => hfibb z)
      (hΦm.pow_const 2).aestronglyMeasurable (B := Bb ^ 2) ?_
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    apply Filter.Eventually.of_forall
    intro x hx
    calc |(Φ x) ^ 2| = |Φ x| ^ 2 := abs_pow _ 2
      _ ≤ Bb ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2
  -- integrability of the `μ`-part of the left-hand side
  have hAint : IntegrableOn (fun x : X N => (Φ x) ^ 2 * (-μ * (∑ i : Fin N,
      w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)))) (abox N ℓ) volume := by
    have hsum : IntegrableOn (fun x : X N => ∑ i : Fin N,
        (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        (abox N ℓ) volume := by
      change Integrable (fun x : X N => ∑ i : Fin N,
        (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        (volume.restrict (abox N ℓ))
      exact integrable_finsetSum (Finset.univ : Finset (Fin N))
        (fun i _ => by simpa [IntegrableOn] using hfibInt i)
    refine (hsum.const_mul (-μ)).congr ?_
    filter_upwards with x
    have h1 : (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))
        = (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1]; ring
  -- integrability of the pair part of the left-hand side
  have hpairInt : ∀ p ∈ pairSet N, IntegrableOn (fun x : X N =>
      (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    have hSb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |(Φ x) ^ 2| ≤ Bb ^ 2 :=
      (ae_restrict_iff' (abox_measurable N ℓ)).mpr (ae_of_all _ (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2))
    exact integrableOn_slot_wSmallPair (N := N) (R := R0) hℓ hd (v_integrable hv1)
      (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hM hR hRχ u hne
      (hΦm.pow_const 2).aestronglyMeasurable (sq_nonneg Bb) hSb
  have hBint : IntegrableOn (fun x : X N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N,
      wSmallPair M ℓ d u v (x p.1) (x p.2)))) (abox N ℓ) volume := by
    have hsum : IntegrableOn (fun x : X N => ∑ p ∈ pairSet N,
        (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2)) (abox N ℓ) volume := by
      change Integrable (fun x : X N => ∑ p ∈ pairSet N,
        (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2))
        (volume.restrict (abox N ℓ))
      exact integrable_finsetSum (pairSet N)
        (fun p hp => by simpa [IntegrableOn] using hpairInt p hp)
    refine (hsum.const_mul (1 / 2)).congr ?_
    filter_upwards with x
    have h1 : (∑ p ∈ pairSet N, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x p.1) (x p.2))
        = (Φ x) ^ 2 * (∑ p ∈ pairSet N, wSmallPair M ℓ d u v (x p.1) (x p.2)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h1]; ring
  -- the left-hand side splits into its `μ`-part and its pair part
  have hsplit : Submission.BoseGases.qLHSword (N := N) ℓ μ
        (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) Φ
      = (∫ x in abox N ℓ, (Φ x) ^ 2 * (-μ * (∑ i : Fin N,
          w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i))))
        + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N,
            wSmallPair M ℓ d u v (x p.1) (x p.2)))) := by
    rw [show Submission.BoseGases.qLHSword (N := N) ℓ μ
          (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h)) Φ
        = ∫ x in abox N ℓ, (Φ x) ^ 2 * ((-μ * (∑ i : Fin N,
              w1Fibre ℓ (wSmallPair M ℓ d u (g0 v h)) (x i)))
            + ((1 / 2) * (∑ p ∈ pairSet N,
                wSmallPair M ℓ d u v (x p.1) (x p.2)))) from rfl]
    rw [← integral_add hAint hBint]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [show wSmall1Pair h M ℓ d u = wSmallPair M ℓ d u (g0 v h) from rfl]
  rw [hsplit]
  rw [muPart_dlBox_bdd hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦm hB0 hB]
  rw [pairRaw_eq_integral_bdd hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u hvol hΦm hB0 hB]
  rw [boxQSum_eq' (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ (dlBox ℓ d u)
    (wSmallPair M ℓ d u v) (wSmallPair M ℓ d u (g0 v h))
    (wSmallPair M ℓ d u (g2 v h)) (omC (Classical.choose h)) Φ]
  ring

end Work.BoseFixB1C
