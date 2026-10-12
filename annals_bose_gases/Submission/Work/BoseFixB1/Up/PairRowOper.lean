import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1S.BoxPotOper
import Submission.Work.BoseFixB1S.BoxQIndCore
import Submission.Work.BoseFixB1S.boxConstCalibB1
import Submission.Work.BoseFixB1S.flatPairEraseB1
import Submission.Work.LocRepoint.chiMass_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.PairRowOper` — the flat pair identity, in the `BoxPotOper` branch

The flat-branch pair identity `flatPairMeanFieldCorrectedB1BF` lives in
`Submission/Work/BoseFixB1B/flatPairMeanFieldExactlyFlatFixed.lean`, whose cone reaches
`Submission/Work/BoseFixB1S.flatPairMeanFieldB1`.  That module declares
`Work.BoseFixB1S.boxQInd_eq`, and `Submission/Work/BoseFixB1S.BoxPotOper` declares a lemma of the
same name; Lean refuses to import both modules into one environment, so *no* module can hold the
pair identity together with the `BoxPotOper` cluster (the flat fibre identity
`Work.BoseFixB1S.flatFibreMeanFieldB1`, the peel `boxPInd_fib_collapse`, ...).

This module resolves the clash by **moving the pair row into the `BoxPotOper` branch**: it is a
verbatim copy of the two source modules below (minus their two `sorry`-ed, unused theorems, and
with `flatPairMeanFieldB1`'s `boxQInd_eq` renamed `boxQInd_eq_slotProj`, since `BoxPotOper` owns
that name), together with the definitions of `flatPairMeanFieldB1` that the copies use
(`slotProj`, `boxPInd_eq_slotProj`, `slotProj_kcInsN`).

Copied (with `import`s replaced by this module's own header):

* `Submission/Work/BoseFixB1S/flatPairMeanFieldB1.lean` — its `slotProj` layer;
* `Submission/Work/BoseFixB1S/flatPairTermAB1.lean` — everything after the imports;
* `Submission/Work/BoseFixB1B/flatPairMeanFieldExactlyFlatFixed.lean` — everything after the
  imports up to (excluding) the `sorry`-ed, refuted statement `flatPairMeanFieldExactlyFlatFixed`
  of its §9.

Nothing here is new mathematics. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases Work.SmallBoxSliding Work.UBBInputs8

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- The box average in slot `i`, *without* the box indicator: the `volA⁻¹∫_A` factor of
`Work.UBBInputs8.boxPInd`. -/
noncomputable def slotProj (volA : ℝ) (A : Set E3) {n : ℕ} (i : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) : Submission.BoseGases.X n → ℝ :=
  fun x => (1 / volA) * ∫ z in A, Φ (Function.update x i z)

lemma boxPInd_eq_slotProj (volA : ℝ) (A : Set E3) {n : ℕ} (i : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) :
    boxPInd volA A i Φ
      = fun x => slotProj volA A i Φ x * A.indicator (fun _ => (1 : ℝ)) (x i) := rfl

/-- `boxQInd` in the `1_A·(Φ − TᵢΦ)` form. -/
lemma boxQInd_eq_slotProj (volA : ℝ) (A : Set E3) {n : ℕ} (i : Fin n)
    (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x - slotProj volA A i Φ x) := by
  rw [boxQInd, boxPInd_eq_slotProj]
  ring

/-- `Tᵢ` at a one-slot insertion. -/
lemma slotProj_kcInsN {volA : ℝ} {A : Set E3} {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (t : E3) (r : Submission.BoseGases.X n) :
    slotProj volA A i Φ (kcInsN n i (t, r))
      = (1 / volA) * ∫ z in A, Φ (kcInsN n i (z, r)) := by
  unfold slotProj
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  exact congrArg Φ (update_kcInsN i t z r)

end Work.BoseFixB1S

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open Submission.BoseGases Work.SmallBoxSliding Work.UBBInputs8

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The pair projection vs. the slot-double-mean -/

/-- `P_i (P_j Φ)` is the product of the two box indicators times the slot-double-mean
`T_i (T_j Φ)`; the indicators come out because `i ≠ j` makes the inner indicator
independent of the outer integration variable. -/
theorem boxPInd_pair_eq_indicator_mul_slotProj (volA : ℝ) (A : Set E3) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (Φ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * slotProj volA A i (slotProj volA A j Φ) x := by
  have hupd : ∀ z : E3, (Function.update x i z) j = x j := by
    intro z
    rw [Function.update_apply, if_neg (Ne.symm hij)]
  have hL : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = (1 / volA) * ((∫ z in A, ((1 / volA) * ∫ w in A,
            Φ (Function.update (Function.update x i z) j w)))
              * A.indicator (fun _ => (1 : ℝ)) (x j))
        * A.indicator (fun _ => (1 : ℝ)) (x i) := by
    rw [Work.UBBInputs8.boxPInd]
    have hpt : ∀ z : E3, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i z)
        = ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w))
          * A.indicator (fun _ => (1 : ℝ)) (x j) := by
      intro z
      rw [Work.UBBInputs8.boxPInd, hupd z]
    simp only [hpt]
    rw [MeasureTheory.integral_mul_const]
  have hR : slotProj volA A i (slotProj volA A j Φ) x
      = (1 / volA) * ∫ z in A,
          ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    simp only [slotProj]
  rw [hL, hR]
  ring

/-! ## 2. `chiSmallB`: continuity, support, degeneracies -/

theorem chiSmallB_continuous_pairRow {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    Continuous (fun x : E3 => chiSmallB M ℓ d u x) := by
  have h1 : Continuous (fun x : E3 => chiScale ℓ x) := chiScale_continuous ℓ
  have h2 : Continuous (fun x : E3 => chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    (chiSmall_continuous hM).comp
      ((continuous_id.const_smul ((ℓ * d)⁻¹)).sub continuous_const)
  show Continuous (fun x : E3 => chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u))
  exact h1.mul h2

theorem chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) {x : E3} (hx : x ∉ dlBox ℓ d u) : chiSmallB M ℓ d u x = 0 := by
  by_contra h
  exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd h)

theorem wSmallPair_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) {v : E3 → ℝ} {x y : E3}
    (h : x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) : wSmallPair M ℓ d u v x y = 0 := by
  rcases h with hx | hy
  · rw [Submission.BoseGases.wSmallPair, chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hx]
    ring
  · rw [Submission.BoseGases.wSmallPair, chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hy]
    ring

/-- Pointwise vanishing of the cutoff when the sliding box is a null set (the
support of `chiSmallB` is an *open* subset of `dlBox`). -/
theorem chiSmallB_eq_zero_of_volume_dlBox_eq_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (h : (MeasureTheory.volume : MeasureTheory.Measure E3) (dlBox ℓ d u) = 0) :
    chiSmallB M ℓ d u = 0 := by
  have hsub : Function.support (chiSmallB M ℓ d u) ⊆ dlBox ℓ d u := by
    intro x hx
    exact Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd (Function.mem_support.mp hx)
  have hcont := chiSmallB_continuous_pairRow (M := M) hM ℓ d u
  have hopen : IsOpen (Function.support (chiSmallB M ℓ d u)) := by
    have heq : Function.support (chiSmallB M ℓ d u)
        = (chiSmallB M ℓ d u) ⁻¹' ({0}ᶜ : Set ℝ) := by
      ext y
      simp [Function.mem_support]
    rw [heq]
    exact isOpen_compl_singleton.preimage hcont
  funext x
  by_contra hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure E3) (dlBox ℓ d u) :=
    lt_of_lt_of_le (Metric.measure_ball_pos _ x hr) (measure_mono (hball.trans hsub))
  rw [h] at hpos
  exact lt_irrefl 0 hpos

/-- Pointwise vanishing of the cutoff from a vanishing `chiMass` (the cutoff is continuous
and nonnegative, so `∫ χ² = 0` forces `χ ≡ 0`). -/
theorem chiSmallB_eq_zero_of_chiMass_eq_zero {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (h : chiMass M ℓ d u = 0) :
    chiSmallB M ℓ d u = 0 := by
  have hint : Integrable (fun x : E3 => (chiSmallB M ℓ d u x) ^ 2) :=
    Work.LocRepoint.integrable_chiSmallB_sq_slice hM hℓ u
  have hzero : (∫ x : E3, (chiSmallB M ℓ d u x) ^ 2) = 0 := by
    rw [← Work.SmallBoxSliding.chiMass_def]
    exact h
  have hsupp0 : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Function.support (fun x : E3 => (chiSmallB M ℓ d u x) ^ 2)) = 0 := by
    have hiff := integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (chiSmallB M ℓ d u x))) hint
    rw [hzero] at hiff
    have hnot : ¬ (0 < (MeasureTheory.volume : MeasureTheory.Measure E3)
        (Function.support (fun x : E3 => (chiSmallB M ℓ d u x) ^ 2))) :=
      fun hh => absurd (hiff.mpr hh) (lt_irrefl 0)
    exact le_antisymm (not_lt.mp hnot) bot_le
  have hsupp : Function.support (fun x : E3 => (chiSmallB M ℓ d u x) ^ 2)
      = Function.support (chiSmallB M ℓ d u) := by
    ext x
    simp [Function.mem_support]
  have hcont := chiSmallB_continuous_pairRow (M := M) hM ℓ d u
  have hopen : IsOpen (Function.support (chiSmallB M ℓ d u)) := by
    have heq : Function.support (chiSmallB M ℓ d u)
        = (chiSmallB M ℓ d u) ⁻¹' ({0}ᶜ : Set ℝ) := by
      ext y
      simp [Function.mem_support]
    rw [heq]
    exact isOpen_compl_singleton.preimage hcont
  funext x
  by_contra hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Function.support (chiSmallB M ℓ d u)) :=
    lt_of_lt_of_le (Metric.measure_ball_pos _ x hr) (measure_mono hball)
  rw [← hsupp, hsupp0] at hpos
  exact lt_irrefl 0 hpos

/-- The `A × A`-integral of `χ(y)²χ(z)²` is `chiMass²`. -/
theorem setIntegral_dlBox_pair_chiSq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    (∫ z in dlBox ℓ d u, ∫ y in dlBox ℓ d u,
        (chiSmallB M ℓ d u y) ^ 2 * (chiSmallB M ℓ d u z) ^ 2)
      = (chiMass M ℓ d u) ^ 2 := by
  have hcongr : (∫ z in dlBox ℓ d u, ∫ y in dlBox ℓ d u,
        (chiSmallB M ℓ d u y) ^ 2 * (chiSmallB M ℓ d u z) ^ 2)
      = ∫ z in dlBox ℓ d u,
          ((∫ y in dlBox ℓ d u, (chiSmallB M ℓ d u y) ^ 2)
            * (chiSmallB M ℓ d u z) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [MeasureTheory.integral_mul_const]
  rw [hcongr, MeasureTheory.integral_const_mul,
    chiMass_eq_setIntegral_dlBox (M := M) hM hℓ hd u]
  ring

/-- The two-variable weight `χ(y)²χ(z)²` is integrable on `B(u) × B(u)`. -/
theorem integrable_chiSmallB_sq_pair {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) :
    Integrable (fun q : E3 × E3 =>
        (chiSmallB M ℓ d u q.1) ^ 2 * (chiSmallB M ℓ d u q.2) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict
        (dlBox ℓ d u ×ˢ dlBox ℓ d u)) := by
  have h1 : Integrable (fun x : E3 => (chiSmallB M ℓ d u x) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u)) :=
    (Work.LocRepoint.integrable_chiSmallB_sq_slice hM hℓ u).mono_measure
      Measure.restrict_le_self
  have h2 := h1.mul_prod h1
  rwa [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod] at h2

/-- The pair integrand may be replaced by its slot-double-mean value a.e.: on the support of
`wSmallPair` both slots lie in the box, where the erasure hypothesis says `Φ = T_iT_jΦ`. -/
theorem eraseIntegrand_wSmallPair {v : E3 → ℝ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) {n : ℕ} {Φ : X n → ℝ} {i j : Fin n} (hij : i ≠ j)
    (herase : (fun x : X n => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j)
        * (Φ x - slotProj (boxMass ℓ d u) (dlBox ℓ d u) i
            (slotProj (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x))
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)] 0) :
    (fun x : X n => (Φ x) ^ 2 * wSmallPair M ℓ d u v (x i) (x j))
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)]
    (fun x : X n => (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
          (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x) ^ 2
        * wSmallPair M ℓ d u v (x i) (x j)) := by
  filter_upwards [herase] with x hx
  simp only [Pi.zero_apply] at hx
  have hP2 := boxPInd_pair_eq_indicator_mul_slotProj (boxMass ℓ d u) (dlBox ℓ d u) hij Φ x
  rw [hP2]
  by_cases h1 : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
      * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 0
  · have hw : wSmallPair M ℓ d u v (x i) (x j) = 0 := by
      by_cases hi : chiSmallB M ℓ d u (x i) = 0
      · rw [Submission.BoseGases.wSmallPair, hi]
        ring
      · by_cases hj : chiSmallB M ℓ d u (x j) = 0
        · rw [Submission.BoseGases.wSmallPair, hj]
          ring
        · exfalso
          have hmi := Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hi
          have hmj := Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hj
          rw [Set.indicator_of_mem hmi, Set.indicator_of_mem hmj, one_mul] at h1
          exact one_ne_zero h1
    rw [h1, hw]
    ring
  · have hΦ : Φ x = slotProj (boxMass ℓ d u) (dlBox ℓ d u) i
        (slotProj (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x := by
      rcases mul_eq_zero.mp hx with h2 | h2
      · exact absurd h2 h1
      · exact sub_eq_zero.mp h2
    have hind : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 1 := by
      have ha : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) = 1 := by
        by_cases hxi : x i ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hxi]
        · exact absurd (by rw [Set.indicator_of_notMem hxi, zero_mul]) h1
      have hb : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 1 := by
        by_cases hxj : x j ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hxj]
        · exact absurd (by rw [Set.indicator_of_notMem hxj, mul_zero]) h1
      rw [ha, hb, one_mul]
    rw [hind, one_mul, ← hΦ]

/-- The `χ²χ²`-weighted integrand may likewise be replaced by its slot-double-mean value a.e. -/
theorem eraseIntegrand_chiSq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) {n : ℕ} {Φ : X n → ℝ} {i j : Fin n} (hij : i ≠ j)
    (herase : (fun x : X n => (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j)
        * (Φ x - slotProj (boxMass ℓ d u) (dlBox ℓ d u) i
            (slotProj (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x))
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)] 0) :
    (fun x : X n => (Φ x) ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2
        * (chiSmallB M ℓ d u (x j)) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict (abox n ℓ)]
    (fun x : X n => (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
          (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x) ^ 2
        * (chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x j)) ^ 2) := by
  filter_upwards [herase] with x hx
  simp only [Pi.zero_apply] at hx
  have hP2 := boxPInd_pair_eq_indicator_mul_slotProj (boxMass ℓ d u) (dlBox ℓ d u) hij Φ x
  rw [hP2]
  by_cases h1 : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
      * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 0
  · have hw : (chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x j)) ^ 2 = 0 := by
      by_cases hi : chiSmallB M ℓ d u (x i) = 0
      · rw [hi]
        ring
      · by_cases hj : chiSmallB M ℓ d u (x j) = 0
        · rw [hj]
          ring
        · exfalso
          have hmi := Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hi
          have hmj := Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hj
          rw [Set.indicator_of_mem hmi, Set.indicator_of_mem hmj, one_mul] at h1
          exact one_ne_zero h1
    rw [h1, mul_assoc, hw]
    ring
  · have hΦ : Φ x = slotProj (boxMass ℓ d u) (dlBox ℓ d u) i
        (slotProj (boxMass ℓ d u) (dlBox ℓ d u) j Φ) x := by
      rcases mul_eq_zero.mp hx with h2 | h2
      · exact absurd h2 h1
      · exact sub_eq_zero.mp h2
    have hind : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 1 := by
      have ha : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) = 1 := by
        by_cases hxi : x i ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hxi]
        · exact absurd (by rw [Set.indicator_of_notMem hxi, zero_mul]) h1
      have hb : (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) = 1 := by
        by_cases hxj : x j ∈ dlBox ℓ d u
        · rw [Set.indicator_of_mem hxj]
        · exact absurd (by rw [Set.indicator_of_notMem hxj, mul_zero]) h1
      rw [ha, hb, one_mul]
    rw [hind, one_mul, ← hΦ]

/-- The global nested `wSmallPair`-integral collapses to the `B(u) × B(u)` integral (the kernel
vanishes off the sliding box; the remaining Fubini swap is where `hInt` is used). -/
theorem flatPairMass_eq_dlBox_pair {v : E3 → ℝ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : E3 × E3 => wSmallPair M ℓ d u v p.1 p.2) (acube ℓ ×ˢ acube ℓ)) :
    Work.BoseFixB1.flatPairMass v M ℓ d u
      = ∫ z in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u v y z := by
  have hinner : ∀ x : E3, (∫ y : E3, wSmallPair M ℓ d u v x y)
      = ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u v x y :=
    fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inr hy))).symm
  have h1 : Work.BoseFixB1.flatPairMass v M ℓ d u
      = ∫ x in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u v x y := by
    rw [Work.BoseFixB1.flatPairMass]
    simp only [hinner]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by
        rw [show (fun y : E3 => wSmallPair M ℓ d u v x y) = fun _ => (0 : ℝ) from
          funext (fun y => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hx))]
        simp)).symm
  rw [h1]
  have hsub : dlBox ℓ d u ×ˢ dlBox ℓ d u ⊆ acube ℓ ×ˢ acube ℓ :=
    Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
      (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
  have hint2 : Integrable (fun q : E3 × E3 => wSmallPair M ℓ d u v q.1 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u))) := by
    rw [Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
    exact hInt.mono_set hsub
  have hprod : (∫ x in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u v x y)
      = ∫ q : E3 × E3, wSmallPair M ℓ d u v q.1 q.2
          ∂(((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u)).prod
            ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u))) :=
    (MeasureTheory.integral_prod _ hint2).symm
  have hsymm : (∫ q : E3 × E3, wSmallPair M ℓ d u v q.1 q.2
          ∂(((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u)).prod
            ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict (dlBox ℓ d u))))
      = ∫ z in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u v y z :=
    MeasureTheory.integral_prod_symm _ hint2
  rw [hprod, hsymm]

theorem flatPairTermAB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) {i j : Fin n} (hij : i ≠ j) (herase : (fun x : Submission.BoseGases.X n => (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j) * (Φ x - Work.BoseFixB1S.slotProj (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) i (Work.BoseFixB1S.slotProj (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) j Φ) x)) =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0) (hInt : MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2) (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x i) (x j)) = (Work.BoseFixB1.flatPairMass v M ℓ d u / (Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2) * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2 := by
  by_cases hvol0 : (MeasureTheory.volume : MeasureTheory.Measure E3) (dlBox ℓ d u) = 0
  · -- Case 0: the sliding box is a null set, so the cutoff vanishes identically.
    have hχ0 : chiSmallB M ℓ d u = 0 :=
      chiSmallB_eq_zero_of_volume_dlBox_eq_zero hM hℓ hd u hvol0
    have hK0 : ∀ a b : E3, wSmallPair M ℓ d u v a b = 0 := by
      intro a b
      simp [Submission.BoseGases.wSmallPair, hχ0]
    have hFPM0 : Work.BoseFixB1.flatPairMass v M ℓ d u = 0 := by
      rw [Work.BoseFixB1.flatPairMass]
      simp [hK0]
    have hκ0 : chiMass M ℓ d u = 0 := by
      rw [Work.SmallBoxSliding.chiMass_def]
      simp [hχ0]
    have hL0 : (∫ x in abox n ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x i) (x j)) = 0 := by
      simp [hK0]
    rw [hL0, hFPM0, hκ0]
    simp
  · -- Case 1: `B(u)` has positive measure.
    have hVpos : 0 < boxMass ℓ d u := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
      exact ENNReal.toReal_pos hvol0
        (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
    cases n with
    | zero => exact absurd i.isLt (Nat.not_lt_zero _)
    | succ m =>
      cases m with
      | zero =>
        refine absurd (Fin.ext ?_) hij
        have hi := i.isLt
        have hj := j.isLt
        omega
      | succ p =>
        rcases Fin.exists_succAbove_eq (x := j) (y := i) hij.symm with ⟨j', hj'⟩
        subst hj'
        have hsub : dlBox ℓ d u ×ˢ dlBox ℓ d u ⊆ acube ℓ ×ˢ acube ℓ :=
          Set.prod_mono (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
            (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
        have hhK : Integrable (fun q : E3 × E3 => wSmallPair M ℓ d u v q.1 q.2)
            ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict
              (dlBox ℓ d u ×ˢ dlBox ℓ d u)) := hInt.mono_set hsub
        have hhC : Integrable (fun q : E3 × E3 =>
              (chiSmallB M ℓ d u q.1) ^ 2 * (chiSmallB M ℓ d u q.2) ^ 2)
            ((MeasureTheory.volume : MeasureTheory.Measure (E3 × E3)).restrict
              (dlBox ℓ d u ×ˢ dlBox ℓ d u)) := integrable_chiSmallB_sq_pair hM hℓ hd u
        have hPK := Q0C.pair_kernel (volA := boxMass ℓ d u) (A := dlBox ℓ d u) hℓ hVpos
          (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
          (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
          (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u) i j' hΦc
          (h := fun y z => wSmallPair M ℓ d u v y z) hhK
        have hPC := Q0C.pair_kernel (volA := boxMass ℓ d u) (A := dlBox ℓ d u) hℓ hVpos
          (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
          (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
          (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u) i j' hΦc
          (h := fun y z => (chiSmallB M ℓ d u y) ^ 2 * (chiSmallB M ℓ d u z) ^ 2) hhC
        have hE1 : (∫ x in abox (p + 2) ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x i) (x (i.succAbove j')))
            = ∫ x in abox (p + 2) ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
                  (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
                * wSmallPair M ℓ d u v (x i) (x (i.succAbove j')) :=
          integral_congr_ae (eraseIntegrand_wSmallPair (v := v) hM hℓ hd u hij herase)
        have hE2 : (∫ x in abox (p + 2) ℓ, (Φ x) ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2
              * (chiSmallB M ℓ d u (x (i.succAbove j'))) ^ 2)
            = ∫ x in abox (p + 2) ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
                  (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
                * (chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x (i.succAbove j'))) ^ 2 :=
          integral_congr_ae (eraseIntegrand_chiSq hM hℓ hd u hij herase)
        have hI1 : (∫ x in abox (p + 2) ℓ, (Φ x) ^ 2 * wSmallPair M ℓ d u v (x i) (x (i.succAbove j')))
            = Work.BoseFixB1.flatPairMass v M ℓ d u
              * ∫ r2 in abox p ℓ,
                  (Q0C.pairRest (boxMass ℓ d u) (dlBox ℓ d u) i j' Φ r2) ^ 2 := by
          rw [hE1, hPK, flatPairMass_eq_dlBox_pair hM hℓ hd u hInt]
        have hmass : (∫ x in abox (p + 2) ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
                (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
              * (chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x (i.succAbove j'))) ^ 2)
            = ∫ x in abox (p + 2) ℓ, (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) i
                (boxPInd (boxMass ℓ d u) (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
                * ((chiSmallB M ℓ d u (x i)) ^ 2 * (chiSmallB M ℓ d u (x (i.succAbove j'))) ^ 2) := by
          apply integral_congr_ae
          filter_upwards with y
          ring
        have hI2 : (∫ x in abox (p + 2) ℓ, (Φ x) ^ 2 * (chiSmallB M ℓ d u (x i)) ^ 2
              * (chiSmallB M ℓ d u (x (i.succAbove j'))) ^ 2)
            = (chiMass M ℓ d u) ^ 2
              * ∫ r2 in abox p ℓ,
                  (Q0C.pairRest (boxMass ℓ d u) (dlBox ℓ d u) i j' Φ r2) ^ 2 := by
          rw [hE2, hmass, hPC, setIntegral_dlBox_pair_chiSq hM hℓ hd u]
        rw [hI1, hI2]
        by_cases hκ : chiMass M ℓ d u = 0
        · have hχ0 := chiSmallB_eq_zero_of_chiMass_eq_zero hM hℓ hd u hκ
          have hK0 : ∀ a b : E3, wSmallPair M ℓ d u v a b = 0 := by
            intro a b
            simp [Submission.BoseGases.wSmallPair, hχ0]
          have hFPM0 : Work.BoseFixB1.flatPairMass v M ℓ d u = 0 := by
            rw [Work.BoseFixB1.flatPairMass]
            simp [hK0]
          rw [hFPM0, hκ]
          simp
        · have hκ2 : (chiMass M ℓ d u) ^ 2 ≠ 0 := pow_ne_zero 2 hκ
          field_simp

end Work.BoseFixB1S

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. Elementary combinatorial helpers -/

/-- Membership in the ordered distinct-pair set. -/
theorem mem_pairSetB1BF {N : ℕ} {p : Fin N × Fin N} :
    p ∈ Submission.BoseGases.pairSet N ↔ p.1 ≠ p.2 := by
  simp [Submission.BoseGases.pairSet]

/-- The iterated `j ≠ i` sum is the `pairSet N` sum (`{i} × (univ.erase i)` partitions the
ordered distinct pairs). -/
theorem sum_erase_eq_pairSetB1BF {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i : Fin N, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, f i j)
      = ∑ p ∈ Submission.BoseGases.pairSet N, f p.1 p.2 := by
  rw [Submission.BoseGases.pairSet, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `(Σᵢ fᵢ)² = Σᵢ fᵢ² + Σ_{ordered distinct pairs} f_{p.1}f_{p.2}`. -/
theorem sq_sum_eq_sum_sq_add_pairSetB1BF {N : ℕ} (f : Fin N → ℝ) :
    (∑ i, f i) ^ 2 = (∑ i, f i ^ 2) + ∑ p ∈ Submission.BoseGases.pairSet N, f p.1 * f p.2 := by
  have h2 : ∀ i : Fin N, (∑ j : Fin N, f i * f j)
      = f i * f i + ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, f i * f j := by
    intro i
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N)) (fun j => f i * f j)
      (Finset.mem_univ i)]
    ring
  calc (∑ i, f i) ^ 2 = (∑ i, f i) * (∑ j, f j) := by rw [sq]
    _ = ∑ i, ∑ j, f i * f j :=
        Finset.sum_mul_sum (Finset.univ : Finset (Fin N)) Finset.univ f f
    _ = ∑ i, (f i * f i + ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, f i * f j) :=
        Finset.sum_congr rfl (fun i _ => h2 i)
    _ = (∑ i, f i * f i)
          + ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin N)).erase i, f i * f j :=
        Finset.sum_add_distrib
    _ = (∑ i, f i ^ 2) + ∑ p ∈ Submission.BoseGases.pairSet N, f p.1 * f p.2 := by
        rw [sum_erase_eq_pairSetB1BF (fun i j => f i * f j)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The parse of the target's right-hand side, machine-checked: the set-integral notation swallows
the trailing subtraction, so `∫ x in s, f x - c` is `∫ x in s, (f x - c)`. -/
theorem setIntegral_parse_is_nested (s : Set ℝ) (f : ℝ → ℝ) (c : ℝ) :
    (∫ x in s, f x - c) = ∫ x in s, (f x - c) := rfl

/-! ## 1. Integrability on the box of continuous functions, and continuity helpers -/

theorem integrableOn_abox_of_continuousB1BF {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : Submission.BoseGases.X N → ℝ} (hf : Continuous f) :
    IntegrableOn f (Submission.BoseGases.abox N ℓ) :=
  hf.continuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hℓ)

theorem continuous_chiSmallB_applyB1BF {N : ℕ} {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3)
    (i : Fin N) :
    Continuous (fun x : Submission.BoseGases.X N => Submission.BoseGases.chiSmallB M ℓ d u (x i)) :=
  (Work.BoseFixB1S.chiSmallB_continuous_pairRow hM ℓ d u).comp (continuous_apply i)

theorem continuous_chiFourthSumB1BF {N : ℕ} {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    Continuous (fun x : Submission.BoseGases.X N =>
      ∑ i : Fin N, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4) :=
  continuous_finsetSum _
    (fun i _ => (continuous_chiSmallB_applyB1BF hM ℓ d u i).pow 4)

theorem continuous_pairSummandB1BF {N : ℕ} {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (p : Fin N × Fin N) :
    Continuous (fun x : Submission.BoseGases.X N =>
      (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
        * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2) :=
  (((hΦc.pow 2).mul ((continuous_chiSmallB_applyB1BF hM ℓ d u p.1).pow 2)).mul
    ((continuous_chiSmallB_applyB1BF hM ℓ d u p.2).pow 2))

theorem continuous_pairSumB1BF {N : ℕ} {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : Submission.BoseGases.X N =>
      ∑ p ∈ Submission.BoseGases.pairSet N,
        (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
          * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2) :=
  continuous_finsetSum _ (fun p _ => continuous_pairSummandB1BF hM ℓ d u hΦc p)

/-- `nCountB` is continuous (it is the finite sum `Σᵢ χ(xᵢ)²`). -/
theorem continuous_nCountB_applyB1BF {N : ℕ} {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    Continuous (fun x : Submission.BoseGases.X N => Work.BoseFixB1.nCountB M ℓ d u x) := by
  have hχ : Continuous (fun y : E3 => Submission.BoseGases.chiSmallB M ℓ d u y) :=
    Work.BoseFixB1S.chiSmallB_continuous_pairRow hM ℓ d u
  rw [show (fun x : Submission.BoseGases.X N => Work.BoseFixB1.nCountB M ℓ d u x)
      = fun x : Submission.BoseGases.X N =>
          ∑ i : Fin N, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 from by
    funext x; rw [Work.BoseFixB1.nCountB]]
  exact continuous_finsetSum _ (fun i _ => (hχ.comp (continuous_apply i)).pow 2)

/-! ## 2. Integrability of a pair pullback times a bounded state -/

/-- The pair pullback `x ↦ w(x i, x j)` of a kernel integrable on the cube is integrable over the
box (`Submission.BoseGases.integrableOn_pair_comp_ae`), for an arbitrary particle number `N`
written as `m + 2`. -/
theorem integrableOn_pair_pullbackB1BF {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w2 : E3 × E3 → ℝ} (hw2 : IntegrableOn w2 (Submission.BoseGases.acube ℓ ×ˢ
      Submission.BoseGases.acube ℓ)) :
    IntegrableOn (fun x : Submission.BoseGases.X N => w2 (x i, x j))
      (Submission.BoseGases.abox N ℓ) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := by
    have hne : (i : ℕ) ≠ (j : ℕ) := fun hh => hij (Fin.ext hh)
    exact ⟨N - 2, by omega⟩
  exact Submission.BoseGases.integrableOn_pair_comp_ae hℓ i j hij hw2

/-- `Φ² · w(x i, x j)` is integrable over the box when `Φ` is continuous there and `w` is
integrable on the cube. -/
theorem integrableOn_pair_mulB1BF {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {w2 : E3 × E3 → ℝ}
    (hw2 : IntegrableOn w2 (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    IntegrableOn (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 * w2 (x i, x j))
      (Submission.BoseGases.abox N ℓ) := by
  have hw2i : IntegrableOn (fun x : Submission.BoseGases.X N => w2 (x i, x j))
      (Submission.BoseGases.abox N ℓ) := integrableOn_pair_pullbackB1BF hℓ hij hw2
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := fun x => (Φ x) ^ 2) ((hΦc.pow 2).continuousOn)
  refine (hw2i.abs.const_mul (max C 0)).mono' ?_ ?_
  · exact (hΦc.pow 2).aestronglyMeasurable.mul hw2i.aestronglyMeasurable
  · rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all _ (fun x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h := hC x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Φ x))] at h
      exact le_trans h (le_max_left C 0))

/-! ## 3. The pair erasure in `slotProj` form -/

theorem pairErasure_of_flatB1BF {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0)
    {i j : Fin N} (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X N =>
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)
        * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x j)
        * (Φ x - Work.BoseFixB1S.slotProj (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i
            (Work.BoseFixB1S.slotProj (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) j Φ) x))
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)] 0 := by
  filter_upwards [Work.BoseFixB1S.flatPairEraseB1 (ℓ := ℓ) (d := d) hℓ hd u hM hΦc hflat hij]
    with x hx
  rw [Work.BoseFixB1S.boxPInd_pair_eq_indicator_mul_slotProj (Work.SmallBoxSliding.boxMass ℓ d u)
    (Submission.BoseGases.dlBox ℓ d u) hij Φ x] at hx
  simp only [Pi.zero_apply] at hx
  rw [mul_sub]
  exact hx

/-! ## 4. The volume of the box (the source of the discrepancy) -/

theorem volume_abox_toRealB1BF {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (MeasureTheory.volume (Submission.BoseGases.abox n ℓ)).toReal = ℓ ^ (3 * n) := by
  rw [Submission.BoseGases.abox_volume n ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity), pow_mul]

/-! ## 5. The left-hand side: `flatPairSum` as the ordered-pair sum -/

theorem flatPairSum_eq_pairSetSumB1BF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    Work.BoseFixB1.flatPairSum v M ℓ d u Φ
      = (1 / 2) * (Work.BoseFixB1.flatPairMass v M ℓ d u
            * ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2)
          * (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x in Submission.BoseGases.abox n ℓ,
                (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2) := by
  have hw2 : IntegrableOn (fun p : E3 × E3 => Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := hInt
  have hIntPair : ∀ (i j : Fin n) (hij : i ≠ j),
      IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x i) (x j))
        (Submission.BoseGases.abox n ℓ) :=
    fun i j hij => integrableOn_pair_mulB1BF hℓ hij hΦc hw2
  have hPairVal : ∀ (i j : Fin n) (hij : i ≠ j),
      (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x i) (x j))
        = (Work.BoseFixB1.flatPairMass v M ℓ d u
            / (Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
          * ∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x j)) ^ 2 :=
    fun i j hij => Work.BoseFixB1S.flatPairTermAB1 h hM hℓ hd u hΦc hij
      (pairErasure_of_flatB1BF hM hℓ hd u hΦc hflat hij) hw2
  rw [Work.BoseFixB1.flatPairSum]
  have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
      = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) := by
    rw [show (fun x : Submission.BoseGases.X n =>
          (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)))
        = (fun x : Submission.BoseGases.X n =>
            (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
              (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) from by
      funext x
      rw [← Finset.mul_sum]
      ring]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum]
    intro p hp
    exact hIntPair p.1 p.2 (mem_pairSetB1BF.mp hp)
  rw [h1, Finset.sum_congr rfl (fun p hp => hPairVal p.1 p.2 (mem_pairSetB1BF.mp hp))]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [div_eq_mul_inv, inv_pow]
  ring

/-! ## 6. The two integrals of the right-hand side -/

/-- `nCountB x = Σᵢ χ(xᵢ)²`, so `∫_{abox} Φ²(nCountB)²` splits into the diagonal term
`∫Φ²Σᵢχ(xᵢ)⁴` and the ordered-pair sum. -/
theorem nCountB_sq_integral_eqB1BF {n : ℕ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : E3) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x) ^ 2)
      = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)
        + ∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x in Submission.BoseGases.abox n ℓ,
              (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2 := by
  have hpt : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x) ^ 2
        = (Φ x) ^ 2 * (∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)
          + ∑ p ∈ Submission.BoseGases.pairSet n,
              (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2 := by
    intro x
    rw [Work.BoseFixB1.nCountB,
      sq_sum_eq_sum_sq_add_pairSetB1BF
        (fun i : Fin n => (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)]
    rw [mul_add]
    congr 1
    · exact congrArg (fun z => (Φ x) ^ 2 * z)
        (Finset.sum_congr rfl (fun i _ => by ring))
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
            ((Φ x) ^ 2 * (∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)
              + ∑ p ∈ Submission.BoseGases.pairSet n,
                  (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                    * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2) := by
    apply integral_congr_ae
    filter_upwards with x
    exact hpt x
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ x) ^ 2 * (∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)
            + ∑ p ∈ Submission.BoseGases.pairSet n,
                (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2))
      = (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)
          + (∫ x in Submission.BoseGases.abox n ℓ,
              ∑ p ∈ Submission.BoseGases.pairSet n,
                (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
                  * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2) :=
    MeasureTheory.integral_add
      (integrableOn_abox_of_continuousB1BF hℓ
        ((hΦc.pow 2).mul (continuous_chiFourthSumB1BF hM ℓ d u)))
      (integrableOn_abox_of_continuousB1BF hℓ
        (continuous_pairSumB1BF hM ℓ d u hΦc))
  have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ,
          ∑ p ∈ Submission.BoseGases.pairSet n,
            (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2)
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (Submission.BoseGases.chiSmallB M ℓ d u (x p.1)) ^ 2
              * (Submission.BoseGases.chiSmallB M ℓ d u (x p.2)) ^ 2 :=
    MeasureTheory.integral_finsetSum (Submission.BoseGases.pairSet n)
      (fun p _ => integrableOn_abox_of_continuousB1BF hℓ
        (continuous_pairSummandB1BF hM ℓ d u hΦc p))
  rw [hstep1, hstep2, hstep3]

/-- `(nCountB x / κ)² = (κ⁻¹)² (nCountB x)²`. -/
theorem nCountB_div_sq_integral_eqB1BF {n : ℕ} {M : ℕ} (ℓ d : ℝ) (u : E3)
    {Φ : Submission.BoseGases.X n → ℝ} :
    (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
      = ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2
        * ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x) ^ 2 := by
  rw [show (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
      = (fun x : Submission.BoseGases.X n =>
          ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2
            * ((Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x) ^ 2)) from by
    funext x
    ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## 7. The intended identity (the repaired statement) -/

theorem flatPairMeanFieldCorrectedB1BF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    Work.BoseFixB1.flatPairSum v M ℓ d u Φ
      = (1 / 2) * Work.BoseFixB1.flatPairMass v M ℓ d u
          * ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
              - ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2
                * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
                    ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 4)) := by
  rw [flatPairSum_eq_pairSetSumB1BF h hM hℓ hd u hΦc hflat hInt,
    nCountB_div_sq_integral_eqB1BF (M := M) ℓ d u,
    nCountB_sq_integral_eqB1BF hM hℓ u hΦc]
  ring

/-! ## 8. The discrepancy: the written statement's right-hand side -/

/-- **The volume factor.**  A set integral of `A x - c` with a *constant* `c` subtracts
`c · volume (abox n ℓ) = c · ℓ^{3n}`, not `c`. -/
theorem innerIntegral_sub_constB1BF {n : ℕ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : E3) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) (C : ℝ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ((Φ x) ^ 2 *
            (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2
          - ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2 * C))
      = (∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
            / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2)
        - ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2 * C * ℓ ^ (3 * n) := by
  have hcont1 : Continuous (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (Work.BoseFixB1.nCountB M ℓ d u x / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2) :=
    (hΦc.pow 2).mul (((continuous_nCountB_applyB1BF hM ℓ d u).div_const _).pow 2)
  rw [MeasureTheory.integral_sub
    (integrableOn_abox_of_continuousB1BF hℓ hcont1)
    (integrableOn_abox_of_continuousB1BF hℓ continuous_const)]
  rw [MeasureTheory.integral_const, Measure.real_def, Measure.restrict_apply_univ,
    volume_abox_toRealB1BF hℓ, smul_eq_mul]
  ring

/-- **The refutation core.**  The term actually written in the target's right-hand side (the
*nested* reading: the second box integral sits inside the first one's body, where it is a constant)
equals `flatPairSum` plus the discrepancy
`½ · flatPairMass · κ⁻² · (1 − ℓ^{3n}) · ∫_{abox}Φ²Σᵢχ(xᵢ)⁴`.  Hence the target statement is
equivalent to `flatPairMass · (1 − ℓ^{3n}) · ∫_{abox}Φ²Σᵢχ(xᵢ)⁴ = 0`. -/
theorem flatPairRHS_written_eqB1BF {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hflat : Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) Φ = 0)
    (hInt : MeasureTheory.IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmallPair M ℓ d u v p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    (1 / 2) * Work.BoseFixB1.flatPairMass v M ℓ d u *
        (∫ x in Submission.BoseGases.abox n ℓ,
          ((Φ x) ^ 2 * (Work.BoseFixB1.nCountB M ℓ d u x
              / Work.SmallBoxSliding.chiMass M ℓ d u) ^ 2
            - ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2
              * (∫ y in Submission.BoseGases.abox n ℓ, (Φ y) ^ 2 *
                  ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (y i)) ^ 4)))
      = Work.BoseFixB1.flatPairSum v M ℓ d u Φ
        + (1 / 2) * Work.BoseFixB1.flatPairMass v M ℓ d u
            * ((Work.SmallBoxSliding.chiMass M ℓ d u)⁻¹) ^ 2 * (1 - ℓ ^ (3 * n))
            * (∫ y in Submission.BoseGases.abox n ℓ, (Φ y) ^ 2 *
                ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (y i)) ^ 4) := by
  rw [innerIntegral_sub_constB1BF hM hℓ u hΦc
      (∫ y in Submission.BoseGases.abox n ℓ, (Φ y) ^ 2 *
        ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d u (y i)) ^ 4),
    flatPairMeanFieldCorrectedB1BF h hM hℓ hd u hΦc hflat hInt,
    nCountB_div_sq_integral_eqB1BF (M := M) ℓ d u,
    nCountB_sq_integral_eqB1BF hM hℓ u hΦc]
  ring


end Work.BoseFixB1B
