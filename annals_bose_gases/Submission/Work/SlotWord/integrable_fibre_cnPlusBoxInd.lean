import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.aemeasurable_fibreAmpEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.integrable_fibre_cnPlusBoxInd`

**Integrability of the fibre excited count `n₊` of a slot piece.**  For a measurable box
`A ⊆ acube L`, a slot set `S : Finset (Fin N)`, a bijection `e : SlotIn N S ≃ Fin S.card` and a
measurable state `Ψ` bounded by `C` on the box `abox N L`, the outside-configuration function

  `y ↦ n₊(A, slotFibreState S e (slotPiece A S Ψ) y)`

is Bochner-integrable against the volume restricted to the outside configurations
`slotOutside L A S = slotBox (acube L ∩ Aᶜ)`.

This is the (R3)-side condition of the `n₊`-half of the fibre factorisation of the word
(`Work.SlotWord.integral_slotFibre_cnPlusBoxInd`): the corresponding *identity* of integrals
separates the `y`-integral from the `ζ`-integral, and the Bochner convention `∫ = 0` for a
non-integrable function makes the exchange meaningful only under this bookkeeping.

The argument has two halves, both elementary and both available for *arbitrary* `volA` (the
statement does not normalise the box by its volume):

* **the pointwise bound.**  For `y ∈ slotOutside L A S` and `ζ ∈ abox S.card L`, the fibre
  `slotFibreState S e (slotPiece A S Ψ) y` only ever evaluates `Ψ` at configurations of `abox N L`
  (every in-box coordinate of the reassembly lies in `acube L` because `ζ` does, and every outside
  coordinate does because `y ∈ slotOutside`), so it is bounded by `C` there.  FS's mean-free
  projection is then bounded by

    `|Q_{A,i} (fibre) ζ| ≤ C + |volA|⁻¹ · (C · |A|)`,

  uniformly in `y`, and hence

    `|n₊(A, fibre)| ≤ S.card · ((C + |volA|⁻¹·(C·|A|))² · |abox S.card L|)`.

  (The `|A|` in the mean term is what replaces the normalisation `volA = |A|` of the corpus's
  `abs_boxQInd_le`; it costs nothing because the domain `slotOutside L A S` is bounded.)
* **the a.e. strong measurability** — the joint map
  `(y, ζ) ↦ Q_{A,i}(fibre_y)(ζ)` is measurable (`measurable_boxQInd_fibre`), so its square is, and
  Mathlib's `StronglyMeasurable.integral_prod_right'` gives the measurability of the `ζ`-integral
  in `y`; a finite sum over the slots closes it.

The domain `slotOutside L A S` has finite measure (it sits in `slotBox (acube L)`, a finite product
of cubes), so `Integrable.of_bound` finishes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBBInputs8
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.SlotWord

variable {N : ℕ}

/-! ## 1. Two elementary estimates -/

/-- **The box mean of a bounded function, with an arbitrary normalisation.**  If `|f| ≤ C` on `A`
and `A` has finite measure, then for *any* real `c`

    `|c · ∫_A f| ≤ |c| · (C · |A|)`.

The corpus's `Work.SlotWord.abs_mul_inv_mul_setIntegral_le` states the case `c = 1 / volA` with
`volA = |A|` (where the right-hand side collapses to `C`); here the normalisation is kept
symbolically, which is what the fibre estimate needs for an unnormalised `volA`. -/
theorem abs_mul_setIntegral_le_of_bound {A : Set ℝ³} {f : ℝ³ → ℝ} {C : ℝ}
    (hfin : (volume : Measure ℝ³) A < ⊤) (hb : ∀ z ∈ A, |f z| ≤ C) (c : ℝ) :
    |c * ∫ z in A, f z| ≤ |c| * (C * (volume : Measure ℝ³).real A) := by
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ³)) (s := A) (f := f)
    hfin (fun z hz => by simpa [Real.norm_eq_abs] using hb z hz)
  simpa using h

/-- **FS's mean-free projection is bounded, with an unnormalised `volA`.**  If the box `A` sits
inside `acube L` and the state is bounded by `C` on every configuration with all coordinates in
`acube L`, then for every such configuration

    `|Q_{A,i} Ψ x| ≤ C + |volA|⁻¹ · (C · |A|)`.

The box mean stays inside `acube L` (because `A ⊆ acube L` and the other coordinates of `x` do), so
`C` bounds it; the prefactor `|volA|⁻¹ · |A|` is the price of not normalising `volA` to the volume
of `A`.  The degenerate case `volA = 0` is handled by the convention `1/0 = 0`. -/
theorem abs_boxQInd_le_volA {N : ℕ} (L : ℝ) {A : Set ℝ³} (hAL : A ⊆ acube L) {volA : ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hfin : (volume : Measure ℝ³) A < ⊤)
    {Ψ : X N → ℝ} (hΨ : ∀ x : X N, (∀ j : Fin N, x j ∈ acube L) → |Ψ x| ≤ C) (i : Fin N) :
    ∀ x : X N, (∀ j : Fin N, x j ∈ acube L) →
      |boxQInd volA A i Ψ x| ≤ C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A) := by
  intro x hx
  have hQeq : boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) := by
    simp only [boxQInd, boxPInd]
    ring
  rw [hQeq]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi, one_mul]
    have h1 : |Ψ x| ≤ C := hΨ x hx
    have h2 : |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)|
        ≤ |volA|⁻¹ * (C * (volume : Measure ℝ³).real A) := by
      have hbd : ∀ z ∈ A, |Ψ (Function.update x i z)| ≤ C := by
        intro z hz
        refine hΨ _ ?_
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hAL hz
        · rw [if_neg hj]; exact hx j
      have h := abs_mul_setIntegral_le_of_bound (A := A)
        (f := fun z => Ψ (Function.update x i z)) (C := C) hfin hbd (1 / volA)
      simpa [one_div] using h
    calc |Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)|
        ≤ |Ψ x| + |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)| := abs_sub _ _
      _ ≤ C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A) := add_le_add h1 h2
  · rw [Set.indicator_of_notMem hxi, zero_mul, abs_zero]
    exact add_nonneg hC
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg volA)) (mul_nonneg hC measureReal_nonneg))

/-! ## 2. The fibre of a slot piece is bounded on the box -/

/-- **The fibre of a slot piece is bounded by `C`.**  If `y` is outside the box `A` (its
coordinates lie in `acube L` and outside `A`) and `x` has all its coordinates in `acube L`, then
the reassembled configuration `slotComb S (x ∘ e) y` has all its coordinates in `acube L`, hence
lies in the corpus box `abox N L`, where `|Ψ| ≤ C`.  The slot piece can only decrease the modulus
(it is an indicator times `Ψ`). -/
theorem abs_slotFibreState_slotPiece_le {N : ℕ} (L : ℝ) {A : Set ℝ³} (hAc : A ⊆ acube L)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) {Ψ : X N → ℝ} {C : ℝ}
    (hΨb : ∀ x ∈ abox N L, |Ψ x| ≤ C) (y : SlotOut N S → ℝ³) (hy : y ∈ slotOutside L A S) :
    ∀ x : X S.card, (∀ k : Fin S.card, x k ∈ acube L) →
      |slotFibreState S e (slotPiece A S Ψ) y x| ≤ C := by
  intro x hx
  rw [slotFibreState_apply]
  have hbox : slotComb S (fun i : SlotIn N S => x (e i)) y ∈ abox N L := by
    rw [mem_abox_iff]
    intro j
    rw [slotComb_apply]
    by_cases hj : j ∈ S
    · rw [dif_pos hj]
      exact hx (e ⟨j, hj⟩)
    · rw [dif_neg hj]
      exact (mem_slotOutside_iff.mp hy).1 ⟨j, hj⟩
  have h1 : |slotPiece A S Ψ (slotComb S (fun i : SlotIn N S => x (e i)) y)|
      ≤ |Ψ (slotComb S (fun i : SlotIn N S => x (e i)) y)| := by
    by_cases h : slotComb S (fun i : SlotIn N S => x (e i)) y ∈ slotSet A S
    · rw [slotPiece, Set.indicator_of_mem h]
    · rw [slotPiece, Set.indicator_of_notMem h, abs_zero]
      exact abs_nonneg _
  exact h1.trans (hΨb _ hbox)

/-! ## 3. The pointwise bound on the fibre excited count -/

/-- **The fibre excited count is bounded, uniformly in the outside configuration.**  For
`y ∈ slotOutside L A S`,

    `|n₊(A, slotFibreState S e (slotPiece A S Ψ) y)| ≤ S.card · ((C + |volA|⁻¹·(C·|A|))² · |abox S.card L|)`.

The `ζ`-integral is over the box `abox S.card L` (finite measure), where each projected square is
bounded by `D²` with `D := C + |volA|⁻¹·(C·|A|)`. -/
theorem abs_cnPlusBoxInd_slotFibreState_le {N : ℕ} (L : ℝ) (hL : 0 < L)
    {A : Set ℝ³} (hA : MeasurableSet A) (hAc : A ⊆ acube L) (volA : ℝ)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : 0 ≤ C)
    (hΨb : ∀ x ∈ abox N L, |Ψ x| ≤ C) (y : SlotOut N S → ℝ³)
    (hy : y ∈ slotOutside L A S) :
    |cnPlusBoxInd L A volA (slotFibreState S e (slotPiece A S Ψ) y)|
      ≤ (S.card : ℝ) *
          ((C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A))^2
            * (volume : Measure (X S.card)).real (abox S.card L)) := by
  set D : ℝ := C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact add_nonneg hC
      (mul_nonneg (inv_nonneg.mpr (abs_nonneg volA)) (mul_nonneg hC measureReal_nonneg))
  have hAfin : (volume : Measure ℝ³) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hAc) (acube_lt_top L hL.le)
  have hGb := abs_slotFibreState_slotPiece_le L hAc S e hΨb y hy
  have hQ : ∀ (i : Fin S.card) (x : X S.card), (∀ k : Fin S.card, x k ∈ acube L) →
      |boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x| ≤ D := by
    intro i x hx
    have h := abs_boxQInd_le_volA (volA := volA) L hAc hC hAfin hGb i x hx
    simpa [hDdef] using h
  have hInt : ∀ i : Fin S.card,
      ∫ x in abox S.card L, (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2
        ≤ D^2 * (volume : Measure (X S.card)).real (abox S.card L) := by
    intro i
    haveI hfinbox : IsFiniteMeasure ((volume : Measure (X S.card)).restrict (abox S.card L)) :=
      isFiniteMeasure_restrict.mpr (ne_of_lt (abox_lt_top S.card L hL.le))
    have hgint : Integrable (fun _ : X S.card => D^2)
        ((volume : Measure (X S.card)).restrict (abox S.card L)) := by
      rw [integrable_const_iff]
      exact Or.inr hfinbox
    have hmono := integral_mono_of_nonneg
      (μ := (volume : Measure (X S.card)).restrict (abox S.card L))
      (f := fun x : X S.card =>
        (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2)
      (g := fun _ : X S.card => D^2)
      (Eventually.of_forall (fun x => sq_nonneg _)) hgint
      (by
        filter_upwards [ae_restrict_mem (abox_measurable S.card L)] with x hx
        have hx' : ∀ k : Fin S.card, x k ∈ acube L := (mem_abox_iff S.card L x).mp hx
        exact sq_le_sq' (abs_le.mp (hQ i x hx')).1 (abs_le.mp (hQ i x hx')).2)
    calc ∫ x in abox S.card L, (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2
        ≤ ∫ x in abox S.card L, D^2 := hmono
      _ = D^2 * (volume : Measure (X S.card)).real (abox S.card L) := by
          rw [setIntegral_const, smul_eq_mul]
          ring
  have hnn : ∀ i : Fin S.card, 0 ≤ ∫ x in abox S.card L,
      (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2 :=
    fun i => integral_nonneg (fun x => sq_nonneg _)
  rw [show cnPlusBoxInd L A volA (slotFibreState S e (slotPiece A S Ψ) y)
      = ∑ i : Fin S.card, ∫ x in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2 from rfl]
  calc |∑ i : Fin S.card, ∫ x in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2|
      ≤ ∑ i : Fin S.card, |∫ x in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin S.card, ∫ x in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2 :=
        Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hnn i))
    _ ≤ ∑ _i : Fin S.card, D^2 * (volume : Measure (X S.card)).real (abox S.card L) :=
        Finset.sum_le_sum (fun i _ => hInt i)
    _ = (S.card : ℝ) * (D^2 * (volume : Measure (X S.card)).real (abox S.card L)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (S.card : ℝ) *
          ((C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A))^2
            * (volume : Measure (X S.card)).real (abox S.card L)) := by
        rw [hDdef]

/-! ## 4. A.e. strong measurability of the fibre excited count -/

/-- **The fibre excited count is a.e. strongly measurable.**  The joint map
`(y, ζ) ↦ Q_{A,i}(slotFibreState S e (slotPiece A S Ψ) y) ζ` is measurable
(`measurable_boxQInd_fibre`); squaring and integrating in `ζ` over the box preserves measurability
in `y` (`StronglyMeasurable.integral_prod_right'`), and a finite sum over the slots closes. -/
theorem aestronglyMeasurable_cnPlusBoxInd_slotFibreState' {N : ℕ} (L : ℝ)
    {A : Set ℝ³} (hA : MeasurableSet A) (volA : ℝ)
    (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card)
    {Ψ : X N → ℝ} (hΨ : Measurable Ψ) :
    AEStronglyMeasurable
      (fun y : SlotOut N S → ℝ³ =>
        cnPlusBoxInd L A volA (slotFibreState S e (slotPiece A S Ψ) y))
      ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S)) := by
  have hΨ' : Measurable (slotPiece A S Ψ) := slotPiece_measurable A hA S hΨ
  have hper : AEStronglyMeasurable (fun y : SlotOut N S → ℝ³ =>
      ∑ i : Fin S.card, ∫ x in abox S.card L,
        (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2)
      ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S)) := by
    have hle : ∀ i : Fin S.card, AEStronglyMeasurable (fun y : SlotOut N S → ℝ³ =>
        ∫ x in abox S.card L,
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2)
        ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S)) := by
      intro i
      have hQ2 : Measurable (fun p : (SlotOut N S → ℝ³) × X S.card =>
          (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) p.1) p.2)^2) :=
        (measurable_boxQInd_fibre (N := N) volA A hA S e i hΨ').pow_const 2
      exact (hQ2.stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure (X S.card)).restrict (abox S.card L))).measurable.aestronglyMeasurable
    have hsum := Finset.aestronglyMeasurable_sum (M := ℝ)
      (μ := (volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S))
      (Finset.univ : Finset (Fin S.card))
      (f := fun (i : Fin S.card) (y : SlotOut N S → ℝ³) => ∫ x in abox S.card L,
        (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2)
      (fun i _ => hle i)
    refine hsum.congr (Eventually.of_forall (fun y => ?_))
    exact Finset.sum_apply y Finset.univ (fun (i : Fin S.card) (y : SlotOut N S → ℝ³) =>
      ∫ x in abox S.card L, (boxQInd volA A i (slotFibreState S e (slotPiece A S Ψ) y) x)^2)
  refine hper.congr (Eventually.of_forall (fun y => ?_))
  rfl

/-! ## 5. The target -/

theorem integrable_fibre_cnPlusBoxInd {N : ℕ} (L : ℝ) (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube L) (volA : ℝ)
    (S : Finset (Fin N)) (e : Work.PerSector.SlotIn N S ≃ Fin S.card)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : 0 ≤ C)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N L, |Ψ x| ≤ C) :
    MeasureTheory.Integrable
      (fun y : Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.cnPlusBoxInd L A volA
          (Work.PerSector.slotFibreState S e (Work.PerSector.slotPiece A S Ψ) y))
      ((MeasureTheory.volume : MeasureTheory.Measure
        (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
        (Work.PerSector.slotOutside L A S)) := by
  -- the outside configurations form a measurable set inside a finite product of cubes
  have hmeasA : MeasurableSet (slotOutside L A S) :=
    Work.PerSector.Work.PerSector.slotBox_measurable
      ((acube_measurable L).inter hA.compl)
  have hsub : slotOutside L A S ⊆ slotBox (ι := SlotOut N S) (acube L) :=
    Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left
  have hfin : (volume : Measure (SlotOut N S → ℝ³)) (slotOutside L A S) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    rw [volume_pi,
      show slotBox (ι := SlotOut N S) (acube L)
          = Set.univ.pi (fun _ : SlotOut N S => acube L) from by
        ext z; simp [slotBox, Set.mem_pi],
      Measure.pi_pi (fun _ : SlotOut N S => (volume : Measure ℝ³)) (fun _ => acube L)]
    exact ENNReal.prod_lt_top (fun _ _ => acube_lt_top L hL.le)
  haveI : IsFiniteMeasure ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hfin)
  refine Integrable.of_bound (aestronglyMeasurable_cnPlusBoxInd_slotFibreState' L hA volA S e hΨ)
    ((S.card : ℝ) *
      ((C + |volA|⁻¹ * (C * (volume : Measure ℝ³).real A))^2
        * (volume : Measure (X S.card)).real (abox S.card L))) ?_
  filter_upwards [ae_restrict_mem hmeasA] with y hy
  rw [Real.norm_eq_abs]
  exact abs_cnPlusBoxInd_slotFibreState_le L hL hA hAc volA S e hΨ hC hΨb y hy

end Work.SlotWord
