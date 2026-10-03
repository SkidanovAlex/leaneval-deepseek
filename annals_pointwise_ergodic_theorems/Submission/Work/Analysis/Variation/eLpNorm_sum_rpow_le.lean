import Mathlib
import Submission.Port.Aesm

/-! ### A note on the name `MeasureTheory.AEMeasurable`

The statement below refers to the a.e.-measurability predicate as `MeasureTheory.AEMeasurable`,
the name it has in most revisions of Mathlib.  In the revision pinned in this workspace that
predicate is declared one level up, in the *root* namespace (`_root_.AEMeasurable`, see
`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`), so the name `MeasureTheory.AEMeasurable`
does not exist there and the statement below would not even elaborate.

To keep the requested statement verbatim, the name `MeasureTheory.AEMeasurable` is introduced
below as a `protected abbrev` of the root declaration.  It is definitionally transparent, so the
mathematical content is unchanged; being `protected` it does not pollute the unqualified name
space of files that `open MeasureTheory` (there `AEMeasurable` still means the root name). -/

namespace MeasureTheory

protected abbrev AEMeasurable {α β : Type*} [MeasurableSpace β] {_m : MeasurableSpace α}
    (f : α → β) (μ : Measure α) : Prop := _root_.AEMeasurable f μ

end MeasureTheory

namespace Work.Analysis.Variation

open MeasureTheory

/-- Pointwise quasi-subadditivity of `t ↦ t ^ q` on `ℝ≥0∞` for `0 < q ≤ 1`: the `q`-th power of a
finite sum is at most the sum of the `q`-th powers.  Immediate by induction from the two-term
inequality `ENNReal.rpow_add_le_add_rpow` (concavity of `t ↦ t ^ q`). -/
private lemma finset_sum_rpow_le {ι : Type*} {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (s : Finset ι) (x : ι → ENNReal) :
    (∑ i ∈ s, x i) ^ q ≤ ∑ i ∈ s, (x i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hq0]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (ENNReal.rpow_add_le_add_rpow (x a) (∑ i ∈ s, x i) hq0.le hq1).trans
        (add_le_add_right ih _)

/-- For a fixed real exponent `q`, the map `t ↦ t ^ q` is Borel measurable on `ℝ≥0∞` (it is the
composition of the jointly measurable rpow with a constant), hence it preserves a.e.-measurability
of `ℝ≥0∞`-valued functions. -/
private lemma aemeasurable_rpow_const {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℝ} {g : α → ENNReal} (hg : _root_.AEMeasurable g μ) :
    _root_.AEMeasurable (fun a => g a ^ q) μ := by
  fun_prop

/-- The quasi-triangle inequality in `L^q` for `0 < q ≤ 1`, for `ENNReal`-valued a.e.-measurable
functions: for a finite family `(g i)` of functions `α → ENNReal`, each a.e.-measurable,
`(eLpNorm (∑_{i ∈ s} g i) (ofReal q) μ)^q ≤ ∑_{i ∈ s} (eLpNorm (g i) (ofReal q) μ)^q`.
The a.e.-measurability hypothesis is necessary: `lintegral` is the lower integral, which is not
subadditive for arbitrary functions.  Proof: for `ENNReal`-valued functions the `L^q` "norm" is
`(∫⁻ (∑_i g i)^q)^{1/q}` (`eLpNorm_eq_lintegral_rpow_enorm_toReal`, using `‖h‖ₑ = h` for
`h : α → ENNReal`); use `(∑_i g i)^q ≤ ∑_i (g i)^q` pointwise (concavity of `t ↦ t^q` for
`q ≤ 1`, i.e. `ENNReal.rpow_add_le_add_rpow` iterated), monotonicity of the lintegral, and
`MeasureTheory.lintegral_finsetSum'`. -/
theorem eLpNorm_sum_rpow_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {ι α : Type*}
    [MeasurableSpace α] {μ : MeasureTheory.Measure α} (s : Finset ι) (g : ι → α → ENNReal)
    (hg : ∀ i ∈ s, MeasureTheory.AEMeasurable (g i) μ) :
    (MeasureTheory.eLpNorm (fun a => ∑ i ∈ s, g i a) (ENNReal.ofReal q) μ) ^ q
      ≤ ∑ i ∈ s, (MeasureTheory.eLpNorm (g i) (ENNReal.ofReal q) μ) ^ q := by
  have hq_ne : q ≠ 0 := hq0.ne'
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hptop : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  -- For `ENNReal`-valued functions, raising the `L^q` quantity to the power `q` gives back the
  -- lower integral of the `q`-th power.
  have key : ∀ f : α → ENNReal, MeasureTheory.AEMeasurable f μ →
      (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q = ∫⁻ a, f a ^ q ∂μ := by
    intro f hf
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    simp only [enorm_eq_self]
    rw [← ENNReal.rpow_mul, div_mul_cancel₀ 1 hq_ne, ENNReal.rpow_one]
  rw [key (fun a => ∑ i ∈ s, g i a) (Finset.aemeasurable_fun_sum s hg)]
  calc ∫⁻ a, (∑ i ∈ s, g i a) ^ q ∂μ
      ≤ ∫⁻ a, ∑ i ∈ s, (g i a) ^ q ∂μ :=
        lintegral_mono fun a => finset_sum_rpow_le hq0 hq1 s (fun i => g i a)
    _ = ∑ i ∈ s, ∫⁻ a, (g i a) ^ q ∂μ :=
        lintegral_finsetSum' s (f := fun i a => (g i a) ^ q)
          (fun i hi => aemeasurable_rpow_const (hg i hi))
    _ = ∑ i ∈ s, (MeasureTheory.eLpNorm (g i) (ENNReal.ofReal q) μ) ^ q :=
        Finset.sum_congr rfl fun i hi => (key (g i) (hg i hi)).symm

end Work.Analysis.Variation
