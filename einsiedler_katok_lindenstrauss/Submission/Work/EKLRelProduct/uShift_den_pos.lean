import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.leafwise_null_transfer_gen
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.uAvg_eq

/-!
# `Work.EKLRelProduct.uShift_den_pos`

The denominator `uShift hf νU n (h • x) (V R ∩ U)` of the (8.12c) ratio of `uAvg_eq` is
positive and finite, for `μ|_(Z n)`-a.e. `x` and `(νH x)|_(shape (mH n) H x)`-a.e. `h`.

The point is that on the flower domain the `uShift`-mass of the `U`-ball is a *shape* mass of the
`U`-leafwise measure (`Work.EKLRelProduct.shapeU_eq_shift`: the `U`-shape at a point of the flower
is the `shiftMap`-preimage of `V R ∩ U`), and shape masses are positive and finite a.e.
(`Work.EKLC6Core.shape_mass_pos`).

Two measure-theoretic points are handled explicitly:

* the shape `shape (mH n) H x` is not assumed measurable -- but it *is* null-measurable for the
  leafwise measure `νH x` (`nullMeasurableSet_shape_of_carried`), because the leafwise measure is
  carried by `H` and the shape is `O ∩ H` with `O` open.  This lets us replace the restricted
  measure `(νH x)|_shape` by `νH x (· ∩ shape)` (`Measure.restrict_apply₀'`), which is the form in
  which the a.e. statement can be reduced to a null *set* statement;

* the conull set `XU` of the `U`-leafwise system is transferred along the `H`-leaves by the
  plaque-algebra-local null transfer `Work.EKLProd.leafwise_null_transfer_gen` (applied with
  `U := H`, `N := XUᶜ`), so that `h • x ∈ XU` for all `h` in the shape outside a `νH x`-null set.
-/

open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract Work.EKLProd

/-- The `H`-shape of a plaque algebra is null-measurable for the `H`-leafwise measure.

Indeed, the leafwise measure `ν x` is carried by `H` (`IsLeafwise.carried`), which exhibits a
measurable conull set contained in `H`; and the shape is `O ∩ H` with `O` open, so it agrees
with the measurable set `(measurable subset of H) ∩ O` up to a `ν x`-null set. -/
theorem nullMeasurableSet_shape_of_carried {μ : MeasureTheory.Measure X3}
    {H : Subgroup SL3} {ν : X3 → MeasureTheory.Measure SL3} {XH : Set X3}
    (hν : IsLeafwise μ H ν XH) {A : MeasurableSpace X3} {Z : Set X3}
    (hplaq : IsPlaqueAlgebra H Z A) {x : X3} (hx : x ∈ XH) (hxZ : x ∈ Z) :
    NullMeasurableSet (shape A H x) (ν x) := by
  obtain ⟨N, hNU, hNmeas, hN0⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (hν.carried x hx)
  obtain ⟨-, -, ⟨Op, hOopen, hOshape⟩, -⟩ := hplaq.2.2.2 x hxZ
  have hae : (((Nᶜ : Set SL3) ∩ (Op : Set SL3)) : Set SL3) =ᵐ[ν x] shape A H x := by
    rw [MeasureTheory.ae_eq_set, hOshape]
    constructor
    · refine MeasureTheory.measure_mono_null ?_ hN0
      rintro g ⟨⟨hgN, hgO⟩, hgOH⟩
      exact absurd (hNU fun hgH => hgOH ⟨hgO, hgH⟩) hgN
    · refine MeasureTheory.measure_mono_null ?_ hN0
      rintro g ⟨⟨hgOp, hgH⟩, hgNO⟩
      by_contra hgN
      exact hgNO ⟨hgN, hgOp⟩
  exact ((hNmeas.compl.inter hOopen.measurableSet).nullMeasurableSet).congr hae

theorem uShift_den_pos {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3}
    (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XU : Set Work.EKLContract.X3}
    (hνU : Work.EKLContract.IsLeafwise μ U νU XU) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
        0 < (Work.EKLRelProduct.uShift hf νU n (h • x))
              (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)) ∧
        (Work.EKLRelProduct.uShift hf νU n (h • x))
              (Work.EKLContract.V hf.R ∩ (U : Set Work.EKLContract.SL3)) < ⊤ := by
  classical
  have hZmeas : MeasurableSet (hf.Z n) :=
    MeasurableSpace.le_def.mp (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  have hXHae : ∀ᵐ x ∂(μ.restrict (hf.Z n)), x ∈ XH := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (hνH.conull ▸ MeasureTheory.Measure.restrict_apply_le (hf.Z n) XHᶜ) bot_le
  have hmass : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      0 < νH x (shape (hf.mH n) H x) ∧ νH x (shape (hf.mH n) H x) < ⊤ := by
    filter_upwards [hXHae, MeasureTheory.ae_restrict_mem hZmeas] with x hxXH hxZ
    exact Work.EKLC6Core.shape_mass_pos hνH (hf.plaqH n) hxXH hxZ
  have hN0 : (μ.restrict (hf.Z n)) XUᶜ = 0 :=
    le_antisymm (hνU.conull ▸ MeasureTheory.Measure.restrict_apply_le (hf.Z n) XUᶜ) bot_le
  have htrans : ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      νH x {u : SL3 | u ∈ shape (hf.mH n) H x ∧ u • x ∈ XUᶜ} = 0 :=
    Work.EKLProd.leafwise_null_transfer_gen (N := XUᶜ) hνH (hf.plaqH n) hmass hN0
  filter_upwards [htrans, hXHae, MeasureTheory.ae_restrict_mem hZmeas] with x hxTrans hxXH hxZ
  have hnm : NullMeasurableSet (shape (hf.mH n) H x) (νH x) :=
    nullMeasurableSet_shape_of_carried hνH (hf.plaqH n) hxXH hxZ
  have key : ∀ h : SL3, h ∈ shape (hf.mH n) H x → h • x ∈ XU →
      0 < (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3)) ∧
      (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3)) < ⊤ := by
    intro h hS hxU
    have hyZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hxZ).1 hS.2
    have hshape := shapeU_eq_shift hTH hUH hnorm hcop hdisj hf n hyZ
    have hval : (uShift hf νU n (h • x)) (V hf.R ∩ (U : Set SL3))
        = νU (h • x) (shape (hf.mU n) U (h • x)) := by
      rw [uShift_eq_map hf νU n (h • x),
        MeasurableEmbedding.map_apply (measurableEmbedding_shiftMap _ _), ← hshape]
    rw [hval]
    exact Work.EKLC6Core.shape_mass_pos hνU (hf.plaqU n) hxU hyZ
  rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply₀' hnm]
  refine le_antisymm (le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hxTrans)) bot_le
  rintro h ⟨hnotP, hS⟩
  exact ⟨hS, fun hxU => hnotP (key h hS hxU)⟩

end Work.EKLRelProduct
