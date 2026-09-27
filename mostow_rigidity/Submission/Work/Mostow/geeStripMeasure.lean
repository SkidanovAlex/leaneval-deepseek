import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.stab_eq_blk

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ### The weight comparison `volume ≤ tubeMeasure 1 m`

The density `cosh ‖w‖ ^ 1 * sinhc ‖w‖ ^ (m - 1)` of `tubeMeasure 1 m` is pointwise `≥ 1`, so
`tubeMeasure 1 m` dominates Lebesgue measure on the normal-coordinate chart `E m`.  (This is a
self-contained copy of `Work.Mostow.volume_le_tubeMeasure`, kept here so that this file does not
depend on `geodRegionTube`.) -/

/-- `1 ≤ sinhc s` for `s ≥ 0` (`sinhc s = sinh s / s`). -/
theorem geeStripOneLeSinhc {s : ℝ} (hs : 0 ≤ s) : 1 ≤ sinhc s := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    simp [sinhc]
  · rw [sinhc, ite_eq_right (ne_of_gt h), one_le_div h]
    exact (Real.self_le_sinh_iff).mpr hs

/-- The density of `tubeMeasure 1 m` is at least `1`. -/
theorem geeStripOneLeTubeDensity (m : ℕ) (w : E m) :
    1 ≤ Real.cosh ‖w‖ ^ 1 * sinhc ‖w‖ ^ (m - 1) := by
  have h1 : (1 : ℝ) ≤ Real.cosh ‖w‖ ^ 1 := by simpa using Real.one_le_cosh ‖w‖
  have h3 : (1 : ℝ) ≤ sinhc ‖w‖ ^ (m - 1) :=
    one_le_pow₀ (geeStripOneLeSinhc (norm_nonneg w))
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Real.cosh ‖w‖ ^ 1 * sinhc ‖w‖ ^ (m - 1) :=
        mul_le_mul h1 h3 zero_le_one (by positivity)

/-- `tubeMeasure 1 m` dominates Lebesgue measure on the normal-coordinate chart `E m`. -/
theorem geeStripVolumeLeTubeMeasure (m : ℕ) :
    (MeasureTheory.volume : MeasureTheory.Measure (E m)) ≤ tubeMeasure 1 m := by
  rw [tubeMeasure]
  have hmono :
      (MeasureTheory.volume : MeasureTheory.Measure (E m)).withDensity
          (fun _ : E m => (1 : ENNReal)) ≤
        (MeasureTheory.volume : MeasureTheory.Measure (E m)).withDensity
          (fun w => ENNReal.ofReal (Real.cosh ‖w‖ ^ 1 * sinhc ‖w‖ ^ (m - 1))) :=
    MeasureTheory.withDensity_mono (Filter.Eventually.of_forall fun w => by
      simpa using ENNReal.ofReal_le_ofReal (geeStripOneLeTubeDensity m w))
  simpa [MeasureTheory.withDensity_one] using hmono

/-- **The `c`-strip of the normal part of a pointwise geodesic-stabilising element lies in the
Margulis region.**  If `a ∈ Λ` lies in the setwise stabiliser `SetStabStd 1 m` with trivial
restriction `resStd 1 m a = 1`, is non-trivial, and its normal part is `c`-close to the identity
(`rotN (nrmStd 1 m a) ≤ c`), then for every normal vector `W` with `‖nrmStd 1 m a W - W‖ ≤ c`
the chart point `fermiW 1 m 0 W` (whose normal coordinate is `W`) lies in the Margulis region
`margRegion m Λ s`, provided `10 * c < s`. -/
theorem geeStripMeasure_subset (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (s c : ℝ) (hc : 0 ≤ c) (h10 : 10 * c < s)
    (a : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (ha : a ∈ Λ)
    (hstab : a ∈ Submission.Mostow.SetStabStd 1 m) (hres : Submission.Mostow.resStd 1 m a = 1)
    (hne : a ≠ 1) (hrot : Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m a) ≤ c) :
    {W : Submission.Mostow.E m | ‖(Submission.Mostow.nrmStd 1 m a) W - W‖ ≤ c}
      ⊆ Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ s := by
  intro W hW
  -- `a` is the pure normal block determined by its normal part
  have ha_eq : a = blk 1 m (1 : PO 1 1) (nrmStd 1 m a) := by
    conv_lhs => rw [rhd_stab_form 1 m hA1 hI1 hA hI hstab]
    rw [hres]
  refine ⟨fermiW 1 m (0 : E 1) W, ⟨a, ha, hstab, hres, hne, ?_⟩, nib_nrmC_fermiW m 0 W⟩
  rw [ha_eq]
  exact (nearId_blk m hA1 hI1 hA hI (nrmStd 1 m a) (0 : E 1) W).1 c s hrot hW h10

theorem geeStripMeasure (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) (s c : ℝ) (hc : 0 ≤ c) (h10 : 10 * c < s)
    (a : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (ha : a ∈ Λ)
    (hstab : a ∈ Submission.Mostow.SetStabStd 1 m) (hres : Submission.Mostow.resStd 1 m a = 1)
    (hne : a ≠ 1) (hrot : Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m a) ≤ c) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m)) {W : Submission.Mostow.E m | ‖(Submission.Mostow.nrmStd 1 m a) W - W‖ ≤ c}
      ≤ Submission.Mostow.tubeMeasure 1 m (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ s) := by
  calc (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
        {W : Submission.Mostow.E m | ‖(Submission.Mostow.nrmStd 1 m a) W - W‖ ≤ c}
      ≤ (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
        (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ s) :=
        MeasureTheory.measure_mono
          (geeStripMeasure_subset m hA1 hI1 hA hI Λ s c hc h10 a ha hstab hres hne hrot)
    _ ≤ Submission.Mostow.tubeMeasure 1 m
        (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ s) :=
        (MeasureTheory.Measure.le_iff'.mp (geeStripVolumeLeTubeMeasure m)) _

end Work.Mostow
