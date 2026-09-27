import Mathlib
import Submission.Work.Mostow.HaarSetup
import Submission.Work.Mostow.Ksub_compact

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

-- `Theta n hA s p = s p.1 * ↑p.2` is continuous, injective and surjective onto `PO n 1`
-- (`continuous_Theta`, `Theta_injective`, `Theta_surjective`, `Theta_fst`, `kPart` in
-- `Submission.Work.Mostow.HaarSetup`).  HINT for finite-on-compacts: `Θ ⁻¹' K ⊆ (· • 0) '' K ×ˢ univ`
-- and `(· • 0) '' K` is compact; `τ univ < ⊤` needs `Ksub` compact
-- (`Submission.Work.Mostow.Ksub_compact`).  For open-positivity use `isOpen_prod_iff` inside the
-- open set `Θ ⁻¹' U`, injectivity, `volHPosOpen` and open-positivity of the Haar measure `τ`.

/-- `Work.Mostow.Ksub n hA` is compact (`Ksub_compact`), so its subtype is a compact group and
hence every Haar measure on it is a *finite* measure; in particular it is s-finite, which lets us
use `Measure.prod_prod`/`Measure.prod_prod_le` for the product `volH n × τ`. -/
theorem sFinite_haar_Ksub (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (τ : MeasureTheory.Measure ↥(Work.Mostow.Ksub n hA))
    [MeasureTheory.Measure.IsHaarMeasure τ] : SFinite τ := by
  haveI : CompactSpace ↥(Ksub n hA) :=
    (isCompact_iff_compactSpace (s := (Ksub n hA : Set (PO n 1)))).mp (Ksub_compact n hA)
  haveI : IsFiniteMeasure τ := ⟨isCompact_univ.measure_lt_top⟩
  infer_instance

/-- The section `s : E n → PO n 1` of the orbit map sends `u` to an element with `s u • 0 = u`, so
for `K` compact in `PO n 1` every `p` with `Theta n hA s p ∈ K` lies in
`(· • 0) '' K ×ˢ univ`.  This is the geometric input for finite-on-compacts. -/
theorem Theta_preimage_subset (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (s : E n → PO n 1) (hs : ∀ u : E n, s u • (0 : E n) = u) {K : Set (PO n 1)} :
    Theta n hA s ⁻¹' K ⊆ ((fun g : PO n 1 => g • (0 : E n)) '' K) ×ˢ (Set.univ : Set ↥(Ksub n hA)) := by
  rintro ⟨u, k⟩ hp
  exact ⟨⟨Theta n hA s (u, k), hp, Theta_fst n hA s hs u k⟩, trivial⟩

/-- The pushforward of `volH n × τ` under `Theta` is finite on compact sets: `K` compact pulls back
into `(· • 0) '' K × univ`, whose `(volH n).prod τ`-measure is at most
`volH n ((· • 0) '' K) * τ univ`, a product of two finite numbers (the first because `(· • 0) '' K`
is compact, the second because `τ` is a Haar measure on the compact group `Ksub`). -/
theorem isFiniteMeasureOnCompacts_theta (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (s : E n → PO n 1) (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s)
    (hvolK : MeasureTheory.IsFiniteMeasureOnCompacts (volH n))
    (τ : MeasureTheory.Measure ↥(Ksub n hA)) [MeasureTheory.Measure.IsHaarMeasure τ] :
    MeasureTheory.IsFiniteMeasureOnCompacts (((volH n).prod τ).map (Theta n hA s)) := by
  haveI : CompactSpace ↥(Ksub n hA) :=
    (isCompact_iff_compactSpace (s := (Ksub n hA : Set (PO n 1)))).mp (Ksub_compact n hA)
  haveI : IsFiniteMeasure τ := ⟨isCompact_univ.measure_lt_top⟩
  haveI : IsFiniteMeasureOnCompacts (volH n) := hvolK
  refine ⟨fun K hK => ?_⟩
  have hc : Continuous (Theta n hA s) := continuous_Theta n hA s hsc
  rw [Measure.map_apply hc.measurable hK.isClosed.measurableSet]
  calc ((volH n).prod τ) (Theta n hA s ⁻¹' K)
      ≤ ((volH n).prod τ) (((fun g : PO n 1 => g • (0 : E n)) '' K) ×ˢ Set.univ) :=
        measure_mono (Theta_preimage_subset n hA s hs)
    _ ≤ volH n ((fun g : PO n 1 => g • (0 : E n)) '' K) * τ Set.univ := Measure.prod_prod_le _ _
    _ < ⊤ := ENNReal.mul_lt_top (hK.image (continuous_smul_zero hA)).measure_lt_top
        isCompact_univ.measure_lt_top

/-- The pushforward of `volH n × τ` under `Theta` is positive on nonempty open sets: `Theta` is
continuous and surjective, so for `U` open and `y = Theta p ∈ U` the open set `Theta ⁻¹' U`
contains a *rectangular* open neighbourhood `U₁ × U₂` of `p` (`isOpen_prod_iff`).  Then
`(volH n).prod τ (U₁ × U₂) = volH n U₁ * τ U₂ > 0` by `volHPosOpen` and the open-positivity of the
Haar measure `τ`. -/
theorem isOpenPosMeasure_theta (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (s : E n → PO n 1) (hs : ∀ u : E n, s u • (0 : E n) = u) (hsc : Continuous s)
    (τ : MeasureTheory.Measure ↥(Ksub n hA)) [MeasureTheory.Measure.IsHaarMeasure τ] :
    MeasureTheory.Measure.IsOpenPosMeasure (((volH n).prod τ).map (Theta n hA s)) := by
  haveI : SFinite τ := sFinite_haar_Ksub n hA τ
  refine ⟨fun U hU hne => ?_⟩
  have hc : Continuous (Theta n hA s) := continuous_Theta n hA s hsc
  rw [Measure.map_apply hc.measurable hU.measurableSet]
  obtain ⟨p, hp⟩ : ∃ p, Theta n hA s p ∈ U := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨p, rfl⟩ := Theta_surjective n hA s hs y
    exact ⟨p, hy⟩
  have hopen : IsOpen (Theta n hA s ⁻¹' U) := hU.preimage hc
  obtain ⟨U₁, U₂, hU₁o, hU₂o, hp1, hp2, hsub⟩ := isOpen_prod_iff.mp hopen p.1 p.2 hp
  have hpos : 0 < ((volH n).prod τ) (U₁ ×ˢ U₂) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos (volHPosOpen n hU₁o ⟨p.1, hp1⟩).ne'
      (Measure.IsOpenPosMeasure.open_pos U₂ hU₂o ⟨p.2, hp2⟩)
  exact ne_of_gt (lt_of_lt_of_le hpos (measure_mono hsub))

theorem theta_measure_facts (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (s : Submission.Mostow.E n → LeanEval.Geometry.MostowRigidity.PO n 1)
    (hs : ∀ u : Submission.Mostow.E n, s u • (0 : Submission.Mostow.E n) = u)
    (hsc : Continuous s) (hvol : MeasureTheory.SigmaFinite (Submission.Mostow.volH n))
    (hvolK : MeasureTheory.IsFiniteMeasureOnCompacts (Submission.Mostow.volH n))
    (τ : MeasureTheory.Measure ↥(Work.Mostow.Ksub n hA))
    [MeasureTheory.Measure.IsHaarMeasure τ] :
    MeasureTheory.IsFiniteMeasureOnCompacts
      (((Submission.Mostow.volH n).prod τ).map (Work.Mostow.Theta n hA s)) ∧
    MeasureTheory.Measure.IsOpenPosMeasure
      (((Submission.Mostow.volH n).prod τ).map (Work.Mostow.Theta n hA s)) :=
  ⟨isFiniteMeasureOnCompacts_theta n hA s hs hsc hvolK τ,
    isOpenPosMeasure_theta n hA s hs hsc τ⟩

end Work.Mostow
