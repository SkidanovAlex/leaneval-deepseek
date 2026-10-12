import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseKinLoc.Compare.compare_box_energy
import Submission.Work.BoseKinLoc.Kinetic.dSpace_fibre_eq
import Submission.Work.BoseKinLoc.Kinetic.fsT_bound_abs
import Submission.Work.BoseKinLoc.Kinetic.integral_fibre_sq
import Submission.Work.BoseKinLoc.Kinetic.momForm_le_box
import Submission.Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Compare.CompareV2Aux` — the measure-theoretic plumbing of
`compare_box_energy_v2`

This module collects the pieces of the comparison theorem that are *independent of the
kinetic hypothesis*:

* `setIntegral_eq_integral_of_eq_zero_off`: for a function vanishing off a measurable set `s`,
  the restricted integral equals the full integral.  (Unconditional: it only uses that the
  Bochner integral of the indicator is the restricted integral, `integral_indicator`.)
* `measurableSet_coverBoxU`, `volume_coverBoxU_toReal`: the support-adapted cover and its
  (`ℝ`-valued) volume `(L+ℓ)³/ℓ³`.
* the slot-`i` lift fibre `liftFibre`, its smoothness / compact support / vanishing, and the
  vanishing of `fsT` on the lift when the translation parameter is off the cover.
* `integrable_fibre_H1`: the one-body `H¹` data of the lift fibres is integrable in the
  remaining coordinates (the corpus's `integral_fibre_sq` + `dSpace_fibre_eq`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Restricted integrals of functions vanishing off the set.**  If `f` vanishes off a
measurable set `s`, then `∫ x in s, f x = ∫ x, f x`.  No integrability is needed: the
Bochner integral of the indicator is the restricted integral, and `s.indicator f = f`
pointwise. -/
theorem setIntegral_eq_integral_of_eq_zero_off {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ} (hf : ∀ x ∉ s, f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  rw [← integral_indicator hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hf x hx]

namespace Compare

/-- The support-adapted cover `coverBoxU ℓ L` is measurable (it is the cube of side
`(L+ℓ)/ℓ` centred at the origin, in coordinates). -/
theorem measurableSet_coverBoxU {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    MeasurableSet (coverBoxU ℓ L) := by
  have hset : coverBoxU ℓ L = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin 3 =>
      Set.Icc (-((L + ℓ) / (2 * ℓ))) ((L + ℓ) / (2 * ℓ)))) := by
    ext u
    rw [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hu k
      rw [Set.mem_Icc]
      exact abs_le.mp ((mem_coverBoxU_iff hℓ hL u).mp hu k)
    · intro hu
      refine (mem_coverBoxU_iff hℓ hL u).mpr fun k => ?_
      have hk := hu k
      rw [Set.mem_Icc] at hk
      exact abs_le.mpr hk
  rw [hset]
  have hmeas : MeasurableSet (Set.univ.pi (fun _ : Fin 3 =>
      Set.Icc (-((L + ℓ) / (2 * ℓ))) ((L + ℓ) / (2 * ℓ)))) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  exact hmeas.preimage (PiLp.volume_preserving_ofLp (Fin 3)).measurable

/-- The `ℝ`-valued volume of the support-adapted cover. -/
theorem volume_coverBoxU_toReal {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    (MeasureTheory.volume (coverBoxU ℓ L)).toReal = (L + ℓ) ^ 3 / ℓ ^ 3 := by
  rw [volume_coverBoxU hℓ hL, ENNReal.toReal_ofReal]
  positivity

end Compare

open Compare

/-! ## The slot-`i` lift fibre of an `(n+1)`-body state -/

/-- The slot-`i` lift fibre: `z ↦ Φ (kcInsN n i (z, r))`.  This is `fibre (n+1) i Φ`
evaluated at `kcInsN n i (z, r)` and does not depend on the inserted coordinate. -/
abbrev liftFib (n : ℕ) (i : Fin (n + 1)) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : Submission.BoseGases.X n) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun z => Φ (Submission.BoseGases.kcInsN n i (z, r))

theorem Work.BoseKinLoc.liftFib_contDiff {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (r : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ENat) (Work.BoseKinLoc.liftFib n i Φ r) := by
  have hins : ContDiff ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.kcInsN n i (z, r)) := by
    have h1 : (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.kcInsN n i (z, r))
        = Function.update (Submission.BoseGases.kcInsN n i (0, r)) i := by
      funext z
      exact Submission.BoseGases.kcInsN_update_zero i z r
    rw [h1]
    exact contDiff_update (⊤ : ENat) (Submission.BoseGases.kcInsN n i (0, r)) i
  exact hΦ.comp hins

/-- The `tsupport` of the slot-`i` lift fibre is contained in the centred box `acube L`
when `Φ` is supported in `abox (n+1) L`. -/
theorem liftFib_tsupport_subset {n : ℕ} {L : ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) :
    tsupport (Work.BoseKinLoc.liftFib n i Φ r) ⊆ Submission.BoseGases.acube L := by
  refine closure_minimal (fun z hz => ?_) (Submission.BoseGases.acube_isClosed L)
  by_contra hzc
  have hins : Submission.BoseGases.kcInsN n i (z, r) ∈ tsupport Φ :=
    subset_tsupport Φ (by simpa [liftFib, Function.mem_support] using hz)
  exact hzc (by
    have h := hsupp hins
    simpa [Submission.BoseGases.kc_insN_apply_same n i z r] using h i)

/-- If `Φ` is supported in `abox (n+1) L`, then the slot-`i` lift fibre vanishes off
`acube L`. -/
theorem liftFib_eq_zero_of_not_mem_acube {n : ℕ} {L : ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∉ Submission.BoseGases.acube L) : liftFib n i Φ r z = 0 :=
  image_eq_zero_of_notMem_tsupport (f := liftFib n i Φ r)
    (fun h => hz (liftFib_tsupport_subset hsupp i r h))

theorem Work.BoseKinLoc.liftFib_hasCompactSupport {n : ℕ} {L : ℝ} (hL : 0 < L)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) : HasCompactSupport (Work.BoseKinLoc.liftFib n i Φ r) :=
  IsCompact.of_isClosed_subset (Submission.BoseGases.acube_compact hL)
    (isClosed_tsupport _) (liftFib_tsupport_subset hsupp i r)

/-- **The lift fibre is constant `0` on `Λ(u)` when `u` is off the cover**, hence `fsT`
vanishes there. -/
theorem fsT_liftFib_eq_zero_of_not_mem_coverBoxU {n : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1))
    (r : Submission.BoseGases.X n) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∉ coverBoxU ℓ L) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (Work.BoseKinLoc.liftFib n i Φ r) = 0 :=
  Word.fsT_eq_zero_of_lamBox_const (c := 0) hℓ u fun z hz =>
    liftFib_eq_zero_of_not_mem_acube hsupp i r
      (not_mem_acube_of_not_mem_coverBoxU hu hz)

/-- **The `H¹` data of the lift fibres is integrable in the remaining coordinates.**
This is the corpus's `integral_fibre_sq` together with `dSpace_fibre_eq`. -/
theorem Work.BoseKinLoc.integrable_liftFib_H1 {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) (i : Fin (n + 1)) :
    MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
      (∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
        + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)) := by
  refine (Kinetic.integral_fibre_sq (n := n) hΦ hcs i).1.add ?_
  simpa only [liftFib] using (Kinetic.dSpace_fibre_eq (n := n) hΦ hcs i).1



namespace Compare

/-! ## The uniform bound on the localised kinetic word -/

/-- **The `N`-body kinetic word is bounded uniformly in the translation parameter.**  For a
smooth state supported in `abox (n+1) L` the word `kinForm (n+1) ℓ d s εT b u Φ` is bounded by a
constant depending only on `(ℓ,d,s,εT,b)` and on the `H¹` data of the slot fibres of `Φ`
(which is finite and integrable in the remaining coordinates by `integral_fibre_sq` +
`dSpace_fibre_eq`).  The bound is what makes the `u`-integral of the word honest. -/
theorem exists_bound_kinForm {n : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hd : 0 < d) {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox (n + 1) L) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseKinLoc.kinForm (n + 1) ℓ d s εT b u Φ‖ ≤ W := by
  have hcsΦ : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Submission.BoseGases.abox_compact (n + 1) hL)
      (isClosed_tsupport Φ) hsupp
  obtain ⟨C, hC0, hCbd⟩ := Work.BoseKinLoc.Kinetic.fsT_bound_abs (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
    hℓ hd (fun u ψ hψ hcsψ => Work.BoseKinLoc.Kinetic.momForm_le_box hℓ hd u hψ hcsψ)
  have hMnn : ∀ i : Fin (n + 1), ∀ r : Submission.BoseGases.X n,
      0 ≤ (∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
        + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r) := by
    intro i r
    exact add_nonneg (integral_nonneg fun z => sq_nonneg _)
      (Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _)
  have hMi : ∀ i : Fin (n + 1), MeasureTheory.Integrable (fun r : Submission.BoseGases.X n =>
      (∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
        + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)) := fun i =>
    Work.BoseKinLoc.integrable_liftFib_H1 hΦ hcsΦ i
  refine ⟨∑ i : Fin (n + 1), C * ∫ r : Submission.BoseGases.X n,
      ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
        + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)), ?_, fun u => ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg hC0 (integral_nonneg (hMnn i))
  · have hpeel : ∀ i : Fin (n + 1),
        ‖Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ‖
          ≤ C * ∫ r : Submission.BoseGases.X n,
              ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
                + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)) := by
      intro i
      rw [Work.BoseKinLoc.Kinetic.slotForm_eq_fibre_integral hℓ (Work.BoseKinLoc.fsT ℓ d s εT b u) u i Φ]
      have hmaj : ∀ r : Submission.BoseGases.X n,
          ENNReal.ofReal ‖Work.BoseKinLoc.fsT ℓ d s εT b u (Work.BoseKinLoc.liftFib n i Φ r)‖
            ≤ ENNReal.ofReal (C * ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
                + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r))) := fun r =>
        ENNReal.ofReal_le_ofReal (by
          have h := hCbd u (Work.BoseKinLoc.liftFib n i Φ r) (Work.BoseKinLoc.liftFib_contDiff hΦ i r)
            (Work.BoseKinLoc.liftFib_hasCompactSupport hL hsupp i r)
          simpa only [Real.norm_eq_abs, Work.BSKinetic.dSpace] using h)
      have hlin : (∫⁻ r : Submission.BoseGases.X n,
            ENNReal.ofReal (C * ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
              + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r))))
          = ENNReal.ofReal (C * ∫ r : Submission.BoseGases.X n,
              ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
                + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r))) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMi i).const_mul C)
          (Filter.Eventually.of_forall fun r => mul_nonneg hC0 (hMnn i r)),
          MeasureTheory.integral_const_mul]
      have hlin_ne : (∫⁻ r : Submission.BoseGases.X n,
            ENNReal.ofReal (C * ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
              + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)))) ≠ ⊤ := by
        rw [hlin]; exact ENNReal.ofReal_ne_top
      calc ‖∫ r : Submission.BoseGases.X n, Work.BoseKinLoc.fsT ℓ d s εT b u (Work.BoseKinLoc.liftFib n i Φ r)‖
          ≤ ENNReal.toReal (∫⁻ r : Submission.BoseGases.X n,
              ENNReal.ofReal ‖Work.BoseKinLoc.fsT ℓ d s εT b u (Work.BoseKinLoc.liftFib n i Φ r)‖) :=
            MeasureTheory.norm_integral_le_lintegral_norm _
        _ ≤ ENNReal.toReal (∫⁻ r : Submission.BoseGases.X n,
              ENNReal.ofReal (C * ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
                + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)))) :=
            ENNReal.toReal_mono hlin_ne (MeasureTheory.lintegral_mono hmaj)
        _ = C * ∫ r : Submission.BoseGases.X n,
              ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
                + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)) := by
            rw [hlin,
              ENNReal.toReal_ofReal (mul_nonneg hC0 (integral_nonneg (hMnn i)))]
    calc ‖Work.BoseKinLoc.kinForm (n + 1) ℓ d s εT b u Φ‖
        = ‖∑ i : Fin (n + 1), Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ‖ := by
          rw [Work.BoseKinLoc.kinForm_eq]
      _ ≤ ∑ i : Fin (n + 1), ‖Work.BoseKinLoc.slotForm (n + 1) (Work.BoseKinLoc.fsT ℓ d s εT b u) ℓ u i Φ‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n + 1), C * ∫ r : Submission.BoseGases.X n,
            ((∫ z : EuclideanSpace ℝ (Fin 3), (liftFib n i Φ r z) ^ 2)
              + Work.BSKinetic.dSpace (Work.BoseKinLoc.liftFib n i Φ r)) :=
          Finset.sum_le_sum fun i _ => hpeel i

end Compare

end Work.BoseKinLoc
