import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.sectorSelection
import Submission.Work.BoseBoxFock.slotSum_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Real-valued companions of the Fubini splitting

`integral_pairCoord_split` / `integrable_pairCoord_comp` (`slotSum_sectorPointwise.lean`) are
stated for `ℂ`-valued functions.  The mass half of `sliceFubini` is an integral of the *real*
function `x ↦ ‖Θ x‖²`, so the two companions below are needed; their proofs are the literal
transcriptions of the originals with `ℂ` replaced by `ℝ`. -/

/-- **The Fubini splitting of the configuration-space integral along a slot set `S`**,
`ℝ`-valued companion of `integral_pairCoord_split`. -/
theorem sliceFubini_integral_pairCoord_split_real {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    ∫ x, F x = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y) := by
  classical
  have hinst : (Finset.Subtype.fintype S : Fintype {i // i ∈ S}) =
      Subtype.fintype (fun i : Fin n => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      (volume : Measure (Fin n → Ω))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  have hF' : MeasureTheory.Integrable (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) =>
      F (pairCoord S q.1 q.2)) := by
    have h := (hmp.symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)).mpr hF
    refine h.congr ?_
    filter_upwards with q
    rw [Function.comp_apply, pairCoord_subtypeProd_symm]
  calc ∫ x, F x
      = ∫ q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω),
          F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω)
            (fun i => i ∈ S)).symm q) :=
        (hmp.symm.integral_comp' F).symm
    _ = ∫ q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω), F (pairCoord S q.1 q.2) := by
        apply integral_congr_ae
        filter_upwards with q
        rw [pairCoord_subtypeProd_symm]
    _ = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y) :=
        integral_prod_symm _ hF'

/-- The integrability companion of `sliceFubini_integral_pairCoord_split_real` (`ℝ`-valued companion of
`integrable_pairCoord_comp`). -/
theorem sliceFubini_integrable_pairCoord_comp_real {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℝ)
    (hF : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) =>
      F (pairCoord S q.1 q.2)) := by
  classical
  have hinst : (Finset.Subtype.fintype S : Fintype {i // i ∈ S}) =
      Subtype.fintype (fun i : Fin n => i ∈ S) := Subsingleton.elim _ _
  have hmp : MeasurePreserving
      ⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S))
      (volume : Measure (Fin n → Ω))
      (volume : Measure (({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω))) := by
    rw [hinst]
    exact volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)
  have h := (hmp.symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)).mpr hF
  refine h.congr ?_
  filter_upwards with q
  rw [Function.comp_apply, pairCoord_subtypeProd_symm]

/-- **The Fubini (slice) package for the BF3c selection.**  With `Θ := slotExact e S Φ` (the
`S`-sector of a compactly supported continuous state, a bounded measurable compactly supported
function of `(Fin n → Ω)`) and `slice_y := sectorSlice e S Φ y` (the slice `u ↦ Θ (pairCoord S u y)`
of that sector), the sector's mass and quadratic form split over the complement configurations
`y`, and the two slice integrands are integrable functions of `y`.

Proof route: `slotExact_measurable_bounded_compactSupport` + `boxSlotSum_measurable_bounded` +
`integrable_mul_of_hasCompactSupport_of_bounded` give the integrability of the two full-space
integrands; `integrable_pairCoord_comp` + `Integrable.prod_left_ae` + `integral_re` give the two
integrability conjuncts and the conversions between `(∫ u, f y u).re` and `∫ u, (f y u).re`
(a.e. in `y`); `integral_pairCoord_split` + `integral_prod_symm` + `integral_re` give the two
identities, with `star_mul_re_eq_normSq` and `boxSlotSum_pairCoord` for the pointwise rewrites.
The form identity is also a corollary of the imported `slotSum_sectorPointwise` (proved). -/
theorem sliceFubini {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
            * Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re)
  ∧ MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2)
  ∧ (∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
            * Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re)
      = (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
          star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φ) x).re
  ∧ (∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2)
      = Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φ) := by
  classical
  obtain ⟨hΘm, hΘb, hΘc⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  obtain ⟨hWm, hWb⟩ :=
    boxSlotSum_measurable_bounded e he hec T (slotExact e S Φ) hΘm hΘb
  have hFint : MeasureTheory.Integrable (fun x : Fin n → Ω =>
      star (slotExact e S Φ x) * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x) :=
    integrable_mul_of_hasCompactSupport_of_bounded
      (hΘc.comp_left (g := star) (by simp))
      (measurable_star_comp hΘm).aestronglyMeasurable
      (hΘb.imp (fun C hC x => by rw [norm_star]; exact hC x))
      hWm.aestronglyMeasurable hWb
  have hGint : MeasureTheory.Integrable (fun x : Fin n → Ω => ‖slotExact e S Φ x‖ ^ 2) :=
    integrable_normSq_of_bounded_compactSupport hΘm hΘb hΘc
  -- the two full-space integrands, pushed to the product space along `pairCoord`
  have hFprod := integrable_pairCoord_comp S
    (fun x : Fin n → Ω => star (slotExact e S Φ x)
      * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x) hFint
  have hGprodR := sliceFubini_integrable_pairCoord_comp_real S
    (fun x : Fin n → Ω => ‖slotExact e S Φ x‖ ^ 2) hGint
  -- the pointwise identification of the assembled form integrand with the slice form integrand
  have hpt : ∀ (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
      star (slotExact e S Φ (pairCoord S u y))
        * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) (pairCoord S u y)
      = star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u := by
    intro u y
    rw [boxSlotSum_pairCoord e T S Φ he hec horth hint hΦ hΦc u y]
    rfl
  have hInnerAe : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
      MeasureTheory.Integrable (fun u : {i // i ∈ S} → Ω =>
        star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u) := by
    filter_upwards [hFprod.prod_left_ae] with y hy
    refine hy.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact hpt u y
  have hGY : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u : {i // i ∈ S} → Ω,
        star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u) := by
    refine (hFprod.integral_prod_right).congr ?_
    filter_upwards with y
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact hpt u y
  -- `(∫ u, f y u).re` and `∫ u, (f y u).re` agree for a.e. `y`
  have hAeRe : (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u).re)
      =ᵐ[volume] (fun y : {i // i ∉ S} → Ω =>
        (∫ u : {i // i ∈ S} → Ω,
          star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u).re) := by
    filter_upwards [hInnerAe] with y hy
    exact integral_re hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the form integrand, with the real part inside the inner integral
    exact hGY.re.congr hAeRe.symm
  · -- the mass integrand
    exact hGprodR.integral_prod_right
  · -- the form identity
    have hpoint := slotSum_sectorPointwise e he hec horth hint T S Φ hΦ hΦc
    simp only [starRingEnd_apply] at hpoint
    exact (integral_congr_ae hAeRe).trans hpoint.symm
  · -- the mass identity
    rw [massR_eq_integral_normSq]
    exact (sliceFubini_integral_pairCoord_split_real S
      (fun x : Fin n → Ω => ‖slotExact e S Φ x‖ ^ 2) hGint).symm

end Work.BoseBoxFock
