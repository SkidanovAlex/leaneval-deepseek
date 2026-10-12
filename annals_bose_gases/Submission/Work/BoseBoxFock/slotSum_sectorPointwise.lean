import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.sectorSlotLift
import Submission.Work.BoseBoxFock.slotSubDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotSum_sectorPointwise` — the form half of the BF3c pointwise decoupling

For orthonormal modes `e`, a one-body operator `T` and a compactly supported continuous state
`Φ`, the quadratic form of the `S`-sector `Θ = slotExact e S Φ` against the first-quantised slot
sum `Work.BoseDict.boxSlotSum e T` **factorises over the complement configuration** `y`:

    `⟨Θ, boxSlotSum e T Θ⟩ = ∫_y ⟨slice_y, slotSumSub e T S slice_y⟩`,

where `slice_y(u) = sectorSlice e S Φ y u = Θ(pairCoord S u y)` is the slice of the sector at the
complement configuration `y`, and `slotSumSub e T S` is the `↥S`-slot part of the slot sum
(`slotSubDefs.lean`).

The mathematical content is the pointwise identity, valid for *every* `(u, y)`:

* the slot sum collapses to the occupied slots (`boxSlotSum_sector_eq_sum_mem`);
* on an occupied slot `j ∈ S` the rank-one slot operator `|η_w⟩⟨η_v|` of the *full* configuration
  applied at `pairCoord S u y` is exactly the `↥S`-slot operator `slotOfSub` applied to the slice
  (`boxSlotOf_pairCoord`), because `Function.update` commutes with `pairCoord`.

The first-quantised statement then follows from the measure-preserving splitting of the
configuration space along `S` (Fubini) and the linearity of the Bochner integral.

## Main declarations

* `pairCoord_subtypeProd_symm` — the slot splitting equivalence is the reassembling map
  `pairCoord` (up to argument order);
* `integral_pairCoord_split` — the Fubini change of variables `∫_x = ∫_y ∫_u`;
* `integrable_pairCoord_comp` — the companion integrability statement;
* `update_pairCoord`, `boxSlotOf_pairCoord`, `boxSlotSum_pairCoord` — the pointwise identities;
* `slotSum_sectorPointwise` — the target.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The slot splitting of the configuration space

`MeasurableEquiv.piEquivPiSubtypeProd` splits a configuration into its coordinates in `S` and its
coordinates outside `S`.  Its inverse is the reassembling map `pairCoord`, up to the order of the
two arguments. -/

/-- The inverse of the splitting equivalence is `pairCoord` (with the two arguments swapped). -/
theorem pairCoord_subtypeProd_symm {n : ℕ} (S : Finset (Fin n)) :
    ⇑((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm)
      = fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) => pairCoord S q.1 q.2 := by
  funext q
  obtain ⟨u, y⟩ := q
  funext i
  by_cases h : i ∈ S <;> simp [pairCoord, h]

/-- **The Fubini splitting of the configuration-space integral along a slot set `S`.** -/
theorem integral_pairCoord_split {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℂ)
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
          F ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Ω) (fun i => i ∈ S)).symm q) :=
        (hmp.symm.integral_comp' F).symm
    _ = ∫ q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω), F (pairCoord S q.1 q.2) := by
        apply integral_congr_ae
        filter_upwards with q
        rw [pairCoord_subtypeProd_symm]
    _ = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω, F (pairCoord S u y) :=
        integral_prod_symm _ hF'

/-- The integrability companion of `integral_pairCoord_split`. -/
theorem integrable_pairCoord_comp {n : ℕ} (S : Finset (Fin n)) (F : (Fin n → Ω) → ℂ)
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

/-! ## 2. The pointwise identities -/

/-- **`Function.update` commutes with `pairCoord` on an occupied slot.**

**Name note.**  `Submission/Work/BoseBoxFock/XSpow_sliceF_pointwise.lean` (the `ExcWindow` side of
the same identity) declares a `update_pairCoord` of its own, indexed by `↥S` instead of by
`Fin n` with a membership proof; the two cannot coexist in one import cone, so this one carries the
suffix `_mem`.  Several files record the resulting "do not import `slotSum_sectorPointwise`"
workaround — with the rename the clash is gone and those prohibitions are obsolete. -/
theorem update_pairCoord_mem {n : ℕ} (S : Finset (Fin n)) (u : {i // i ∈ S} → Ω)
    (y : {i // i ∉ S} → Ω) (j : Fin n) (hj : j ∈ S) (z : Ω) :
    Function.update (pairCoord S u y) j z
      = pairCoord S (Function.update u ⟨j, hj⟩ z) y := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, pairCoord_mem S (Function.update u ⟨i, hj⟩ z) y i hj,
      Function.update_self]
  · rw [Function.update_of_ne hij z (pairCoord S u y)]
    by_cases hi : i ∈ S
    · rw [pairCoord_mem S u y i hi,
        pairCoord_mem S (Function.update u ⟨j, hj⟩ z) y i hi]
      exact (Function.update_of_ne
        (a := ⟨i, hi⟩) (a' := ⟨j, hj⟩) (fun h => hij (Subtype.ext_iff.mp h)) z u).symm
    · rw [pairCoord_notMem S u y i hi,
        pairCoord_notMem S (Function.update u ⟨j, hj⟩ z) y i hi]

/-- **A `V`-supported slot operator on the assembled configuration is the `↥S`-slot operator on
the slice.**  For `j ∈ S`, the slot-`j` rank-one operator of the full configuration applied at
`pairCoord S u y` equals `slotOfSub` at the slot `⟨j, hj⟩` applied to the slice at `y`. -/
theorem boxSlotOf_pairCoord {m n : ℕ} (e : Fin m → Ω → ℂ) (w v : Fin m → ℝ)
    (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) (j : Fin n) (hj : j ∈ S)
    (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω) :
    Work.BoseDict.boxSlotOf e w v j (slotExact e S Φ) (pairCoord S u y)
      = slotOfSub e w v ⟨j, hj⟩ (sectorSlice e S Φ y) u := by
  rw [Work.BoseDict.boxSlotOf, slotOfSub, pairCoord_mem S u y j hj]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [show (sectorSlice e S Φ y) (Function.update u ⟨j, hj⟩ z)
      = slotExact e S Φ (pairCoord S (Function.update u ⟨j, hj⟩ z) y) from rfl,
    update_pairCoord_mem]

/-- **The slot sum of a sector, read at the assembled configuration, is the `↥S`-slot sum of the
slice.** -/
theorem boxSlotSum_pairCoord {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω) :
    Work.BoseDict.boxSlotSum e T (slotExact e S Φ) (pairCoord S u y)
      = slotSumSub e T S (sectorSlice e S Φ y) u := by
  rw [boxSlotSum_sector_eq_sum_mem e T S Φ he hec horth hint hΦ hΦc]
  simp only [slotSumSub, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_attach S (fun j => ∑ l : Fin m, ∑ l' : Fin m,
      T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
          (slotExact e S Φ) (pairCoord S u y))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [boxSlotOf_pairCoord]

/-! ## 3. The target -/

theorem slotSum_sectorPointwise {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.slotExact e S Φ x)
        * Work.BoseDict.boxSlotSum e T (Work.BoseBoxFock.slotExact e S Φ) x).re
      = ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
          (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            (starRingEnd ℂ) (Work.BoseBoxFock.sectorSlice e S Φ y u)
              * Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re := by
  classical
  obtain ⟨hΘm, hΘb, hΘc⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  obtain ⟨hWm, hWb⟩ :=
    boxSlotSum_measurable_bounded e he hec T (slotExact e S Φ) hΘm hΘb
  -- integrability of the integrand of the left-hand side
  have hFint : MeasureTheory.Integrable (fun x : Fin n → Ω =>
      (starRingEnd ℂ) (slotExact e S Φ x)
        * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x) := by
    rw [show (fun x : Fin n → Ω => (starRingEnd ℂ) (slotExact e S Φ x)
          * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x)
        = fun x => star (slotExact e S Φ x)
          * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x from
      funext fun x => by rw [starRingEnd_apply]]
    exact integrable_mul_of_hasCompactSupport_of_bounded
      (hΘc.comp_left (g := star) (by simp))
      (measurable_star_comp hΘm).aestronglyMeasurable
      (hΘb.imp (fun C hC x => by rw [norm_star]; exact hC x))
      hWm.aestronglyMeasurable hWb
  -- the pointwise identification of the assembled integrand with the slice integrand
  have hpt : ∀ (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
      (starRingEnd ℂ) (slotExact e S Φ (pairCoord S u y))
          * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) (pairCoord S u y)
        = (starRingEnd ℂ) (sectorSlice e S Φ y u)
          * slotSumSub e T S (sectorSlice e S Φ y) u := by
    intro u y
    rw [boxSlotSum_pairCoord e T S Φ he hec horth hint hΦ hΦc u y]
    rfl
  -- the Fubini splitting of the left-hand side, then the pointwise rewrite
  have hsplit : (∫ x : Fin n → Ω, (starRingEnd ℂ) (slotExact e S Φ x)
        * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) x)
      = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          (starRingEnd ℂ) (slotExact e S Φ (pairCoord S u y))
            * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) (pairCoord S u y) :=
    integral_pairCoord_split S _ hFint
  have hslice : (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
        (starRingEnd ℂ) (slotExact e S Φ (pairCoord S u y))
          * Work.BoseDict.boxSlotSum e T (slotExact e S Φ) (pairCoord S u y))
      = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          (starRingEnd ℂ) (sectorSlice e S Φ y u)
            * slotSumSub e T S (sectorSlice e S Φ y) u := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => hpt u y))
  -- integrability of the outer integral
  have hGint : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u : {i // i ∈ S} → Ω, (starRingEnd ℂ) (sectorSlice e S Φ y u)
        * slotSumSub e T S (sectorSlice e S Φ y) u) := by
    refine ((integrable_pairCoord_comp S _ hFint).integral_prod_right).congr ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => hpt u y))
  rw [hsplit, hslice]
  exact (integral_re hGint).symm

end Work.BoseBoxFock
