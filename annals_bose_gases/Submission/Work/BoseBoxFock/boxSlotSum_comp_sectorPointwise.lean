import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxSlotSum_comp_sector_split
import Submission.Work.BoseBoxFock.sectorCollapse
import Submission.Work.BoseBoxFock.slotSum_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotSum_comp_sectorPointwise` — the pointwise decoupling of a *composite*
slot sum

`slotSum_sectorPointwise` (`slotSum_sectorPointwise.lean`) proves that the quadratic form of a
single first-quantised slot sum `boxSlotSum e T` on the `S`-sector `Θ = slotExact e S Φ`
factorises over the complement configuration `y`:

    `⟨Θ, boxSlotSum e T Θ⟩ = ∫_y ⟨slice_y, slotSumSub e T S slice_y⟩`,

where `slice_y = sectorSlice e S Φ y` is the slice of `Θ` at `y`.  The present file proves the
same factorisation for a **composition** `boxSlotSum e T₁ ∘ boxSlotSum e T₂` (the shape of a
product of two one-body rows of the box Hamiltonian), which is what the box ↔ model bridge needs
whenever two rows are applied in succession:

    `⟨Θ, boxSlotSum e T₁ (boxSlotSum e T₂ Θ)⟩
        = ∫_y ⟨slice_y, slotSumSub e T₁ S (slotSumSub e T₂ S slice_y)⟩`.

The new ingredient is that the *inner* state `Ψ := boxSlotSum e T₂ Θ` is no longer a sector of a
state, but only has the two structural properties the decoupling uses:

* `Ψ` is measurable and bounded (`boxSlotSum_measurable_bounded`);
* `Ψ` has no `V`-component in the slots outside `S`
  (`boxSlotSum_slotProj1_comm` + `slotProj1_slotExact_eq_zero` + `boxSlotSum_zero`).

Both are proved here, and the pointwise decoupling and the Fubini step of
`slotSum_sectorPointwise` are then rerun verbatim with `Θ ↦ Ψ`:

* `boxSlotOf_pairCoord_gen` — the slot operator of the full configuration, applied at
  `pairCoord S u y`, is the `↥S`-slot operator `slotOfSub` applied to the slice (arbitrary state);
* `boxSlotSum_pairCoord_gen` — the pointwise decoupling for a state with no `V`-component
  outside `S`;
* `slotSum_sectorPointwise_gen` — the Fubini/integrability step in the same generality;
* `boxSlotSum_comp_sectorPointwise` — the target.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The pointwise decoupling for a state with no `V`-component outside `S` -/

/-- **`Function.update` and `pairCoord`.**  A `V`-supported rank-one slot operator on the assembled
configuration is the `↥S`-slot operator on the slice, for an *arbitrary* state `Ψ`: this is
`boxSlotOf_pairCoord` with the sector `slotExact e S Φ` and its slice `sectorSlice e S Φ y`
replaced by `Ψ` and `u' ↦ Ψ (pairCoord S u' y)`.  The proof uses only
`update_pairCoord_mem`. -/
theorem boxSlotOf_pairCoord_gen {m n : ℕ} (e : Fin m → Ω → ℂ) (w v : Fin m → ℝ)
    (S : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ) (j : Fin n) (hj : j ∈ S)
    (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω) :
    Work.BoseDict.boxSlotOf e w v j Ψ (pairCoord S u y)
      = slotOfSub e w v ⟨j, hj⟩ (fun u' => Ψ (pairCoord S u' y)) u := by
  rw [Work.BoseDict.boxSlotOf, slotOfSub, pairCoord_mem S u y j hj]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [update_pairCoord_mem]

/-- **The slot sum of an `S`-empty state, read at the assembled configuration, is the `↥S`-slot sum
of its slice.**  This is `boxSlotSum_pairCoord` with the sector `slotExact e S Φ` replaced by an
arbitrary measurable bounded state `Ψ` whose slots outside `S` carry no `V`-component
(`∀ j ∉ S, slotProj1 e j Ψ = 0`), which is exactly the hypothesis under which the slot sum
collapses (`boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero`). -/
theorem boxSlotSum_pairCoord_gen {m n : ℕ} (e : Fin m → Ω → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n)) (Ψ : (Fin n → Ω) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨ0 : ∀ j : Fin n, j ∉ S → slotProj1 e j Ψ = 0)
    (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω) :
    Work.BoseDict.boxSlotSum e T Ψ (pairCoord S u y)
      = slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u := by
  classical
  rw [boxSlotSum_eq_sum_mem_of_slotProj1_eq_zero e T S Ψ he hec horth hint hΨm hΨb hΨ0]
  simp only [slotSumSub, Finset.sum_apply, Pi.smul_apply]
  rw [← Finset.sum_attach S (fun j => ∑ l : Fin m, ∑ l' : Fin m,
      T (Work.BoseB4.evec m l') l •
        Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Ψ
          (pairCoord S u y))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  rw [boxSlotOf_pairCoord_gen]

/-! ## 2. The Fubini step in the same generality -/

/-- **The pointwise decoupling of a slot sum against a *fixed* sector state.**  For a measurable
bounded state `Ψ` with no `V`-component outside `S`, the quadratic form of `boxSlotSum e T Ψ`
against the sector `Θ = slotExact e S Φ` factorises: the full-space integral splits along
`pairCoord` and the two integrands agree pointwise (`boxSlotSum_pairCoord_gen`). -/
theorem slotSum_sectorPointwise_gen {m n : ℕ}
    (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (Ψ : (Fin n → Ω) → ℂ) (hΨm : Measurable Ψ) (hΨb : ∃ C, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨ0 : ∀ j : Fin n, j ∉ S → slotProj1 e j Ψ = 0) :
    MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re)
    ∧ (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re)
      = (∫ x : Fin n → Ω, star (slotExact e S Φ x) * Work.BoseDict.boxSlotSum e T Ψ x).re := by
  classical
  obtain ⟨hΘm, hΘb, hΘc⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  obtain ⟨hWm, hWb⟩ := boxSlotSum_measurable_bounded e he hec T Ψ hΨm hΨb
  have hFint : MeasureTheory.Integrable (fun x : Fin n → Ω =>
      star (slotExact e S Φ x) * Work.BoseDict.boxSlotSum e T Ψ x) :=
    integrable_mul_of_hasCompactSupport_of_bounded
      (hΘc.comp_left (g := star) (by simp))
      (measurable_star_comp hΘm).aestronglyMeasurable
      (hΘb.imp (fun C hC x => by rw [norm_star]; exact hC x))
      hWm.aestronglyMeasurable hWb
  -- the pointwise identification of the assembled integrand with the slice integrand
  have hpt : ∀ (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
      star (slotExact e S Φ (pairCoord S u y))
          * Work.BoseDict.boxSlotSum e T Ψ (pairCoord S u y)
        = star (sectorSlice e S Φ y u)
          * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u := by
    intro u y
    rw [boxSlotSum_pairCoord_gen e T S Ψ he hec horth hint hΨm hΨb hΨ0 u y]
    rfl
  -- the two full-space integrands, pushed to the product space along `pairCoord`
  have hFprod := integrable_pairCoord_comp S
    (fun x : Fin n → Ω => star (slotExact e S Φ x)
      * Work.BoseDict.boxSlotSum e T Ψ x) hFint
  have hInnerAe : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
      MeasureTheory.Integrable (fun u : {i // i ∈ S} → Ω =>
        star (sectorSlice e S Φ y u)
          * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u) := by
    filter_upwards [hFprod.prod_left_ae] with y hy
    refine hy.congr (Filter.Eventually.of_forall (fun u => ?_))
    exact hpt u y
  have hGY : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
      ∫ u : {i // i ∈ S} → Ω,
        star (sectorSlice e S Φ y u)
          * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u) := by
    refine (hFprod.integral_prod_right).congr ?_
    filter_upwards with y
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact hpt u y
  -- `(∫ u, f y u).re` and `∫ u, (f y u).re` agree for a.e. `y`
  have hAeRe : (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re)
      =ᵐ[volume] (fun y : {i // i ∉ S} → Ω =>
        (∫ u : {i // i ∈ S} → Ω,
          star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re) := by
    filter_upwards [hInnerAe] with y hy
    exact integral_re hy
  -- the Fubini splitting, and the pointwise rewrite to the slice form
  have hsplit : (∫ x : Fin n → Ω, star (slotExact e S Φ x)
        * Work.BoseDict.boxSlotSum e T Ψ x)
      = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          star (slotExact e S Φ (pairCoord S u y))
            * Work.BoseDict.boxSlotSum e T Ψ (pairCoord S u y) :=
    integral_pairCoord_split S _ hFint
  have hslice : (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
        star (slotExact e S Φ (pairCoord S u y))
          * Work.BoseDict.boxSlotSum e T Ψ (pairCoord S u y))
      = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => hpt u y))
  refine ⟨?_, ?_⟩
  · -- the form integrand, with the real part inside the inner integral
    exact hGY.re.congr hAeRe.symm
  · -- the form identity
    calc ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φ y u)
            * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re
        = ∫ y : {i // i ∉ S} → Ω, (∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φ y u)
              * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re :=
          integral_congr_ae hAeRe
      _ = (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φ y u)
              * slotSumSub e T S (fun u' => Ψ (pairCoord S u' y)) u).re :=
          integral_re hGY
      _ = (∫ x : Fin n → Ω,
            star (slotExact e S Φ x) * Work.BoseDict.boxSlotSum e T Ψ x).re := by
          rw [← hslice, ← hsplit]

/-! ## 3. The target -/

theorem boxSlotSum_comp_sectorPointwise {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (S : Finset (Fin n))
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
            * Work.BoseBoxFock.slotSumSub e T₁ S
                (Work.BoseBoxFock.slotSumSub e T₂ S
                  (Work.BoseBoxFock.sectorSlice e S Φ y)) u).re)
    ∧ (∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
          ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
              * Work.BoseBoxFock.slotSumSub e T₁ S
                  (Work.BoseBoxFock.slotSumSub e T₂ S
                    (Work.BoseBoxFock.sectorSlice e S Φ y)) u).re)
      = (∫ x : Fin n → EuclideanSpace ℝ (Fin 3),
          star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x).re := by
  classical
  obtain ⟨hΘm, hΘb, -⟩ :=
    slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.bounded_above_of_compact_support hΦc
  -- the inner state `Ψ = boxSlotSum e T₂ Θ` is measurable and bounded
  obtain ⟨hΨm, hΨb⟩ :=
    boxSlotSum_measurable_bounded e he hec T₂ (slotExact e S Φ) hΘm hΘb
  -- and it has no `V`-component in the slots outside `S`
  have hΨ0 : ∀ j : Fin n, j ∉ S →
      slotProj1 e j (Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φ)) = 0 := by
    intro j hj
    rw [boxSlotSum_slotProj1_comm e he hec horth hint T₂ (slotExact e S Φ) hΘm hΘb j]
    rw [slotProj1_slotExact_eq_zero e he hec horth S j hj Φ hΦ.measurable hΦb]
    exact boxSlotSum_zero e he hec T₂
  -- the general decoupling, at the inner state
  have hgen := slotSum_sectorPointwise_gen e he hec horth hint T₁ S Φ hΦ hΦc
    (Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φ)) hΨm hΨb hΨ0
  -- its slice is the `↥S`-slot sum of the slice of `Φ`
  have hfun : ∀ y : {i // i ∉ S} → Ω,
      (fun u' : {i // i ∈ S} → Ω =>
        Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φ) (pairCoord S u' y))
        = slotSumSub e T₂ S (sectorSlice e S Φ y) := by
    intro y
    funext u'
    exact boxSlotSum_pairCoord e T₂ S Φ he hec horth hint hΦ hΦc u' y
  refine ⟨?_, ?_⟩
  · refine hgen.1.congr ?_
    filter_upwards with y
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    rw [hfun y]
  · rw [← hgen.2]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    rw [hfun y]

end Work.BoseBoxFock
