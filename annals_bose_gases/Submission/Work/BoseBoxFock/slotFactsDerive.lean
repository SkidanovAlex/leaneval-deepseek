import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotFactsInst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotFactsDerive` — the two fibre facts *derived* from `SlotFacts`

`Work.BoseBoxFock.SlotFacts` carries three operator-side facts (goodness, the *pointwise* sector
decoupling, and the sector splitting of the quadratic form).  The generic slice selection
`Work.BoseBoxFock.exists_slice_le_window_of_op` additionally needs

* the *integral* decoupling `(∫ star (slotExact e S Φc) · Op (slotExact e S Φc)).re
  = ∫_y ∫_u (star slice · OpS S slice).re`, and
* the integrability of `y ↦ ∫_u (star slice · OpS S slice).re`,

and both are derived here from the three fields, exactly along the lines of
`Work.BoseBoxFock.sliceFubini`: the pointwise identity turns the sector integral into the
product-space integral of the decoupled integrand (`integrable_pairCoord_comp`), the section
integrability and the two identities follow from `Integrable.prod_left_ae` /
`Integrable.integral_prod_right`, and `integral_re` converts between `(∫ f).re` and `∫ f.re`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- The real part of a Bochner integral of a complex-valued function. -/
theorem re_integral_of_integrable {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℂ} (hf : MeasureTheory.Integrable f μ) :
    (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  have h := Complex.reCLM.integral_comp_comm hf
  simp only [Complex.reCLM_apply] at h
  exact h.symm

/-- **The derived fibre facts.**  For any operator satisfying `SlotFacts` at a continuous compactly
supported state `Φc`, the *integral* decoupling of the sector form holds and the fibre integrand is
integrable in the complement configuration. -/
theorem SlotFacts.dec_fibre {m n : ℕ} {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    {Op : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (h : SlotFacts e Φc Op OpS) :
    (∀ S : Finset (Fin n), MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          (star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re))
    ∧ (∀ S : Finset (Fin n),
        (∫ x : Xn n, star (slotExact e S Φc x) * Op (slotExact e S Φc) x).re
          = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
              (star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re) := by
  classical
  constructor
  · intro S
    -- the sector is good and compactly supported
    obtain ⟨hΘgood, hΘc⟩ := slotExact_slotGood he hec S Φc hΦcont hΦc
    -- the full-space integrand
    have hFint : MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op (slotExact e S Φc) x) :=
      integrable_star_mul_of_compact hΘc hΘgood (h.good _ hΘgood)
    -- pushed to the product space
    have hFprod : MeasureTheory.Integrable
        (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) =>
          star (slotExact e S Φc (pairCoord S q.1 q.2))
            * Op (slotExact e S Φc) (pairCoord S q.1 q.2)) :=
      integrable_pairCoord_comp S _ hFint
    -- the pointwise identity between the two integrands
    have hpt : ∀ (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
        star (slotExact e S Φc (pairCoord S u y)) * Op (slotExact e S Φc) (pairCoord S u y)
          = star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u := by
      intro u y
      rw [h.slice S u y]
      rfl
    have hInnerAe : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
        MeasureTheory.Integrable (fun u : {i // i ∈ S} → Ω =>
          star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u) := by
      filter_upwards [hFprod.prod_left_ae] with y hy
      refine hy.congr (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    have hGY : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u) := by
      refine (hFprod.integral_prod_right).congr ?_
      filter_upwards with y
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    -- `(∫ u, f y u).re` and `∫ u, (f y u).re` agree for a.e. `y`
    have hAeRe : (fun y : {i // i ∉ S} → Ω =>
          ∫ u : {i // i ∈ S} → Ω,
            (star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re)
        =ᵐ[volume] (fun y : {i // i ∉ S} → Ω =>
          (∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re) := by
      filter_upwards [hInnerAe] with y hy
      exact integral_re hy
    exact hGY.re.congr hAeRe.symm
  · intro S
    obtain ⟨hΘgood, hΘc⟩ := slotExact_slotGood he hec S Φc hΦcont hΦc
    have hFint : MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op (slotExact e S Φc) x) :=
      integrable_star_mul_of_compact hΘc hΘgood (h.good _ hΘgood)
    have hFprod : MeasureTheory.Integrable
        (fun q : ({i // i ∈ S} → Ω) × ({i // i ∉ S} → Ω) =>
          star (slotExact e S Φc (pairCoord S q.1 q.2))
            * Op (slotExact e S Φc) (pairCoord S q.1 q.2)) :=
      integrable_pairCoord_comp S _ hFint
    have hpt : ∀ (u : {i // i ∈ S} → Ω) (y : {i // i ∉ S} → Ω),
        star (slotExact e S Φc (pairCoord S u y)) * Op (slotExact e S Φc) (pairCoord S u y)
          = star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u := by
      intro u y
      rw [h.slice S u y]
      rfl
    have hInnerAe : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → Ω)),
        MeasureTheory.Integrable (fun u : {i // i ∈ S} → Ω =>
          star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u) := by
      filter_upwards [hFprod.prod_left_ae] with y hy
      refine hy.congr (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    have hGY : MeasureTheory.Integrable (fun y : {i // i ∉ S} → Ω =>
        ∫ u : {i // i ∈ S} → Ω,
          star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u) := by
      refine (hFprod.integral_prod_right).congr ?_
      filter_upwards with y
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    have hAeRe : (fun y : {i // i ∉ S} → Ω =>
          ∫ u : {i // i ∈ S} → Ω,
            (star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re)
        =ᵐ[volume] (fun y : {i // i ∉ S} → Ω =>
          (∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re) := by
      filter_upwards [hInnerAe] with y hy
      exact integral_re hy
    calc (∫ x : Xn n, star (slotExact e S Φc x) * Op (slotExact e S Φc) x).re
        = (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
            star (slotExact e S Φc (pairCoord S u y))
              * Op (slotExact e S Φc) (pairCoord S u y)).re := by
          rw [integral_pairCoord_split S
            (fun x : Xn n => star (slotExact e S Φc x) * Op (slotExact e S Φc) x) hFint]
      _ = (∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          exact hpt u y
      _ = ∫ y : {i // i ∉ S} → Ω, (∫ u : {i // i ∈ S} → Ω,
            star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re :=
          re_integral_of_integrable hGY
      _ = ∫ y : {i // i ∉ S} → Ω, ∫ u : {i // i ∈ S} → Ω,
            (star (sectorSlice e S Φc y u) * OpS S (sectorSlice e S Φc y) u).re :=
          integral_congr_ae hAeRe.symm

end Work.BoseBoxFock
