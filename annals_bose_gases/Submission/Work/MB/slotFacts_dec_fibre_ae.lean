import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotFactsDerive
import Submission.Work.MB.SlotSumSplitAux
import Submission.Work.MB.slotSectorWeak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.slotFacts_dec_fibre_ae` — the derived fibre facts at the *weak* mode hypotheses

`Work.BoseBoxFock.SlotFacts.dec_fibre` derives the two fibre facts — the integral decoupling of
the sector form and the integrability of the fibre integrand — from the three operator-side
fields of `Work.BoseBoxFock.SlotFacts`, at modes `e` that are `Continuous` with
`HasCompactSupport` and at a state `Φc` that is continuous with compact support.

Those regularity hypotheses are *unsatisfiable* at the honest modes of the box ↔ model bridge
(`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate mode is a.e. the box indicator,
which has no continuous representative).  The present module proves the very same two fibre facts
on the weak bundle of `Submission/Work/MB/`:

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ` (supported in the corpus box),

with a state `Φc` that is only measurable, everywhere bounded, and supported in the `n`-particle
box `boxPow n ℓ`.

The proof is the strong one (`Submission/Work/BoseBoxFock/slotFactsDerive.lean`) with the two
inputs replaced:

* `slotExact_slotGood` (good *and* compactly supported sector) ↦ `Work.MB.slotExact_mb_weak`
  (measurable, bounded and box-supported sector — the box support is exactly what the compact
  support was used for);
* `integrable_star_mul_of_compact` ↦ `integrable_star_mul_of_support` below: the sector is
  supported in the box `boxPow n ℓ` of finite measure, so the bounded product is integrable there
  (`Work.MB.integrable_of_bdd_of_support`), which is all that the Fubini step
  (`Work.BoseBoxFock.integral_pairCoord_split` / `integrable_pairCoord_comp`) needs.

Everything here is `sorry`-free.
-/

noncomputable section

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- `star f * g` is integrable when `f` is measurable, everywhere bounded and supported in the box
`boxPow n ℓ` (of finite measure), and `g` is measurable and everywhere bounded.

This is the weak replacement of `Work.BoseBoxFock.integrable_star_mul_of_compact`: the compact
support of `f` is used in the strong chain only to make the product integrable, and the box
support together with the finite measure of `boxPow n ℓ` does that just as well
(`Work.MB.integrable_of_bdd_of_support`). -/
private theorem integrable_star_mul_of_support {n : ℕ} {ℓ : ℝ} {f g : (Fin n → E3) → ℂ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (hfs : Function.support f ⊆ boxPow n ℓ)
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => star (f x) * g x) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  refine integrable_of_bdd_of_support (measurableSet_boxPow n ℓ) (volume_boxPow_lt_top n ℓ)
    ((Complex.continuous_conj.measurable.comp hfm).mul hgm).aestronglyMeasurable
    (C := max Cf 0 * max Cg 0) ?_ ?_
  · intro x
    rw [norm_mul, norm_star]
    exact mul_le_mul ((hCf x).trans (le_max_left _ _)) ((hCg x).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · intro x hx
    rw [Function.notMem_support.mp (fun h => hx (hfs h)), star_zero, zero_mul]

theorem slotFacts_dec_fibre_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (Φc : Work.BoseDict.Xn n → ℂ) (hΦm : Measurable Φc)
    (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : Function.support Φc ⊆ Work.MB.boxPow n ℓ)
    {Op : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ)}
    {OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)}
    (h : Work.BoseBoxFock.SlotFacts e Φc Op OpS) :
    (∀ S : Finset (Fin n), MeasureTheory.Integrable (fun y : {i // i ∉ S} →
        EuclideanSpace ℝ (Fin 3) =>
        ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re))
      ∧ (∀ S : Finset (Fin n),
        (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
            * Op (Work.BoseBoxFock.slotExact e S Φc) x).re
          = ∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
              ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
                (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
                  * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re) := by
  classical
  -- the two conjuncts are obtained for each sector `S` by one and the same computation
  have key : ∀ S : Finset (Fin n),
      MeasureTheory.Integrable (fun y : {i // i ∉ S} → E3 =>
        ∫ u : {i // i ∈ S} → E3,
          (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re)
      ∧ ((∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
            * Op (Work.BoseBoxFock.slotExact e S Φc) x).re
          = ∫ y : {i // i ∉ S} → E3, ∫ u : {i // i ∈ S} → E3,
              (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
                * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re) := by
    intro S
    -- the sector of the state: measurable, bounded, and supported in the box
    obtain ⟨hΘm, hΘb, hΘsupp0⟩ := slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb
    obtain ⟨CΘ, -, hCΘ⟩ := hΘb
    have hΘsupp : Function.support (Work.BoseBoxFock.slotExact e S Φc) ⊆ boxPow n ℓ :=
      hΘsupp0 hΦsupp
    have hΘgood : Work.BoseBoxFock.SlotGood (Work.BoseBoxFock.slotExact e S Φc) :=
      ⟨hΘm, ⟨CΘ, hCΘ⟩⟩
    have hOpΘ : Work.BoseBoxFock.SlotGood (Op (Work.BoseBoxFock.slotExact e S Φc)) :=
      h.good _ hΘgood
    -- the full-space integrand is integrable (box support + finite measure)
    have hFint : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
        star (Work.BoseBoxFock.slotExact e S Φc x)
          * Op (Work.BoseBoxFock.slotExact e S Φc) x) :=
      integrable_star_mul_of_support hΘm ⟨CΘ, hCΘ⟩ hΘsupp hOpΘ.1 hOpΘ.2
    -- pushed to the product space
    have hFprod : MeasureTheory.Integrable
        (fun q : ({i // i ∈ S} → E3) × ({i // i ∉ S} → E3) =>
          star (Work.BoseBoxFock.slotExact e S Φc (Work.BoseBoxFock.pairCoord S q.1 q.2))
            * Op (Work.BoseBoxFock.slotExact e S Φc)
                (Work.BoseBoxFock.pairCoord S q.1 q.2)) :=
      Work.BoseBoxFock.integrable_pairCoord_comp S _ hFint
    -- the pointwise identity between the two integrands
    have hpt : ∀ (u : {i // i ∈ S} → E3) (y : {i // i ∉ S} → E3),
        star (Work.BoseBoxFock.slotExact e S Φc (Work.BoseBoxFock.pairCoord S u y))
            * Op (Work.BoseBoxFock.slotExact e S Φc)
                (Work.BoseBoxFock.pairCoord S u y)
          = star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u := by
      intro u y
      rw [h.slice S u y]
      rfl
    have hInnerAe : ∀ᵐ y ∂(volume : Measure ({i // i ∉ S} → E3)),
        MeasureTheory.Integrable (fun u : {i // i ∈ S} → E3 =>
          star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u) := by
      filter_upwards [hFprod.prod_left_ae] with y hy
      refine hy.congr (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    have hGY : MeasureTheory.Integrable (fun y : {i // i ∉ S} → E3 =>
        ∫ u : {i // i ∈ S} → E3,
          star (Work.BoseBoxFock.sectorSlice e S Φc y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u) := by
      refine (hFprod.integral_prod_right).congr ?_
      filter_upwards with y
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      exact hpt u y
    -- `(∫ u, f y u).re` and `∫ u, (f y u).re` agree for a.e. `y`
    have hAeRe : (fun y : {i // i ∉ S} → E3 =>
          ∫ u : {i // i ∈ S} → E3,
            (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re)
        =ᵐ[volume] (fun y : {i // i ∉ S} → E3 =>
          (∫ u : {i // i ∈ S} → E3,
            star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re) := by
      filter_upwards [hInnerAe] with y hy
      exact integral_re hy
    refine ⟨hGY.re.congr hAeRe.symm, ?_⟩
    calc (∫ x : Work.BoseDict.Xn n, star (Work.BoseBoxFock.slotExact e S Φc x)
            * Op (Work.BoseBoxFock.slotExact e S Φc) x).re
        = (∫ y : {i // i ∉ S} → E3, ∫ u : {i // i ∈ S} → E3,
            star (Work.BoseBoxFock.slotExact e S Φc (Work.BoseBoxFock.pairCoord S u y))
              * Op (Work.BoseBoxFock.slotExact e S Φc)
                  (Work.BoseBoxFock.pairCoord S u y)).re := by
          rw [Work.BoseBoxFock.integral_pairCoord_split S
            (fun x : Work.BoseDict.Xn n =>
              star (Work.BoseBoxFock.slotExact e S Φc x)
                * Op (Work.BoseBoxFock.slotExact e S Φc) x) hFint]
      _ = (∫ y : {i // i ∉ S} → E3, ∫ u : {i // i ∈ S} → E3,
            star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
          exact hpt u y
      _ = ∫ y : {i // i ∉ S} → E3, (∫ u : {i // i ∈ S} → E3,
            star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re :=
          Work.BoseBoxFock.re_integral_of_integrable hGY
      _ = ∫ y : {i // i ∉ S} → E3, ∫ u : {i // i ∈ S} → E3,
            (star (Work.BoseBoxFock.sectorSlice e S Φc y u)
              * OpS S (Work.BoseBoxFock.sectorSlice e S Φc y) u).re :=
          integral_congr_ae hAeRe.symm
  exact ⟨fun S => (key S).1, fun S => (key S).2⟩

end Work.MB
