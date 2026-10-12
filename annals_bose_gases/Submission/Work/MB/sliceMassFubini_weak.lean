import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.MB.SlotSumSplitAux
import Submission.Work.MB.slotFacts_boxSlotSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The squared norm of a bounded, measurable state supported in the `n`-particle box is
integrable.**  Weak companion of `Work.BoseBoxFock.integrable_normSq_of_bounded_compactSupport`
(the compact support `tsupport Θ` of the strong version is replaced by the box support
`Function.support Θ ⊆ boxPow n ℓ`, which has finite volume by `Volume_boxPow_lt_top`).

Proved by `Integrable.mono'` against the indicator of the box, so that no `whnf` unification ever
has to unfold the lambda `fun x => ‖Θ x‖ ^ 2`; stated for a *variable* state, so the call sites
never see a large term either. -/
theorem integrable_normSq_of_bounded_boxSupport {n : ℕ} {ℓ : ℝ} {Θ : (Fin n → E3) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ boxPow n ℓ) :
    MeasureTheory.Integrable (fun x => ‖Θ x‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hΘb
  set g : (Fin n → E3) → ℝ := (boxPow n ℓ).indicator (fun _ => max C 0 ^ 2) with hg
  refine MeasureTheory.Integrable.mono' (g := g) ?_ ?_ ?_
  · rw [hg, integrable_indicator_iff (measurableSet_boxPow n ℓ)]
    exact integrableOn_const (volume_boxPow_lt_top n ℓ)
  · exact (hΘm.norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    by_cases hx : x ∈ boxPow n ℓ
    · rw [hg, Set.indicator_of_mem hx]
      have h1 : (0 : ℝ) ≤ ‖Θ x‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC x).trans (le_max_left _ _)) 2
    · rw [hg, Set.indicator_of_notMem hx]
      have h0 : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘs h))
      rw [h0]
      simp

/-- **The weak Fubini (slice) package for the *mass*.**  For modes `e l` that are only measurable,
everywhere bounded and supported in the corpus box `boxL ℓ`, and a state `Φc` that is only
measurable, everywhere bounded and supported in the `n`-particle box `boxPow n ℓ`, the mass of the
`S`-sector `slotExact e S Φc` splits over the complement configurations `y`: the squared-norm
integrand `u ↦ ‖sectorSlice e S Φc y u‖²` is integrable for a.e. `y`, the function
`y ↦ ∫_u ‖sectorSlice e S Φc y u‖²` is integrable, and its integral is `massR (slotExact e S Φc)`.

This is the weak twin of the second/fourth conjuncts of `Work.BoseBoxFock.sliceFubini`, with
`slotExact_measurable_bounded_compactSupport` replaced by `Work.MB.slotExact_mb_weak` (box support
in place of compact support) and `Work.BoseBoxFock.integrable_pairCoord_comp` /
`sliceFubini_integral_pairCoord_split_real` doing the Fubini step. -/
theorem sliceMassFubini_weak {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) (Φc : Work.BoseDict.Xn n → ℂ)
    (hΦm : Measurable Φc) (hΦb : ∃ C, ∀ x, ‖Φc x‖ ≤ C)
    (hΦsupp : Function.support Φc ⊆ Work.MB.boxPow n ℓ) :
    (∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
        MeasureTheory.Integrable (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
          ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2))
      ∧ MeasureTheory.Integrable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
          ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
            ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2)
      ∧ (∫ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
            ∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
              ‖Work.BoseBoxFock.sectorSlice e S Φc y u‖ ^ 2)
          = Work.BoseBoxFock.massR (Work.BoseBoxFock.slotExact e S Φc) := by
  classical
  obtain ⟨hΘm, ⟨C, _hC0, hCb⟩, hΘs⟩ := slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb
  have hΘsupp : Function.support (Work.BoseBoxFock.slotExact e S Φc) ⊆ boxPow n ℓ :=
    hΘs hΦsupp
  have hGint : MeasureTheory.Integrable
      (fun x : Fin n → E3 => ‖Work.BoseBoxFock.slotExact e S Φc x‖ ^ 2) :=
    integrable_normSq_of_bounded_boxSupport hΘm ⟨C, hCb⟩ hΘsupp
  have hGprod := Work.BoseBoxFock.sliceFubini_integrable_pairCoord_comp_real S
    (fun x : Fin n → E3 => ‖Work.BoseBoxFock.slotExact e S Φc x‖ ^ 2) hGint
  refine ⟨?_, ?_, ?_⟩
  · -- the squared-norm integrand is integrable for a.e. `y`
    filter_upwards [hGprod.prod_left_ae] with y hy
    exact hy.congr (Filter.Eventually.of_forall (fun u => rfl))
  · -- the outer integral is integrable
    refine hGprod.integral_prod_right.congr ?_
    filter_upwards with y
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => rfl))
  · -- the value of the integral is the sector mass
    rw [Work.BoseBoxFock.massR_eq_integral_normSq]
    exact (Work.BoseBoxFock.sliceFubini_integral_pairCoord_split_real S
      (fun x : Fin n → E3 => ‖Work.BoseBoxFock.slotExact e S Φc x‖ ^ 2) hGint).symm

end Work.MB
