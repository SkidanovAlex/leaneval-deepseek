import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.dictBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.PCFU.aP_aeStronglyMeasurable`

The slot mean `aP ℓ i Ξ x = ℓ⁻³ ∫_{y ∈ acube ℓ} Ξ (Function.update x i y)` of an
almost-everywhere measurable `Ξ : X n → ℝ` is again almost-everywhere strongly measurable.

The proof is a Fubini / change-of-variables argument.  The map

    U : X n × ℝ³ → X n,   U (x, y) = Function.update x i y

is **quasi-measure-preserving** from `volume ⊗ volume` to `volume`: identifying `X (m+1)` with
`ℝ³ × X m` through the measure-preserving measurable equivalence `kcInsN m i`, the map `U`
becomes the projection `(z, r, y) ↦ (y, r)` forgetting the first coordinate, which is
quasi-measure-preserving.  Consequently `AEMeasurable` transfers from `Ξ` to `Ξ ∘ U`, and
`AEStronglyMeasurable.integral_prod_right'` then gives strong measurability of the `y`-integral.
-/

noncomputable section

namespace Work.PCFU

open MeasureTheory
open Submission.BoseGases

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- The basic `Function.update` identity at the coordinate-insertion equivalence `kcInsN`:
replacing the `i`-th coordinate of `kcInsN m i (z, r)` by `y` gives `kcInsN m i (y, r)`. -/
lemma update_kcInsN {m : ℕ} (i : Fin (m + 1)) (z y : Sp) (r : X m) :
    Function.update (kcInsN m i (z, r)) i y = kcInsN m i (y, r) := by
  funext j
  by_cases hj : j = i
  · rw [hj, Function.update_apply, if_pos rfl, kc_insN_apply_same]
  · rw [Function.update_apply, if_neg hj]
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hj
    rw [← hj', kc_insN_apply_succ, kc_insN_apply_succ]

/-- The measure of the `i`-th slice through `y` of a measurable set, computed in the
`kcInsN`-coordinates: the forgotten coordinate contributes a factor `volume univ`. -/
lemma measure_update_slice {m : ℕ} (i : Fin (m + 1)) (y : Sp) {s : Set (X (m + 1))}
    (hs : MeasurableSet s) :
    (volume : Measure (X (m + 1))) {x : X (m + 1) | Function.update x i y ∈ s}
      = (volume : Measure Sp) Set.univ
        * (volume : Measure (X m)) {r : X m | kcInsN m i (y, r) ∈ s} := by
  have hκm : MeasurePreserving (⇑(kcInsN m i)) ((volume : Measure Sp).prod (volume : Measure (X m)))
      (volume : Measure (X (m + 1))) := kc_mp_insN m i
  have hA : MeasurableSet {x : X (m + 1) | Function.update x i y ∈ s} :=
    hs.preimage (by fun_prop)
  have h1 : (volume : Measure (X (m + 1))) {x : X (m + 1) | Function.update x i y ∈ s}
      = ((volume : Measure Sp).prod (volume : Measure (X m)))
          ((⇑(kcInsN m i)) ⁻¹' {x : X (m + 1) | Function.update x i y ∈ s}) := by
    rw [← hκm.map_eq]
    exact Measure.map_apply hκm.measurable hA
  rw [h1]
  have h2 : (⇑(kcInsN m i)) ⁻¹' {x : X (m + 1) | Function.update x i y ∈ s}
      = Set.univ ×ˢ {r : X m | kcInsN m i (y, r) ∈ s} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and]
    rw [update_kcInsN i p.1 y p.2]
  rw [h2, Measure.prod_prod]

/-- **The `update` map is quasi-measure-preserving.**  For every `i : Fin (m+1)` the map
`(x, y) ↦ Function.update x i y` pushes the product Lebesgue measure forward to a measure
dominated by Lebesgue measure on `X (m+1)`. -/
theorem quasiMeasurePreserving_update {m : ℕ} (i : Fin (m + 1)) :
    Measure.QuasiMeasurePreserving
      (fun p : X (m + 1) × Sp => Function.update p.1 i p.2)
      ((volume : Measure (X (m + 1))).prod (volume : Measure Sp))
      (volume : Measure (X (m + 1))) := by
  refine ⟨?_, Measure.AbsolutelyContinuous.mk ?_⟩
  · exact (by fun_prop : Measurable (fun p : X (m + 1) × Sp => Function.update p.1 i p.2))
  · intro s hs hμs
    have hκm : MeasurePreserving (⇑(kcInsN m i)) ((volume : Measure Sp).prod (volume : Measure (X m)))
        (volume : Measure (X (m + 1))) := kc_mp_insN m i
    have hUmeas : MeasurableSet
        ((fun p : X (m + 1) × Sp => Function.update p.1 i p.2) ⁻¹' s) :=
      hs.preimage (by fun_prop)
    rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply_symm hUmeas]
    have hT : MeasurableSet ((⇑(kcInsN m i)) ⁻¹' s) := hs.preimage hκm.measurable
    have hmap1 : (Measure.map (⇑(kcInsN m i))
          ((volume : Measure Sp).prod (volume : Measure (X m)))) s
        = ((volume : Measure Sp).prod (volume : Measure (X m))) ((⇑(kcInsN m i)) ⁻¹' s) :=
      Measure.map_apply hκm.measurable hs
    have hS : ((volume : Measure Sp).prod (volume : Measure (X m))) ((⇑(kcInsN m i)) ⁻¹' s) = 0 := by
      rw [← hmap1, hκm.map_eq]
      exact hμs
    have hden : (∫⁻ z : Sp, (volume : Measure (X m))
          (Prod.mk z ⁻¹' ((⇑(kcInsN m i)) ⁻¹' s)) ∂(volume : Measure Sp)) = 0 := by
      rw [← Measure.prod_apply hT]
      exact hS
    have hae : ∀ᵐ y ∂(volume : Measure Sp),
        (volume : Measure (X m)) (Prod.mk y ⁻¹' ((⇑(kcInsN m i)) ⁻¹' s)) = 0 :=
      (lintegral_eq_zero_iff (measurable_measure_prodMk_left hT)).mp hden
    have hcongr : (fun y : Sp => (volume : Measure (X (m + 1)))
          ((fun x : X (m + 1) => (x, y))
            ⁻¹' ((fun p : X (m + 1) × Sp => Function.update p.1 i p.2) ⁻¹' s)))
        =ᵐ[(volume : Measure Sp)] 0 := by
      filter_upwards [hae] with y hy
      have hy' : (volume : Measure (X m)) {r : X m | kcInsN m i (y, r) ∈ s} = 0 := hy
      have hset : (fun x : X (m + 1) => (x, y))
            ⁻¹' ((fun p : X (m + 1) × Sp => Function.update p.1 i p.2) ⁻¹' s)
          = {x : X (m + 1) | Function.update x i y ∈ s} := rfl
      show (volume : Measure (X (m + 1)))
          ((fun x : X (m + 1) => (x, y))
            ⁻¹' ((fun p : X (m + 1) × Sp => Function.update p.1 i p.2) ⁻¹' s)) = 0
      rw [hset, measure_update_slice i y hs, hy', mul_zero]
    rw [lintegral_congr_ae hcongr]
    simp

theorem aP_aeStronglyMeasurable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Ξ : Submission.BoseGases.X n → ℝ}
    (hΞ : AEMeasurable Ξ (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.aP ℓ i Ξ)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    have hqmp_full := quasiMeasurePreserving_update (m := m) i
    have hqmp : Measure.QuasiMeasurePreserving
        (fun p : X (m + 1) × Sp => Function.update p.1 i p.2)
        ((volume : Measure (X (m + 1))).prod ((volume : Measure Sp).restrict (acube ℓ)))
        (volume : Measure (X (m + 1))) :=
      hqmp_full.mono_left (Measure.absolutelyContinuous_of_le
        (Measure.prod_mono le_rfl Measure.restrict_le_self))
    have hAEM : AEMeasurable (fun p : X (m + 1) × Sp => Ξ (Function.update p.1 i p.2))
        ((volume : Measure (X (m + 1))).prod ((volume : Measure Sp).restrict (acube ℓ))) :=
      hΞ.comp_quasiMeasurePreserving hqmp
    have hAESM : AEStronglyMeasurable (fun p : X (m + 1) × Sp => Ξ (Function.update p.1 i p.2))
        ((volume : Measure (X (m + 1))).prod ((volume : Measure Sp).restrict (acube ℓ))) :=
      hAEM.aestronglyMeasurable
    have hint : AEStronglyMeasurable
        (fun x : X (m + 1) =>
          ∫ y : Sp, Ξ (Function.update x i y) ∂((volume : Measure Sp).restrict (acube ℓ)))
        (volume : Measure (X (m + 1))) := hAESM.integral_prod_right'
    have hfin := hint.const_mul (1 / ℓ ^ 3)
    have hgoal : (fun x : X (m + 1) =>
          (1 / ℓ ^ 3) * ∫ y : Sp, Ξ (Function.update x i y) ∂((volume : Measure Sp).restrict (acube ℓ)))
        = Submission.BoseGases.aP ℓ i Ξ := by
      funext x
      rfl
    exact hgoal ▸ hfin

end Work.PCFU
