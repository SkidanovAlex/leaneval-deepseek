import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3FibreQ_int
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3FibreQ`

The fibre (slice) forms of the block-III one-slot pairing.

* **Part 1** is the exact `L²`-form of the slot-`j` rank-one pairing with the (bounded, compactly
  supported) kernel `K (a, b) = w a * conj (w b)`: splitting the configuration along the coordinate
  `j` (`integral_fibre_one`, along the measure preserving equivalence `fibreIns j`), exchanging the
  two remaining variables by Fubini and moving the complex conjugate through the Bochner integral
  (`integral_conj`) turns the pairing `⟨Ψ, w_j Ξ⟩` into the `L²`-pairing of the two fibres
  `x' ↦ ∫ u, conj (w u) · Ψ (x'[j ↦ u])`.  The only integrability input is the sibling
  `PB3FibreQ_int` (the slot operator is bounded on `L²`; it is proved there from the `L²`-bounds on
  `Ψ`, `Ξ` and on `w`).
* **Part 2** is the box identity: the `χ_ℓ`-weighted `L²`-mass of the box projection `boxQ ℓ j Ψ`
  over the box `abox n ℓ` equals the iterated box integral of the same quantity written through the
  mean-free part `mf` of the slot section `sect j x' Ψ`.  This is the slice identity
  `setIntegral_insertCoord_slice` (for the continuous integrand), a Fubini exchange of the two box
  integrals and the pointwise identification `boxQ ℓ j Ψ (x'[j ↦ w]) = mf ℓ (sect j x' Ψ) w`
  (the box `acube ℓ` of `boxQ` is the box `boxL ℓ` of `mf`).

`sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary identities -/

/-- The fibre insertion of `integral_fibre_two` is the coordinate insertion of `PB3Defs`. -/
lemma fibreIns_eq_insertCoord {n : ℕ} (j : Fin n) (v : E3)
    (x' : {k : Fin n // k ≠ j} → E3) : fibreIns j v x' = insertCoord j v x' := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [fibreIns]
  · simp [fibreIns, insertCoord, hk]

/-- The inserted coordinate evaluates to the inserted value. -/
lemma insertCoord_apply_self {n : ℕ} (j : Fin n) (v : E3)
    (x' : {k : Fin n // k ≠ j} → E3) : insertCoord j v x' j = v := by
  rw [insertCoord_eq]; simp

/-! ## 2. Part 1: the fibre identity, modulo integrability -/

/-- **The fibre form of the slot-`j` rank-one pairing.**  Assuming the pairing integrand is
integrable (the sibling `PB3FibreQ_int`), splitting the configuration along the slot `j`, exchanging
the two remaining variables (Fubini) and conjugating the resulting integral produces the `L²`
pairing of the two fibres. -/
lemma fibre_part1 {n : ℕ} (j : Fin n) {Ψ Ξ : Xn n → ℂ} {w : E3 → ℂ}
    (hFint : Integrable (fun x : Xn n => (starRingEnd ℂ) (Ψ x)
        * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u))))
      (volume : Measure (Xn n))) :
    (∫ x : Xn n, (starRingEnd ℂ) (Ψ x)
        * (w (x j) * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (Function.update x j u))))
      = ∫ x' : {k : Fin n // k ≠ j} → E3,
          (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (insertCoord j u x'))
            * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (insertCoord j u x')) := by
  classical
  set g : E3 → ({k : Fin n // k ≠ j} → E3) → ℂ := fun v y =>
    (starRingEnd ℂ) (Ψ (insertCoord j v y))
      * (w v * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (insertCoord j u y))) with hg
  have hFins : Integrable (fun q : E3 × ({k : Fin n // k ≠ j} → E3) =>
      (starRingEnd ℂ) (Ψ (fibreIns j q.1 q.2))
        * (w ((fibreIns j q.1 q.2) j)
            * (∫ u : E3, (starRingEnd ℂ) (w u)
                * Ξ (Function.update (fibreIns j q.1 q.2) j u))))
      (volume : Measure (E3 × ({k : Fin n // k ≠ j} → E3))) :=
    ((measurePreserving_fibreIns j).integrable_comp hFint.aestronglyMeasurable).mpr hFint
  have hpt : ∀ q : E3 × ({k : Fin n // k ≠ j} → E3),
      (starRingEnd ℂ) (Ψ (fibreIns j q.1 q.2))
        * (w ((fibreIns j q.1 q.2) j)
            * (∫ u : E3, (starRingEnd ℂ) (w u)
                * Ξ (Function.update (fibreIns j q.1 q.2) j u)))
      = g q.1 q.2 := by
    intro q
    rw [hg]
    simp only [fibreIns_eq_insertCoord, insertCoord_apply_self, update_insertCoord]
  have hGint : Integrable (Function.uncurry g)
      ((volume : Measure E3).prod (volume : Measure ({k : Fin n // k ≠ j} → E3))) := by
    have h1 := hFins
    rw [Measure.volume_eq_prod E3 ({k : Fin n // k ≠ j} → E3)] at h1
    exact h1.congr (Filter.Eventually.of_forall hpt)
  rw [integral_fibre_one (ι := Fin n) j hFint]
  simp only [fibreIns_eq_insertCoord]
  have hstep1 : (∫ v : E3, ∫ y : ({k : Fin n // k ≠ j} → E3),
        (starRingEnd ℂ) (Ψ (insertCoord j v y))
          * (w ((insertCoord j v y) j)
              * (∫ u : E3, (starRingEnd ℂ) (w u)
                  * Ξ (Function.update (insertCoord j v y) j u))))
      = ∫ v : E3, ∫ y : ({k : Fin n // k ≠ j} → E3), g v y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hg]
    simp only [insertCoord_apply_self, update_insertCoord]
  rw [hstep1, integral_integral_swap hGint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hC : (∫ v : E3, g v y)
      = (∫ v : E3, (starRingEnd ℂ) (Ψ (insertCoord j v y)) * w v)
        * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (insertCoord j u y)) := by
    rw [hg]
    simp only
    rw [show (∫ v : E3, (starRingEnd ℂ) (Ψ (insertCoord j v y))
          * (w v * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (insertCoord j u y))))
        = ∫ v : E3, ((starRingEnd ℂ) (Ψ (insertCoord j v y)) * w v)
            * (∫ u : E3, (starRingEnd ℂ) (w u) * Ξ (insertCoord j u y)) from
        integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)]
    rw [integral_mul_const]
  rw [hC]
  have hconj : (∫ v : E3, (starRingEnd ℂ) (Ψ (insertCoord j v y)) * w v)
      = (starRingEnd ℂ) (∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (insertCoord j u y)) := by
    rw [← integral_conj (μ := (volume : Measure E3))
      (f := fun u : E3 => (starRingEnd ℂ) (w u) * Ψ (insertCoord j u y))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [map_mul, starRingEnd_apply, star_star, mul_comm]
  rw [hconj]

/-! ## 3. Part 2 helpers -/

/-- Pointwise identification of `boxQ` at an inserted coordinate with `mf` of the section: the box
`acube ℓ` of `boxQ` is the box `boxL ℓ` of `mf`. -/
lemma boxQ_insertCoord_eq_mf_sect {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    (Ψ : Xn n → ℂ) (w : E3) (x' : {k : Fin n // k ≠ j} → E3) :
    boxQ ℓ j Ψ (insertCoord j w x') = mf ℓ (sect j x' Ψ) w := by
  simp only [boxQ, mf, sect]
  rw [← corpusBox_boxL_eq_acube hℓ]
  simp only [update_insertCoord]

/-- Continuity of the slot box projection of a smooth state: the box mean is a parametric integral
over the compact cube `acube ℓ`. -/
lemma continuous_boxQ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Continuous (fun x : Xn n => boxQ ℓ j Ψ x) := by
  have hupd : Continuous (fun q : Xn n × E3 => Function.update q.1 j q.2) :=
    continuous_update (A := fun _ : Fin n => E3) j
  have hjoint : Continuous (fun p : Xn n × E3 => Ψ (Function.update p.1 j p.2)) :=
    hΨ.continuous.comp hupd
  have hcont : Continuous (fun x : Xn n => ∫ y : E3 in Submission.BoseGases.acube ℓ,
      Ψ (Function.update x j y)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (x : Xn n) (y : E3) => Ψ (Function.update x j y))
      (show Continuous (fun p : Xn n × E3 => Ψ (Function.update p.1 j p.2)) from hjoint)
      (Submission.BoseGases.acube_compact hℓ)
  simp only [boxQ]
  exact hΨ.continuous.sub (continuous_const.mul hcont)

/-- The Fubini exchange of the two box integrals (over `boxL ℓ` and over the slice box
`boxPiSet ι ℓ`) for a continuous integrand. -/
theorem boxL_boxPiSet_integral_swapR {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {G : E3 → ({k : Fin n // k ≠ i} → E3) → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    (∫ w in boxL ℓ, ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, G w x')
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ i}) ℓ, ∫ w in boxL ℓ, G w x' := by
  have hmp : ((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure ({k : Fin n // k ≠ i} → E3)).restrict
          (boxPiSet ({k : Fin n // k ≠ i}) ℓ))
      = (volume : Measure (E3 × ({k : Fin n // k ≠ i} → E3))).restrict
          (boxL ℓ ×ˢ boxPiSet ({k : Fin n // k ≠ i}) ℓ) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have hInt : Integrable (Function.uncurry G)
      (((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure ({k : Fin n // k ≠ i} → E3)).restrict
          (boxPiSet ({k : Fin n // k ≠ i}) ℓ))) := by
    rw [hmp]
    exact hG.continuousOn.integrableOn_compact
      ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod (isCompact_boxPiSet hℓ))
  exact MeasureTheory.integral_integral_swap hInt

/-! ## 4. Part 2 -/

/-- **The box identity.**  The `χ_ℓ`-weighted `L²`-mass of `boxQ ℓ j Ψ` over `abox n ℓ` equals the
iterated box integral of the `mf`-form of the slot sections. -/
lemma fibre_part2 {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Xn n → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖boxQ ℓ j Ψ x‖ ^ 2)
      = ∫ x' in boxPiSet ({k : Fin n // k ≠ j}) ℓ,
          ∫ w in boxL ℓ,
            (Submission.BoseGases.chiScale ℓ w) ^ 2
              * ‖mf ℓ (sect j x' Ψ) w‖ ^ 2 := by
  have hcont : Continuous (fun x : Xn n =>
      (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖boxQ ℓ j Ψ x‖ ^ 2) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).comp
        (continuous_apply j)).pow 2).mul
      ((continuous_boxQ hℓ j hΨ).norm.pow 2)
  have hGcont : Continuous (Function.uncurry (fun (w : E3)
      (x' : {k : Fin n // k ≠ j} → E3) =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2
          * ‖boxQ ℓ j Ψ (insertCoord j w x')‖ ^ 2)) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).comp continuous_fst).pow 2).mul
      (((continuous_boxQ hℓ j hΨ).comp (continuous_insertCoord j)).norm.pow 2)
  rw [← setIntegral_insertCoord_slice hℓ j hcont]
  simp only [insertCoord_apply_self]
  rw [boxL_boxPiSet_integral_swapR hℓ j hGcont]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [insertCoord_apply_self]
  rw [boxQ_insertCoord_eq_mf_sect hℓ j Ψ w x']

theorem PB3FibreQ {n : ℕ} (j : Fin n) {Ψ Ξ : Work.BoseDict.Xn n → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ 2 (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)))
    (hΞ : MeasureTheory.MemLp Ξ 2 (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn n)))
    {w : EuclideanSpace ℝ (Fin 3) → ℂ} (hwc : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (hwb : ∃ C : ℝ, ∀ x, ‖w x‖ ≤ C) (hwcs : HasCompactSupport w) :
    (∫ x : Work.BoseDict.Xn n, (starRingEnd ℂ) (Ψ x)
        * (w (x j) * (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
            * Ξ (Function.update x j u))))
      = ∫ x' : {k : Fin n // k ≠ j} → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
              * Ψ (Work.BoseBoxFock.insertCoord j u x'))
            * (∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (w u)
                * Ξ (Work.BoseBoxFock.insertCoord j u x'))
    ∧ (∀ {ℓ : ℝ}, 0 < ℓ → ∀ {Ψ : Work.BoseDict.Xn n → ℂ}, ContDiff ℝ (⊤ : ℕ∞) Ψ →
        tsupport Ψ ⊆ Work.MB.boxPow n ℓ →
        (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖Work.BoseBoxFock.boxQ ℓ j Ψ x‖ ^ 2)
          = ∫ x' in Work.BoseBoxFock.boxPiSet ({k : Fin n // k ≠ j}) ℓ,
              ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
                (Submission.BoseGases.chiScale ℓ w) ^ 2
                  * ‖Work.BoseBoxFock.mf ℓ (Work.BoseBoxFock.sect j x' Ψ) w‖ ^ 2) := by
  refine ⟨fibre_part1 (Ψ := Ψ) (Ξ := Ξ) (w := w) j
      (PB3FibreQ_int j hΨ hΞ hwc hwb hwcs), ?_⟩
  intro ℓ hℓ Ψ' hΨ' _
  exact fibre_part2 j hℓ hΨ'

end Work.BoseBoxFock
