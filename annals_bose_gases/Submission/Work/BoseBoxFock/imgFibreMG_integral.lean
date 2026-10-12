import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
import Submission.Work.BoseBoxFock.setIntegral_insertCoord2_slice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreMG_integral`

The `u`-marginal of the `G`-density of the position-space fibre:

    ∫_{u ∈ boxL ℓ} imgFibreMG ℓ p G u = imgFibreN ℓ G .

Both sides are the `L²`-mass of `G` on the `n`-particle box: the left-hand side averages the
`p.1`-slot of the configuration over `boxL ℓ` and integrates out the remaining coordinates
(`p.2`-slot included), which is precisely the measure-preserving two-coordinate insertion
`(x', (u, v)) ↦ insertCoord2 p u v x'` of `Work.BoseBoxFock.sliceIns`.  The proof is

* the set integral over `boxPiSet` as an integral against `Measure.pi (boxMeas ℓ)`
  (`setIntegral_boxPiSet_eq`),
* one Fubini swap inside the `u`-integral (`MeasureTheory.integral_integral_swap`), for which the
  integrand is integrable because it is continuous and the measure is carried by the compact box
  (`sliceProdMeasure_fixed_fst` + `ContinuousOn.integrableOn_compact`),
* the corpus peel identity `setIntegral_insertCoord2_slice`, which is the measure-preserving
  change of variables back to `abox n ℓ`.

The three helper lemmas are the `(p.1 = u)`-frozen analogues of `sliceIns_integrable` and are
reusable for the sibling marginals (`imgFibreMF_integral`, `imgFibreDG_integral`).

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Continuity of the two-coordinate insertion with the `p.1`-slot frozen**: the map
`q ↦ insertCoord2 p u q.1 q.2` is the insertion `sliceInsFun` composed with the continuous map
`q ↦ (u, q.1, q.2)`. -/
lemma continuous_insertCoord2_frozen_fst {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (u : E3) :
    Continuous (fun q : E3 × (pairFib23 n p → E3) => insertCoord2 p u q.1 q.2) := by
  have : (fun q : E3 × (pairFib23 n p → E3) => insertCoord2 p u q.1 q.2)
      = fun q => sliceInsFun p ((u, q.1), q.2) := rfl
  rw [this]
  exact (continuous_sliceInsFun p hp).comp
    ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)

/-- **The `(p.1 = u)`-slice of the insertion measure**: the product of the box measure with the
`boxPiSet`-product measure is the Lebesgue measure restricted to the product box. -/
lemma sliceProdMeasure_frozen_fst {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) :
    (boxMeas ℓ).prod (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))
      = (volume : Measure (E3 × (pairFib23 n p → E3))).restrict
          (Work.BoseK15.corpusBox.boxL ℓ ×ˢ boxPiSet (pairFib23 n p) ℓ) := by
  have h2 : Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ)
      = (volume : Measure (pairFib23 n p → E3)).restrict (boxPiSet (pairFib23 n p) ℓ) :=
    (restrict_boxPiSet_eq).symm
  rw [h2, boxMeas, Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- **Integrability of the inserted square at a frozen `p.1`-slot**: since the slice measure is
carried by the compact product box and the integrand is continuous, the integral is finite. -/
lemma integrable_insertCoord2_frozen_fst {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {G : Submission.BoseGases.X n → ℝ} (hG : Continuous G) (u : E3) :
    Integrable (fun q : E3 × (pairFib23 n p → E3) => (G (insertCoord2 p u q.1 q.2)) ^ 2)
      ((boxMeas ℓ).prod (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) := by
  rw [sliceProdMeasure_frozen_fst p]
  exact ContinuousOn.integrableOn_compact
    ((Work.BoseK15.corpusBox.boxL_compact ℓ).prod (isCompact_boxPiSet hℓ))
    (((hG.pow 2).comp (continuous_insertCoord2_frozen_fst p hp u)).continuousOn)

/-- **Fubini in the `(x', s)`-order**: the `x'`-integration (over the remaining coordinates) may be
performed before the `s`-integration (over the box). -/
lemma integral_boxPiSet_boxL_swap {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {G : Submission.BoseGases.X n → ℝ} (hG : Continuous G) (u : E3) :
    (∫ x' : pairFib23 n p → E3,
        ∫ s : E3, (G (insertCoord2 p u s x')) ^ 2 ∂(boxMeas ℓ)
        ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ)))
      = ∫ s : E3, (∫ x' : pairFib23 n p → E3, (G (insertCoord2 p u s x')) ^ 2
          ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) ∂(boxMeas ℓ) :=
  (MeasureTheory.integral_integral_swap (integrable_insertCoord2_frozen_fst hℓ hp hG u)).symm

theorem imgFibreMG_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {G : Submission.BoseGases.X n → ℝ} (hG : Continuous G) :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.imgFibreMG ℓ p G u)
      = Work.BoseBoxFock.imgFibreN ℓ G := by
  calc (∫ u in Work.BoseK15.corpusBox.boxL ℓ, Work.BoseBoxFock.imgFibreMG ℓ p G u)
      = ∫ u : E3, (∫ x' : pairFib23 n p → E3,
            ∫ s : E3, (G (insertCoord2 p u s x')) ^ 2 ∂(boxMeas ℓ)
            ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) ∂(boxMeas ℓ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          unfold imgFibreMG
          rw [setIntegral_boxPiSet_eq]
    _ = ∫ u : E3, (∫ s : E3, (∫ x' : pairFib23 n p → E3,
            (G (insertCoord2 p u s x')) ^ 2
            ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ)))
            ∂(boxMeas ℓ)) ∂(boxMeas ℓ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          exact integral_boxPiSet_boxL_swap hℓ hp hG u
    _ = ∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in boxPiSet (pairFib23 n p) ℓ, (G (insertCoord2 p u s x')) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          exact (setIntegral_boxPiSet_eq (fun x' : pairFib23 n p → E3 =>
            (G (insertCoord2 p u s x')) ^ 2)).symm
    _ = ∫ x in Submission.BoseGases.abox n ℓ, (G x) ^ 2 :=
          setIntegral_insertCoord2_slice hℓ p hp (hG.pow 2)
    _ = Work.BoseBoxFock.imgFibreN ℓ G := rfl

end Work.BoseBoxFock
