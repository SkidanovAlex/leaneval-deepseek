import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibre2Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2_mf_integral` — the `u`-marginal of the mirror fibre

The mean-field density attached to the *mirror* position-space fibre `imgFibre₂` (the one that
averages the slot `p.2`) is, at fixed `u`,

    ∫_{x' ∈ boxPiSet (pairFib2 n p) ℓ} ∫_{s ∈ boxL ℓ} (F (insertCoord2 p u s x'))² .

This module proves that its `u`-marginal is the full box `L²`-mass of `F`:

    ∫_{u ∈ boxL ℓ} ∫_{x'} ∫_{s} (F (insertCoord2 p u s x'))² = imgFibreN ℓ F
      = ∫_{abox n ℓ} (F x)² .

**Proof.**  The two-coordinate insertion `(y, s, x') ↦ insertCoord2 p y s x'` is a
measure-preserving bijection of the triple box `boxL ℓ × boxL ℓ × boxPiSet (pairFib2 n p) ℓ`
onto `abox n ℓ` (the corpus's `setIntegral_insertCoord2_slice`, via `sliceIns`), so the only
content of the statement is that the *iterated order* of the three integrals is the one in which
the insertion lemma is stated: `(u, x', s) ↦ (u, s, x')`.

That permutation is performed here with two foundational tools:

* the set integral over the product box `boxPiSet` is the integral against the product measure
  `Measure.pi (fun _ => boxMeas ℓ)` (`setIntegral_boxPiSet_eq`), and
* the `(x', s)`-double integral satisfies Fubini (`MeasureTheory.integral_integral_swap`); the
  joint integrand is continuous and the product measure
  `(Measure.pi (fun _ => boxMeas ℓ)).prod (boxMeas ℓ)` is the restriction of Lebesgue measure to
  the product of the two compact boxes (`restrict_boxPiSet_eq` + `Measure.prod_restrict`), whence
  integrability by `ContinuousOn.integrableOn_compact`.

Nothing here needs the smoothing of `F`: continuity is enough.

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The Fubini swap of the `(x', s)`-integration -/

/-- **Integrability of the swapped integrand.**  For a continuous `F`, the function
`q ↦ (F (insertCoord2 p u q.2 q.1))²` on `(pairFib2 n p → E3) × E3` is integrable against the
product of the box measures: that product is the restriction of Lebesgue measure to the product of
the compact boxes `boxPiSet (pairFib2 n p) ℓ` and `boxL ℓ`, on which the (continuous) integrand is
bounded. -/
lemma integrable_insertCoord2_swap {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F : Xn n → ℝ} (hF : Continuous F) (u : E3) :
    Integrable (fun q : (pairFib2 n p → E3) × E3 => (F (insertCoord2 p u q.2 q.1)) ^ 2)
      ((Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ)).prod (boxMeas ℓ)) := by
  have hcont : Continuous (fun q : (pairFib2 n p → E3) × E3 => insertCoord2 p u q.2 q.1) := by
    have h : (fun q : (pairFib2 n p → E3) × E3 => insertCoord2 p u q.2 q.1)
        = fun q => sliceInsFun p ((u, q.2), q.1) := rfl
    rw [h]
    exact (continuous_sliceInsFun p hp).comp
      ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
  rw [show (Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ)).prod (boxMeas ℓ)
      = (volume : Measure ((pairFib2 n p → E3) × E3)).restrict
          (boxPiSet (pairFib2 n p) ℓ ×ˢ boxL ℓ) from by
    rw [← restrict_boxPiSet_eq (ι := pairFib2 n p), Measure.prod_restrict,
      Measure.volume_eq_prod]]
  exact ContinuousOn.integrableOn_compact
    ((isCompact_boxPiSet (ι := pairFib2 n p) hℓ).prod (Work.BoseK15.corpusBox.boxL_compact ℓ))
    (((hF.comp hcont).pow 2).continuousOn)

/-- **Fubini in the `(x', s)`-order**: the integration over the remaining coordinates may be
performed before the integration over the averaged box. -/
lemma integral_boxPiSet_boxL_swap2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F : Xn n → ℝ} (hF : Continuous F) (u : E3) :
    (∫ x' : pairFib2 n p → E3, (∫ s : E3, (F (insertCoord2 p u s x')) ^ 2 ∂(boxMeas ℓ))
        ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ)))
      = ∫ s : E3, (∫ x' : pairFib2 n p → E3, (F (insertCoord2 p u s x')) ^ 2
          ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ))) ∂(boxMeas ℓ) :=
  MeasureTheory.integral_integral_swap (integrable_insertCoord2_swap hℓ hp hF u)

/-! ## 2. The marginal identity -/

/-- **The `u`-marginal of the mirror mean-field fibre is the box `L²`-mass.**  The three
integrations (`u` over the box, `x'` over the remaining coordinates, `s` over the box) are
reordered to the shape of the corpus's measure-preserving insertion identity
`setIntegral_insertCoord2_slice`. -/
theorem imgFibre2_mf_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {F : Submission.BoseGases.X n → ℝ} (hF : Continuous F) :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ,
      ∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
        ∫ s in Work.BoseK15.corpusBox.boxL ℓ,
          (F (Work.BoseBoxFock.insertCoord2 p u s x')) ^ 2)
      = Work.BoseBoxFock.imgFibreN ℓ F := by
  have hf : Continuous fun x : Xn n => (F x) ^ 2 := hF.pow 2
  calc (∫ u in boxL ℓ,
        ∫ x' in boxPiSet (pairFib2 n p) ℓ, ∫ s in boxL ℓ, (F (insertCoord2 p u s x')) ^ 2)
      = ∫ u : E3, (∫ x' : pairFib2 n p → E3,
            (∫ s : E3, (F (insertCoord2 p u s x')) ^ 2 ∂(boxMeas ℓ))
            ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ))) ∂(boxMeas ℓ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          beta_reduce
          rw [setIntegral_boxPiSet_eq]
    _ = ∫ u : E3, (∫ s : E3, (∫ x' : pairFib2 n p → E3,
            (F (insertCoord2 p u s x')) ^ 2
            ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ))) ∂(boxMeas ℓ)) ∂(boxMeas ℓ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          beta_reduce
          exact integral_boxPiSet_boxL_swap2 hℓ hp hF u
    _ = ∫ u in boxL ℓ, ∫ s in boxL ℓ,
          ∫ x' in boxPiSet (pairFib2 n p) ℓ, (F (insertCoord2 p u s x')) ^ 2 := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          beta_reduce
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          beta_reduce
          exact (setIntegral_boxPiSet_eq (fun x' : pairFib2 n p → E3 =>
            (F (insertCoord2 p u s x')) ^ 2)).symm
    _ = ∫ x in Submission.BoseGases.abox n ℓ, (F x) ^ 2 :=
          setIntegral_insertCoord2_slice hℓ p hp hf
    _ = imgFibreN ℓ F := rfl

end Work.BoseBoxFock
