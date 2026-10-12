import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.CentreBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ESYRound5/Energy/pairSplit.lean`

The **two-slot splitting of the box measure**.  If `a ≠ b` are two particle
labels in `Fin (M+2)`, the box measure `Measure.pi (fun _ => ν)` on
`Fin (M+2) → α` splits as the product of the two singled-out slots (with `a`
written as the first and `b = a.succAbove b'` as the second) and the remaining
`M` slots:

    `Measure.pi ν  ≃  (ν × ν) × Measure.pi ν`.

`pairSplitEquiv` is the underlying measurable equivalence and
`measurePreserving_pairSplitEquiv` the measure identity.  On top of it we record
the two integration facts used by the two-body weighted mode expansion:

* `integrable_comp_pair_coord` : the pullback of an integrable function of two
  slots is integrable over the product space (this is the two-slot analogue of
  the one-slot `integrable_comp_eval`);
* `integrableOn_abox_comp_pair_coord` : its box form, the two-body analogue of
  the one-body pullback used in the evaluation of the one-body word.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.ESYRound5.Energy

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The action of a product of measurable equivalences on a pair. -/
theorem prodCongr_apply {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (ab : α ≃ᵐ β) (cd : γ ≃ᵐ δ) (p : α × γ) :
    (ab.prodCongr cd) p = (ab p.1, cd p.2) := rfl

/-- **The two-slot splitting equivalence.**  For `a : Fin (M+2)` and
`b' : Fin (M+1)` it reads a configuration as the pair of the coordinates `a` and
`a.succAbove b'` together with the remaining `M` coordinates. -/
noncomputable def pairSplitEquiv (α : Type*) [MeasurableSpace α] (M : ℕ)
    (a : Fin (M+2)) (b' : Fin (M+1)) :
    (Fin (M+2) → α) ≃ᵐ (α × α) × (Fin M → α) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+2) => α) a).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => α) b'))).trans
    (MeasurableEquiv.prodAssoc.symm)

/-- The value of the splitting equivalence on a configuration. -/
theorem pairSplitEquiv_apply {M : ℕ} (α : Type*) [MeasurableSpace α] (a : Fin (M+2))
    (b' : Fin (M+1)) (x : Fin (M+2) → α) :
    pairSplitEquiv α M a b' x
      = ((x a, x (a.succAbove b')), fun k => x (a.succAbove (b'.succAbove k))) := by
  rw [pairSplitEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply, prodCongr_apply]
  rw [show (⇑(MeasurableEquiv.prodAssoc.symm) :
      α × (α × (Fin M → α)) → (α × α) × (Fin M → α)) = fun p => ((p.1, p.2.1), p.2.2) from rfl]
  refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> rfl

/-- **The splitting equivalence is measure preserving**: the box measure splits
as the product of the two singled-out slots and the remaining ones. -/
theorem measurePreserving_pairSplitEquiv {M : ℕ} {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] (a : Fin (M+2)) (b' : Fin (M+1)) :
    MeasurePreserving (pairSplitEquiv α M a b') (Measure.pi (fun _ : Fin (M+2) => ν))
      ((ν.prod ν).prod (Measure.pi (fun _ : Fin M => ν))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+2) => α) a)
      (Measure.pi (fun _ : Fin (M+2) => ν))
      (ν.prod (Measure.pi (fun _ : Fin (M+1) => ν))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M+2) => ν) a
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => α) b')
      (Measure.pi (fun _ : Fin (M+1) => ν)) (ν.prod (Measure.pi (fun _ : Fin M => ν))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => ν) b'
  have h3 : MeasurePreserving ((MeasurableEquiv.refl α).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => α) b'))
      (ν.prod (Measure.pi (fun _ : Fin (M+1) => ν)))
      (ν.prod (ν.prod (Measure.pi (fun _ : Fin M => ν)))) :=
    MeasurePreserving.prod (MeasurePreserving.id ν) h2
  have h4 : MeasurePreserving (MeasurableEquiv.prodAssoc.symm :
      α × (α × (Fin M → α)) ≃ᵐ (α × α) × (Fin M → α))
      (ν.prod (ν.prod (Measure.pi (fun _ : Fin M => ν))))
      ((ν.prod ν).prod (Measure.pi (fun _ : Fin M => ν))) :=
    (MeasureTheory.measurePreserving_prodAssoc ν ν (Measure.pi (fun _ : Fin M => ν))).symm
  exact h4.comp (h3.comp h1)

/-- **Two-slot pullback integrability.**  A function of the two slots `a`,
`a.succAbove b'` which is integrable for the product measure `ν × ν` is
integrable over the product space (the two-slot analogue of
`MeasureTheory.integrable_comp_eval`). -/
theorem integrable_comp_pair_coord {M : ℕ} {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsFiniteMeasure ν] (a : Fin (M+2)) (b' : Fin (M+1)) {F : α → α → ℝ}
    (hF : Integrable (fun z : α × α => F z.1 z.2) (ν.prod ν)) :
    Integrable (fun x : Fin (M+2) → α => F (x a) (x (a.succAbove b')))
      (Measure.pi (fun _ : Fin (M+2) => ν)) := by
  have h1 : Integrable (fun p : (α × α) × (Fin M → α) => F p.1.1 p.1.2)
      ((ν.prod ν).prod (Measure.pi (fun _ : Fin M => ν))) :=
    Integrable.comp_fst hF (Measure.pi (fun _ : Fin M => ν))
  have h2 := ((measurePreserving_pairSplitEquiv ν a b').integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding (pairSplitEquiv α M a b'))).mpr h1
  refine Integrable.congr h2 (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, pairSplitEquiv_apply]

/-- **Two-slot pullback integrability over the box.**  The box form of
`integrable_comp_pair_coord`, with the cube measure `volume ↾ acube ℓ`: a function
of the two slots which is integrable on the square of cubes is integrable over
the `N`-particle box. -/
theorem integrableOn_abox_comp_pair_coord {M : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (a : Fin (M+2))
    (b' : Fin (M+1)) {W : ℝ³ → ℝ³ → ℝ}
    (hW : IntegrableOn (fun z : ℝ³ × ℝ³ => W z.1 z.2) (acube ℓ ×ˢ acube ℓ)) :
    IntegrableOn (fun x : X (M+2) => W (x a) (x (a.succAbove b'))) (abox (M+2) ℓ) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ⟩
  have hpair : Integrable (fun z : ℝ³ × ℝ³ => W z.1 z.2)
      (((volume : Measure ℝ³).restrict (acube ℓ)).prod
        ((volume : Measure ℝ³).restrict (acube ℓ))) := by
    rw [IntegrableOn] at hW
    rw [Measure.prod_restrict]
    exact hW
  have hpi := integrable_comp_pair_coord ((volume : Measure ℝ³).restrict (acube ℓ)) a b' hpair
  rw [IntegrableOn, restrict_abox_eq_pi (M+2) ℓ]
  exact hpi

end Work.ESYRound5.Energy
