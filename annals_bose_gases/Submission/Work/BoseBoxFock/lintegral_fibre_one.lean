import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_fibre_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

local notation "𝔼" => EuclideanSpace ℝ (Fin 3)

/-! ## Splitting off one coordinate, `lintegral` form

The measure-preserving equivalence `peelEquiv` splits `ι → 𝔼` into
`𝔼 × ({k : ι // k ≠ a} → 𝔼)` by the coordinate `a`.  Its inverse is exactly `fibreIns a`, so the
`lintegral` version of the Fubini splitting follows from Tonelli for the product measure.

The three structural lemmas below are the same ones used by `integral_fibre_one`
(`Submission.Work.BoseBoxFock.integral_fibre_two`), repeated here because they are `private`
there; the Fubini step is the only new content. -/

/-- Splitting off the coordinate `a` as a factor `𝔼`. -/
private def peelEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] (a : ι) :
    (ι → 𝔼) ≃ᵐ 𝔼 × ({k : ι // k ≠ a} → 𝔼) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)).trans
    ((MeasurableEquiv.funUnique {k : ι // k = a} 𝔼).prodCongr (MeasurableEquiv.refl _))

private theorem peelEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (x : ι → 𝔼) :
    peelEquiv ι a x = (x a, fun k : {k : ι // k ≠ a} => x k.1) := by
  simp only [peelEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.funUnique]
  rfl

private theorem peelEquiv_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (p : 𝔼 × ({k : ι // k ≠ a} → 𝔼)) :
    (peelEquiv ι a).symm p = fibreIns a p.1 p.2 := by
  refine (Equiv.symm_apply_eq (peelEquiv ι a).toEquiv).mpr ?_
  change p = peelEquiv ι a (fibreIns a p.1 p.2)
  rw [peelEquiv_apply]
  refine Prod.ext ?_ ?_
  · simp only [fibreIns]
    rw [dif_pos trivial]
  · funext k
    simp only [fibreIns]
    rw [dif_neg k.2]

private theorem peelEquiv_fun_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    ⇑(peelEquiv ι a) = fun x : ι → 𝔼 =>
      Prod.map (⇑(MeasurableEquiv.funUnique {k : ι // k = a} 𝔼)) id
        (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)) x) := by
  funext x
  rw [peelEquiv_apply, MeasurableEquiv.piEquivPiSubtypeProd_apply, Prod.map_apply,
    MeasurableEquiv.funUnique_apply]
  rfl

private theorem measurePreserving_peelEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    MeasurePreserving (peelEquiv ι a) (volume : Measure (ι → 𝔼))
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))) := by
  letI : Unique {k : ι // k = a} := uniqueOfSubsingleton ⟨a, rfl⟩
  letI : Fintype {k : ι // k = a} := Subtype.fintype (fun k : ι => k = a)
  have h₁ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => 𝔼) (fun k : ι => k = a)
  have h₂ := volume_preserving_piUnique (fun _ : {k : ι // k = a} => 𝔼)
  have h₃ := h₂.prod (MeasurePreserving.id (volume : Measure ({k : ι // ¬(k = a)} → 𝔼)))
  refine (h₃.comp h₁).congr (peelEquiv ι a).measurable ?_
  filter_upwards with x
  exact congrFun (peelEquiv_fun_eq (ι := ι) a) x

/-- The one-coordinate fibre splitting, `lintegral` (Tonelli) form. -/
theorem lintegral_fibre_one {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) {F : (ι → EuclideanSpace ℝ (Fin 3)) → ENNReal} (hF : AEMeasurable F) : ∫⁻ x : ι → EuclideanSpace ℝ (Fin 3), F x = ∫⁻ w : EuclideanSpace ℝ (Fin 3), ∫⁻ y : {k : ι // k ≠ a} → EuclideanSpace ℝ (Fin 3), F (fibreIns a w y) := by
  have hmp := measurePreserving_peelEquiv (ι := ι) a
  have hsymm := MeasurePreserving.symm (peelEquiv ι a) hmp
  -- transport the integral along the measure preserving equivalence `peelEquiv`
  have hstep : (∫⁻ p : 𝔼 × ({k : ι // k ≠ a} → 𝔼), F ((peelEquiv ι a).symm p))
      = ∫⁻ x : ι → 𝔼, F x :=
    hsymm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F
  rw [← hstep]
  -- Tonelli for the product measure
  have hmap : Measure.map (⇑(peelEquiv ι a).symm)
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼))) = (volume : Measure (ι → 𝔼)) :=
    hsymm.map_eq
  have hF' : AEMeasurable F (Measure.map (⇑(peelEquiv ι a).symm)
      (volume : Measure (𝔼 × ({k : ι // k ≠ a} → 𝔼)))) := by
    rw [hmap]
    exact hF
  have hae : AEMeasurable (fun p : 𝔼 × ({k : ι // k ≠ a} → 𝔼) => F ((peelEquiv ι a).symm p))
      ((volume : Measure 𝔼).prod (volume : Measure ({k : ι // k ≠ a} → 𝔼))) :=
    hF'.comp_measurable (MeasurableEquiv.measurable _)
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [lintegral_prod (f := fun p : 𝔼 × ({k : ι // k ≠ a} → 𝔼) => F ((peelEquiv ι a).symm p)) hae]
  -- identify the inverse of the peel with the coordinate insertion
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact congrArg F (peelEquiv_symm_apply a (w, y))

end Work.BoseBoxFock
