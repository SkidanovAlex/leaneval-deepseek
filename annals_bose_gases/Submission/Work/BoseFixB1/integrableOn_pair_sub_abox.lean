import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrableOn_pair_sub_abox`

For `f ∈ L¹(ℝ³)` and distinct slots `i ≠ j : Fin N`, the pair integrand
`x ↦ f (xᵢ − xⱼ)` is integrable over the *centred* `N`-particle box `abox N ℓ`
(`0 < ℓ`).

Route (all supporting machinery is already in the corpus, `Submission/WordInteg.lean`):

* replace `f` by its measurable representative `w := AEMeasurable.mk f hf.aemeasurable`,
  which is integrable (`Integrable.congr`) and agrees with `f` a.e.;
* `Submission.BoseGases.integrableOn_abs_sub_abox` gives `|w (xᵢ − xⱼ)|` integrable on
  the centred box;
* `Integrable.mono'` removes the absolute values (we have the a.e.-strong measurability
  of `x ↦ w (xᵢ − xⱼ)` from measurability of `w` and continuity of `x ↦ xᵢ − xⱼ`);
* `Integrable.congr` transfers back along the a.e.-equality of `f` and `w` composed with
  `x ↦ xᵢ − xⱼ`; the subtraction profile of a null set is null inside the box
  (`abox_null_preimage_pair`), which is the auxiliary lemma proved below.
-/

namespace Work.BoseFixB1

open MeasureTheory

/-- If `v =ᵐ w` on `ℝ³`, then `x ↦ v (xᵢ − xⱼ)` and `x ↦ w (xᵢ − xⱼ)` agree a.e. on the
centred `N`-particle box `abox N ℓ`: the subtraction profile of a null set is null there
(`abox_null_preimage_pair`). -/
private lemma abox_ae_pair_of_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v w : ℝ³ → ℝ}
    (hvw : v =ᵐ[volume] w) (i j : Fin N) (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X N => v (x i - x j))
      =ᵐ[volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N => w (x i - x j)) := by
  have hN : volume {y : ℝ³ | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure ℝ³)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ) {x : Submission.BoseGases.X N | x i - x j ∈ t} = 0 :=
    Submission.BoseGases.abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume : Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N ℓ)
      {x : Submission.BoseGases.X N | v (x i - x j) ≠ w (x i - x j)} = 0 :=
    measure_mono_null (fun x hx => hNt hx) hpre
  rw [show ((fun x : Submission.BoseGases.X N => v (x i - x j))
        =ᵐ[volume.restrict (Submission.BoseGases.abox N ℓ)]
        (fun x : Submission.BoseGases.X N => w (x i - x j)))
      ↔ {x : Submission.BoseGases.X N | v (x i - x j) = w (x i - x j)}
          ∈ ae (volume.restrict (Submission.BoseGases.abox N ℓ)) from Iff.rfl]
  rw [mem_ae_iff,
    show ({x : Submission.BoseGases.X N | v (x i - x j) = w (x i - x j)})ᶜ
      = {x : Submission.BoseGases.X N | v (x i - x j) ≠ w (x i - x j)} by
        ext x; simp]
  exact hfail

theorem integrableOn_pair_sub_abox {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    {i j : Fin N} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => f (x i - x j))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  let w : ℝ³ → ℝ := AEMeasurable.mk f hf.aemeasurable
  have hwm : Measurable w := AEMeasurable.measurable_mk hf.aemeasurable
  have hwae : f =ᵐ[volume] w := AEMeasurable.ae_eq_mk hf.aemeasurable
  have hwInt : MeasureTheory.Integrable w := hf.congr hwae
  have hwa : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X N => |w (x i - x j)|)
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.integrableOn_abs_sub_abox hℓ hwInt i j hij
  have hwaesm : AEStronglyMeasurable (fun x : Submission.BoseGases.X N => w (x i - x j))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    (hwm.comp (by fun_prop :
      Measurable fun x : Submission.BoseGases.X N => x i - x j)).aestronglyMeasurable
  have hwsub : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => w (x i - x j))
      (volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    refine hwa.mono' hwaesm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
  have hae := abox_ae_pair_of_ae hℓ hwae i j hij
  exact hwsub.congr hae.symm

end Work.BoseFixB1
