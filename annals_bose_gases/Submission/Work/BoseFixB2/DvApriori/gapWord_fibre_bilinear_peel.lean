import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# `gapWord_fibre_bilinear_peel` — peeling the fibre slot out of the centred-box integral

For a slot `j : Fin (m+1)` and continuous `A B : X (m+1) → ℝ`,

    ∫_{abox (m+1) ℓ} ∫_{acube ℓ} A(x_{j←z}) B(x_{j←z}) dz dx = ℓ³ ∫_{abox (m+1) ℓ} A B .

The reason is that the replacement map `(x,z) ↦ x_{j←z}` only touches the slot `j`, so
Fubini over the product structure `X (m+1) ≅ ℝ³ × X m` (the measure-preserving split
`MeasurableEquiv.piFinSuccAbove` isolating the slot `j`, cf. `restrict_abox_eq_pi`)
integrates the (irrelevant) slot-`j` variable to the full volume `vol (acube ℓ) = ℓ³`.

The argument is factored as:

* `integral_update_peel_aux` — the abstract statement for an arbitrary (finite, σ-finite)
  measure `ν` on a measurable space: the double integral `∫ x, ∫ z, G (x_{j←z})` over the
  product measure `Measure.pi (fun _ => ν)` collapses to `(ν univ).toReal * ∫ G`.  The proof
  is a change of variables along the measure-preserving split `piFinSuccAbove j` together
  with two applications of Fubini (`integral_prod_symm`), the slot-`j` variable being
  integrated out as a constant;
* the specialisation to `ν = volume↾acube ℓ` and `G = A · B` on the box `abox (m+1) ℓ`,
  where `A · B` is integrable by compactness of the box
  (`abox_compact`, `ContinuousOn.integrableOn_compact`) and `(ν univ).toReal = ℓ³`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases

/-- **Peel of one slot out of a product measure.**

For a finite σ-finite measure `ν` on `β`, a slot `j : Fin (k+1)` and an integrable
`G : (Fin (k+1) → β) → ℝ`,

    ∫ x, (∫ z, G (update x j z) ∂ν) ∂(Measure.pi (fun _ => ν))
      = (ν univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ => ν)) .

The coordinate `j` of `x` does not occur in `G (update x j z)`, so it integrates to the
total mass of `ν`; the remaining integral is the full product integral. -/
theorem integral_update_peel_aux {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [SigmaFinite ν] [IsFiniteMeasure ν] {k : ℕ} (j : Fin (k + 1))
    {G : (Fin (k + 1) → β) → ℝ}
    (hG : Integrable G (Measure.pi (fun _ : Fin (k + 1) => ν))) :
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j
  have he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => β) j := rfl
  have hmp : MeasurePreserving e (Measure.pi (fun _ : Fin (k + 1) => ν))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_piFinSuccAbove (α := fun _ : Fin (k + 1) => β)
      (μ := fun _ : Fin (k + 1) => ν) j
  have hmp' : MeasurePreserving (e.symm) (ν.prod (Measure.pi (fun _ : Fin k => ν)))
      (Measure.pi (fun _ : Fin (k + 1) => ν)) := MeasurePreserving.symm e hmp
  have hemb : MeasurableEmbedding (e.symm) := MeasurableEquiv.measurableEmbedding e.symm
  have hK : Integrable (fun p : β × (Fin k → β) => G (e.symm p))
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
    (hmp'.integrable_comp_emb hemb (g := G)).mpr hG
  have hE : ((e.symm : β × (Fin k → β) → (Fin (k + 1) → β)))
      = fun f => Fin.insertNth j f.1 f.2 := by
    rw [he]
    funext f mm
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hpoint : ∀ (p : β × (Fin k → β)) (z : β),
      Function.update (e.symm p) j z = e.symm (z, p.2) := by
    rintro ⟨a, y⟩ z
    rw [hE]
    exact Fin.update_insertNth (α := fun _ : Fin (k + 1) => β) j a z y
  have h1 : (∫ x, (∫ z, G (Function.update x j z) ∂ν)
        ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
      = ∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    have h := hmp'.integral_comp hemb (fun x => ∫ z, G (Function.update x j z) ∂ν)
    rw [← h]
    simp only [hpoint]
  have hKw : Integrable (fun w : Fin k → β => ∫ z, G (e.symm (z, w)) ∂ν)
      (Measure.pi (fun _ : Fin k => ν)) := hK.integral_prod_right
  have hT : Integrable (fun p : β × (Fin k → β) => ∫ z, G (e.symm (z, p.2)) ∂ν)
      (ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    simpa using hKw.comp_snd ν
  have h2 : (∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))))
      = (ν Set.univ).toReal * ∫ p : β × (Fin k → β), G (e.symm p)
        ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := by
    rw [integral_prod_symm _ hT]
    have hc : ∀ w : Fin k → β, (∫ _a : β, (∫ z, G (e.symm (z, w)) ∂ν) ∂ν)
        = (ν Set.univ).toReal * (∫ z, G (e.symm (z, w)) ∂ν) := by
      intro w
      rw [integral_const, Measure.real_def]
      rfl
    simp only [hc]
    rw [integral_const_mul, ← integral_prod_symm _ hK]
  calc
    (∫ x, (∫ z, G (Function.update x j z) ∂ν) ∂(Measure.pi (fun _ : Fin (k + 1) => ν)))
        = ∫ p : β × (Fin k → β), (∫ z, G (e.symm (z, p.2)) ∂ν)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h1
    _ = (ν Set.univ).toReal * ∫ p : β × (Fin k → β), G (e.symm p)
            ∂(ν.prod (Measure.pi (fun _ : Fin k => ν))) := h2
    _ = (ν Set.univ).toReal * ∫ y, G y ∂(Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [hmp'.integral_comp hemb G]

theorem gapWord_fibre_bilinear_peel {ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ} (j : Fin (m + 1))
    {A B : Submission.BoseGases.X (m + 1) → ℝ} (hAc : Continuous A) (hBc : Continuous B) (c : ℝ) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        c * ∫ z in Submission.BoseGases.acube ℓ,
          A (Function.update x j z) * B (Function.update x j z))
      = c * ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, A x * B x := by
  have hfin : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top⟩
  haveI := hfin
  have hG : Integrable (fun y : Submission.BoseGases.X (m + 1) => A y * B y)
      (Measure.pi (fun _ : Fin (m + 1) =>
        (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) := by
    rw [← Submission.BoseGases.restrict_abox_eq_pi (m + 1) ℓ]
    exact ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 1) hℓ)
      (hAc.mul hBc).continuousOn
  have hpeel := integral_update_peel_aux
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) j
    (G := fun y : Submission.BoseGases.X (m + 1) => A y * B y) hG
  simp only [] at hpeel
  rw [Submission.BoseGases.restrict_abox_eq_pi]
  rw [integral_const_mul]
  rw [hpeel]
  have hvol : (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ)) Set.univ).toReal = ℓ ^ 3 := by
    rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol]
  ring

end Work.BoseFixB2.DvApriori
