import Mathlib

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory MeasureTheory.Measure

set_option backward.isDefEq.respectTransparency false

/-- Fubini's theorem for `ENNReal`-valued functions on a finite product of measure spaces:
the integral of a product of functions of one variable each is the product of the integrals. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ENNReal) (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
      have hg : AEMeasurable (fun y : (j : Fin n) → E (Fin.succAbove 0 j) =>
          ∏ j, f (Fin.succAbove 0 j) (y j)) (Measure.pi fun j => μ (Fin.succAbove 0 j)) := by
        simpa only [Function.comp_apply] using
          (Finset.aemeasurable_fun_prod Finset.univ (fun j _ =>
            (hf (Fin.succAbove 0 j)).comp_quasiMeasurePreserving
              (quasiMeasurePreserving_eval (fun j => μ (Fin.succAbove 0 j)) j)))
      rw [← (measurePreserving_piFinSuccAbove μ 0).symm |>.lintegral_comp_emb
            (MeasurableEquiv.piFinSuccAbove E 0).symm.measurableEmbedding (fun x => ∏ i, f i (x i))]
      have hcongr : (∫⁻ a : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm a i)
            ∂(μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) =
          ∫⁻ a : E 0 × ((j : Fin n) → E (Fin.succAbove 0 j)),
            f 0 a.1 * ∏ j, f (Fin.succAbove 0 j) (a.2 j)
            ∂(μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j)) :=
        lintegral_congr (fun a => by
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ,
            Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq,
            Fin.cons_zero])
      rw [hcongr]
      rw [lintegral_prod_mul (hf 0) hg]
      rw [ih (fun j => f (Fin.succAbove 0 j)) (fun j => hf (Fin.succAbove 0 j))]
      rw [Fin.prod_univ_succ]
      congr 1

theorem piFubini {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, MeasureTheory.Measure (α i)) [∀ i, MeasureTheory.SigmaFinite (μ i)]
    (f : ∀ i, α i → ENNReal) (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : (∀ i, α i), ∏ i, f i (x i) ∂(MeasureTheory.Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := measurePreserving_piCongrLeft (α := α) μ e
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.piCongrLeft α e).measurableEmbedding
        (fun x => ∏ i, f i (x i))]
  have hcongr : (∫⁻ a : (k : Fin (Fintype.card ι)) → α (e k),
        ∏ i, f i ((MeasurableEquiv.piCongrLeft α e) a i) ∂(Measure.pi fun k => μ (e k))) =
      ∫⁻ a : (k : Fin (Fintype.card ι)) → α (e k),
        ∏ k, f (e k) (a k) ∂(Measure.pi fun k => μ (e k)) := by
    apply lintegral_congr
    intro a
    rw [← Equiv.prod_comp e (fun i => f i ((MeasurableEquiv.piCongrLeft α e) a i))]
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [hcongr]
  rw [lintegral_fin_nat_prod_eq_prod (E := fun k => α (e k)) (μ := fun k => μ (e k))
        (f := fun k => f (e k)) (fun k => hf (e k))]
  exact Equiv.prod_comp e (fun i => ∫⁻ x, f i x ∂μ i)

end Work.BW
