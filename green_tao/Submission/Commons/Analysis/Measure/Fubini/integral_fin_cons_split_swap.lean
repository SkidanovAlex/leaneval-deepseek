import Mathlib
import Submission.Commons.Analysis.Measure.Fubini.integral_fin_cons_split
import Submission.Commons.Analysis.Measure.Fubini.integral_prod_four_left_assoc

/-!
# Splitting an iterated integral over `Fin (n+1) → ℝ`, with the head integrals outside

This file proves `Commons.Analysis.Measure.Fubini.integral_fin_cons_split_swap`: for a function `Φ`
on pairs of points of `Fin (n+1) → ℝ` which is integrable for the product of Lebesgue measures,
the iterated integral `∫ t, ∫ t', Φ t t'` can be computed by splitting each variable as
`t = Fin.cons s w` with `s : ℝ` and `w : Fin n → ℝ`, and by performing the four resulting
one-dimensional integrals in the order `w, w', s, s'`.

The proof combines
* Mathlib's Fubini theorem `MeasureTheory.integral_prod`;
* the commons lemma `Commons.Analysis.Measure.Fubini.integral_fin_cons_split`, which
  provides the measure-preserving equivalences `finConsMeasurableEquiv`,
  `measurePreserving_prodCongr` and the middle swap `midSwap` realising the splitting
  `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)`, `t ↦ (t 0, Fin.tail t)`;
* the commons lemma `Commons.Analysis.Measure.Fubini.integral_prod_four_left_assoc`,
  a Fubini theorem for a left-associated four-fold product of measures.
-/


open MeasureTheory MeasureTheory.Measure

namespace Commons.Analysis.Measure.Fubini

private noncomputable def psiME (n : ℕ) :
    (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ ≃ᵐ
      ((ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ))) :=
  ((MeasurableEquiv.prodAssoc).trans (MeasurableEquiv.prodComm)).trans (midSwap n)

private lemma psiME_apply (n : ℕ) (w w' : Fin n → ℝ) (s s' : ℝ) :
    psiME n (((w, w'), s), s') = ((s, w), (s', w')) := by
  have h1 : (MeasurableEquiv.prodAssoc (((w, w'), s), s')) = ((w, w'), (s, s')) := rfl
  have h2 : (MeasurableEquiv.prodComm ((w, w'), (s, s'))) = ((s, s'), (w, w')) := rfl
  rw [psiME, MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply, h1, h2, midSwap_apply]

private lemma psiME_measurePreserving (n : ℕ) :
    MeasurePreserving (psiME n)
      ((((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).prod
        (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).prod
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc :
        (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ ≃ᵐ
          ((Fin n → ℝ) × (Fin n → ℝ)) × (ℝ × ℝ))
      ((((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).prod
        (volume : Measure ℝ)).prod (volume : Measure ℝ))
      (((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) :=
    measurePreserving_prodAssoc ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure ℝ) (volume : Measure ℝ)
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm :
        ((Fin n → ℝ) × (Fin n → ℝ)) × (ℝ × ℝ) ≃ᵐ
          (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ)))
      (((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))) :=
    measurePreserving_swap
  have h3 : MeasurePreserving (midSwap n)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))))
      (((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).prod
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))) :=
    midSwap_measurePreserving n
  exact (h1.trans h2).trans h3

theorem integral_fin_cons_split_swap {n : ℕ}
    (Φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℂ)
    (hΦ : MeasureTheory.Integrable (Function.uncurry Φ)
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Fin (n + 1) → ℝ)))) :
    ∫ t : Fin (n + 1) → ℝ, ∫ t' : Fin (n + 1) → ℝ, Φ t t'
      = ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, ∫ s : ℝ, ∫ s' : ℝ,
          Φ (Fin.cons s w) (Fin.cons s' w') := by
  have he : MeasurePreserving (finConsMeasurableEquiv n)
      (volume : Measure (ℝ × (Fin n → ℝ))) (volume : Measure (Fin (n+1) → ℝ)) :=
    finConsMeasurableEquiv_measurePreserving n
  have hF_mp : MeasurePreserving
      ((finConsMeasurableEquiv n).prodCongr (finConsMeasurableEquiv n))
      (volume : Measure ((ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ))))
      (volume : Measure ((Fin (n+1) → ℝ) × (Fin (n+1) → ℝ))) :=
    measurePreserving_prodCongr he he
  have step0 : (∫ t : Fin (n+1) → ℝ, ∫ t' : Fin (n+1) → ℝ, Φ t t')
      = ∫ z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ), Φ z.1 z.2 :=
    integral_integral hΦ
  have step1 : (∫ z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ), Φ z.1 z.2)
      = ∫ a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
          Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2) := by
    have h := (hF_mp.integral_comp'
      (fun z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ) => Φ z.1 z.2)).symm
    have h2 : (∫ a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
          (fun z : (Fin (n+1) → ℝ) × (Fin (n+1) → ℝ) => Φ z.1 z.2)
            ((finConsMeasurableEquiv n).prodCongr (finConsMeasurableEquiv n) a))
        = ∫ a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
            Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2) := by
      apply integral_congr_ae
      filter_upwards with a
      obtain ⟨⟨s, w⟩, ⟨s', w'⟩⟩ := a
      simp
    exact h.trans h2
  have hG : Integrable (fun a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)) =>
        Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2))
      (volume : Measure ((ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)))) := by
    have h := (hF_mp.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding
        ((finConsMeasurableEquiv n).prodCongr (finConsMeasurableEquiv n)))).mpr hΦ
    refine h.congr ?_
    filter_upwards with a
    obtain ⟨⟨s, w⟩, ⟨s', w'⟩⟩ := a
    simp [Function.uncurry]
  have hψ_mp : MeasurePreserving (psiME n)
      (volume : Measure ((((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ))
      (volume : Measure ((ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)))) :=
    psiME_measurePreserving n
  have step3 : (∫ a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)),
          Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2))
      = ∫ y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ,
          Φ (Fin.cons y.1.2 y.1.1.1) (Fin.cons y.2 y.1.1.2) := by
    have h := (hψ_mp.integral_comp'
      (fun a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)) =>
        Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2))).symm
    have h2 : (∫ y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ,
          (fun a : (ℝ × (Fin n → ℝ)) × (ℝ × (Fin n → ℝ)) =>
            Φ (Fin.cons a.1.1 a.1.2) (Fin.cons a.2.1 a.2.2)) (psiME n y))
        = ∫ y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ,
            Φ (Fin.cons y.1.2 y.1.1.1) (Fin.cons y.2 y.1.1.2) := by
      apply integral_congr_ae
      filter_upwards with y
      obtain ⟨⟨⟨w, w'⟩, s⟩, s'⟩ := y
      rw [psiME_apply]
    exact h.trans h2
  have hFint : Integrable
      (fun y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ =>
        Φ (Fin.cons y.1.2 y.1.1.1) (Fin.cons y.2 y.1.1.2))
      (volume : Measure ((((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ)) := by
    have h := (hψ_mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding (psiME n))).mpr hG
    refine h.congr ?_
    filter_upwards with y
    obtain ⟨⟨⟨w, w'⟩, s⟩, s'⟩ := y
    simp [psiME_apply]
  have step5 : (∫ y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ,
          Φ (Fin.cons y.1.2 y.1.1.1) (Fin.cons y.2 y.1.1.2))
      = ∫ w : Fin n → ℝ, ∫ w' : Fin n → ℝ, ∫ s : ℝ, ∫ s' : ℝ,
          Φ (Fin.cons s w) (Fin.cons s' w') :=
    integral_prod_four_left_assoc (volume : Measure (Fin n → ℝ)) (volume : Measure (Fin n → ℝ))
      (volume : Measure ℝ) (volume : Measure ℝ)
      (fun y : (((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ =>
        Φ (Fin.cons y.1.2 y.1.1.1) (Fin.cons y.2 y.1.1.2)) hFint
  exact step0.trans (step1.trans (step3.trans step5))

end Commons.Analysis.Measure.Fubini
