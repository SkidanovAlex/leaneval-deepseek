import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of the pullback along the pair-evaluation map `x ↦ (x i, x j)`

On the `n`-particle centred box `abox n ℓ = (Λ(ℓ))ⁿ` the volume measure is the product
`Measure.pi (fun _ => ν)` of the restricted cube measure `ν = volume.restrict (acube ℓ)`
(`Submission.BoseGases.restrict_abox_eq_pi`).  Pushing this product forward along the
two-slot evaluation `x ↦ (x i, x j)` (`i ≠ j`) produces the **scalar multiple**
`(ν univ)^(n-2) • (ν.prod ν)` of the product measure (`Work.BoseFixB2.Pot.lintegral_pi_pair_aux`),
so — because `ν` is finite on the centred cube (`ν univ = ofReal (ℓ^3) < ⊤`) — a function
`H` integrable for `ν.prod ν` pulls back to an integrable function on the box.

The mathematical content is that the finite factor `(ν univ)^(n-2)` cannot destroy
integrability; the whole argument is the `lintegral` identity

`∫⁻ x, ‖H (x i, x j)‖ₑ ∂(π ν) = (ν univ)^(n-2) * ∫⁻ p, ‖H p‖ₑ ∂(ν.prod ν)`,

together with the a.e. strong measurability of the pullback (a quasi-measure-preserving
composition).
-/

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace Work.BoseBoxFock.PCFU

/-- **Pair-evaluation integrability wrinkle (abstract form).**  If `ν` is a finite measure
(`ν univ < ⊤`, sigma-finite is part of the ambient API) and `g` is integrable for `ν.prod ν`,
then the pullback `x ↦ g (x i, x j)` of `g` along two distinct slots of an `(m+2)`-fold product
of `ν` is integrable.

The pushforward of `Measure.pi (fun _ => ν)` along the pair map is `(ν univ)^m • (ν.prod ν)`
(that is `Work.BoseFixB2.Pot.lintegral_pi_pair_aux`), and the factor `(ν univ)^m` is finite. -/
theorem integrable_pair_eval_pi {m : ℕ} {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SigmaFinite ν] (hν_top : ν Set.univ < ⊤)
    {i j : Fin (m + 2)} (hij : i ≠ j) {g : α × α → ℝ}
    (hg : MeasureTheory.Integrable g (ν.prod ν)) :
    MeasureTheory.Integrable (fun x : Fin (m + 2) → α => g (x i, x j))
      (MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν)) := by
  have hp : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : Fin (m + 2) → α => (x i, x j))
      (MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν)) (ν.prod ν) :=
    Work.BoseFixB2.Pot.quasiMeasurePreserving_pair_eval_aux ν hij
  refine ⟨?_, ?_⟩
  · exact MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving hg.1 hp
  · -- a measurable representative of `g` (the peel lemma needs genuine measurability)
    set G : α × α → ℝ := AEMeasurable.mk g hg.1.aemeasurable with hGdef
    have hGmeas : Measurable G := hg.1.aemeasurable.measurable_mk
    have hGeq : g =ᵐ[ν.prod ν] G := hg.1.aemeasurable.ae_eq_mk
    change (∫⁻ x : Fin (m + 2) → α, ‖g (x i, x j)‖ₑ
      ∂(MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν))) < ⊤
    -- replace `g` by its measurable representative, slot by slot
    have h1 : (∫⁻ x : Fin (m + 2) → α, ‖g (x i, x j)‖ₑ
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν)))
        = ∫⁻ x, ‖G (x i, x j)‖ₑ
            ∂(MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν)) := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [hp.ae_eq hGeq] with x hx
      exact congrArg (fun r : ℝ => ‖r‖ₑ) (by simpa [Function.comp_apply] using hx)
    -- the two-coordinate peel of the product measure
    have h2 : (∫⁻ x, ‖G (x i, x j)‖ₑ
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (m + 2) => ν)))
        = (ν Set.univ) ^ m * ∫⁻ a, ∫⁻ b, ‖G (a, b)‖ₑ ∂ν ∂ν :=
      Work.BoseFixB2.Pot.lintegral_pi_pair_aux (H := fun a b => ‖G (a, b)‖ₑ) ν i j hij (by
        show Measurable (fun p : α × α => ‖G p‖ₑ)
        exact hGmeas.enorm)
    have h3 : (∫⁻ a, ∫⁻ b, ‖G (a, b)‖ₑ ∂ν ∂ν) = ∫⁻ p, ‖G p‖ₑ ∂(ν.prod ν) :=
      (MeasureTheory.lintegral_prod (f := fun p : α × α => ‖G p‖ₑ)
        hGmeas.enorm.aemeasurable).symm
    have h4 : (∫⁻ p, ‖G p‖ₑ ∂(ν.prod ν)) = ∫⁻ p, ‖g p‖ₑ ∂(ν.prod ν) := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [hGeq] with p hp'
      exact (congrArg (fun r : ℝ => ‖r‖ₑ) hp').symm
    rw [h1, h2, h3, h4]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hν_top) hg.2

theorem integrableOn_pair_pullback_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n}
    (hij : i ≠ j)
    {H : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hH : MeasureTheory.Integrable H
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => H (x i, x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 :=
    ⟨n - 2, by have := Work.BoseFixB2.Pot.two_le_of_ne hij; omega⟩
  change MeasureTheory.Integrable (fun x : Submission.BoseGases.X (k + 2) => H (x i, x j))
    ((MeasureTheory.volume :
        MeasureTheory.Measure (Submission.BoseGases.X (k + 2))).restrict
      (Submission.BoseGases.abox (k + 2) ℓ))
  rw [Submission.BoseGases.restrict_abox_eq_pi (k + 2) ℓ]
  have htop : ((MeasureTheory.volume :
        MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ)) Set.univ < ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact Submission.BoseGases.acube_lt_top ℓ (le_of_lt hℓ)
  exact integrable_pair_eval_pi _ htop hij hH

end Work.BoseBoxFock.PCFU
