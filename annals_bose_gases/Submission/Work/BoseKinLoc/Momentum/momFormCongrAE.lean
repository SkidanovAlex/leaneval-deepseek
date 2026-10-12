import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.momDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momFormCongrAE` — the `momForm` only sees the box

`momForm ℓ d u ψ = (2π)⁻³ ∫_p 1_{(d²ℓ)⁻¹,∞)}(‖p‖)·‖kinFT (1_{Λ(u)}(ψ − m_u))‖²`
(FS `eq:DefT`, third term) is a functional of the *restriction of `ψ` to the sliding box*
`Λ(u) = bsBox ℓ u`: the window `indU ℓ u = 1_{Λ(u)}` kills everything outside `Λ(u)`, and the
box mean `m_u` is an integral over `Λ(u)`.  Hence if `ψ = g` a.e. on `Λ(u)` then
`momForm ℓ d u ψ = momForm ℓ d u g`.

The three steps are:

* `bsMean_congr_ae` — the box means agree (`setIntegral_bigBox_eq_translate` rewrites the box
  mean as an integral over `Λ(u)`, and `ae_restrict_iff'` turns the hypothesis into an a.e.
  equality for the restricted measure);
* the windowed mean-free states `1_{Λ(u)}(ψ − m_u)` and `1_{Λ(u)}(g − m_g)` agree pointwise off
  a null set (outside `Λ(u)` both vanish);
* `kinFT` of two a.e. equal functions agree (`integral_congr_ae`), and then so do the `p`-integrals.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.BoseKinLoc.Momentum

/-- The moving box `Λ(u) = bsBox ℓ u` is measurable. -/
private lemma measurableSet_bsBox (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasurableSet (Work.BSKinetic.bsBox ℓ u) := by
  have h : Work.BSKinetic.bsBox ℓ u
      = (fun x : EuclideanSpace ℝ (Fin 3) => x - ℓ • u) ⁻¹' Submission.BoseGases.acube ℓ := rfl
  rw [h]
  exact (Submission.BoseGases.acube_measurable ℓ).preimage (by fun_prop)

/-- The box mean as an integral over the moving box: `m_u(φ) = ℓ⁻³ ∫_{Λ(u)} φ`. -/
private lemma bsMean_eq_setIntegral (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BSKinetic.bsMean ℓ u φ
      = (ℓ ^ 3)⁻¹ * ∫ x in Work.BSKinetic.bsBox ℓ u, φ x := by
  rw [Work.BSKinetic.bsMean, Work.BSKinetic.bsBox_eq_bigBox,
    ← Work.BSKinetic.setIntegral_bigBox_eq_translate]

/-- The box means of two functions that agree a.e. on the box coincide. -/
private lemma bsMean_congr_ae (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      y ∈ Work.BSKinetic.bsBox ℓ u → ψ y = g y) :
    Work.BSKinetic.bsMean ℓ u ψ = Work.BSKinetic.bsMean ℓ u g := by
  have hbox_ae : ψ =ᵐ[(MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Work.BSKinetic.bsBox ℓ u)] g :=
    (ae_restrict_iff' (measurableSet_bsBox ℓ u)).2 h
  rw [bsMean_eq_setIntegral ℓ u ψ, bsMean_eq_setIntegral ℓ u g, integral_congr_ae hbox_ae]

/-- The windowed mean-free box state `1_{Λ(u)}(ψ − m_u)` is determined a.e. by the values of `ψ`
on the box. -/
private lemma statU_congr_ae (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      y ∈ Work.BSKinetic.bsBox ℓ u → ψ y = g y) :
    (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u g z : ℝ) : ℂ)) := by
  have hmean := bsMean_congr_ae ℓ u h
  filter_upwards [h] with y hy
  by_cases hyb : y ∈ Work.BSKinetic.bsBox ℓ u
  · have hψg : ψ y = g y := hy hyb
    have hQ : Work.BoseKinLoc.Qfree ℓ u ψ y = Work.BoseKinLoc.Qfree ℓ u g y := by
      simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]
      rw [hmean, hψg]
    rw [hQ]
  · have h0 : Work.BoseKinLoc.indU ℓ u y = 0 := by
      simp only [Work.BoseKinLoc.indU, Work.BoseKinLoc.lamBox]
      exact Set.indicator_of_notMem hyb _
    simp [h0]

theorem momFormCongrAE (ℓ d : ℝ) {ψ g : EuclideanSpace ℝ (Fin 3) → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (h : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      y ∈ Work.BSKinetic.bsBox ℓ u → ψ y = g y) :
    Work.BoseKinLoc.momForm ℓ d u ψ = Work.BoseKinLoc.momForm ℓ d u g := by
  have hae := statU_congr_ae ℓ u h
  -- `kinFT` of two a.e. equal functions coincide.
  have hFT : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u g z : ℝ) : ℂ)) p := by
    intro p
    simp only [Submission.BoseGases.kinFT]
    apply integral_congr_ae
    filter_upwards [hae] with z hz
    rw [hz]
  simp only [Work.BoseKinLoc.momForm]
  have hInt : (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u ψ z : ℝ) : ℂ)) p‖ ^ 2)
      = (∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.momProj ℓ d p *
      ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          ((Work.BoseKinLoc.indU ℓ u z : ℝ) : ℂ) * ((Work.BoseKinLoc.Qfree ℓ u g z : ℝ) : ℂ)) p‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [hFT p]
  rw [hInt]

end Work.BoseKinLoc.Momentum
