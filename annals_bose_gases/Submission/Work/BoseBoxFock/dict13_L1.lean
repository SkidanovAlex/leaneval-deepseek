import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dict13Aux10
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem dict13_L1 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (hΨsym : Submission.BoseGases.PermInvariant n Ψ)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : MeasureTheory.AEStronglyMeasurable (Function.uncurry k) MeasureTheory.volume)
    (hkI : MeasureTheory.Integrable (Function.uncurry k) MeasureTheory.volume)
    (hksym : ∀ w y, k w y = k y w)
    {c : ℂ} (hc : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1) (hr : (starRingEnd ℂ) c = c)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    ((ℓ ^ 3)⁻¹ : ℝ) *
        (Work.BoseBoxFock.rowShape13 (Work.BoseBoxFock.boxRestrictC ℓ Ψ)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (Work.BoseBoxFock.qmqKernel ℓ k) p).re
      = ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
            * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
            * k (x p.1) (x p.2) := by
  classical
  -- the weight and its bound on the box
  set G : Submission.BoseGases.X n → ℝ := fun x =>
    Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
      * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x with hGdef
  have hGc : Continuous G := by
    rw [hGdef]
    exact (Submission.BoseGases.aP_continuous hℓ p.1
        (Submission.BoseGases.aQ_continuous hℓ p.2 hΨc)).mul
      (Submission.BoseGases.aP_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΨc))
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    (f := G) hGc.continuousOn
  have hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ, ‖G x‖ ≤ max C 0 := fun x hx =>
    le_trans (hC x hx) (le_max_left _ _)
  -- the `L¹` transfer at the box restriction and the `θ`-weights
  refine (lhsFun_eq_lhsGen (c := c) (p := p) k).trans ?_
  refine lhsGen_eq_of_bounded (D := rowDataBoxRestrict hℓ hΨc hp) (G := G)
    (Bc := max C 0) (le_max_right _ _) hGc hGb ?_ hkm hkI hksym
  -- the bounded case is the proved dictionary
  intro h hm hb hs
  exact block13_dict hℓ hΨc hΨsym hm (by simpa only [Real.norm_eq_abs] using hb) hs hc hr hp

end Work.BoseBoxFock
