import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Compare

theorem potential_fubini_v2 {N : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ : ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ2 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2))
    (hswap : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
      (Φ p.2) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ p.1 p.2))
    (hpot : ∀ x : Submission.BoseGases.X N,
      (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        = -μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)
          + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
        (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3), ∫ x : Submission.BoseGases.X N,
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        = (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 *
              (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
          - μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)
              * (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) := by
  -- The first conjunct: `hpot` turns the `u`-average of `potWordU` into the
  -- un-localised potential, so `Φ²·Σv` is the marginal of the joint `u`-integrand.
  have hintS : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))) := by
    have hFub := hswap.integral_prod_right
    have h1 : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        (∫ u : EuclideanSpace ℝ (Fin 3), (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        + (μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)) * (Φ x) ^ 2) :=
      hFub.add (hΦ2.const_mul (μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)))
    refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
    show (∫ u : EuclideanSpace ℝ (Fin 3), (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        + (μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)) * (Φ x) ^ 2
      = (Φ x) ^ 2 * (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))
    rw [MeasureTheory.integral_const_mul]
    rw [hpot x]
    ring
  have hintc : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      (Φ x) ^ 2 * (-μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y))) :=
    (hΦ2.const_mul (-μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y))).congr
      (Filter.Eventually.of_forall (fun x => by ring))
  refine ⟨hintS, ?_⟩
  -- The second conjunct: Fubini plus the pointwise identity `hpot`.
  calc ∫ u : EuclideanSpace ℝ (Fin 3), ∫ x : Submission.BoseGases.X N,
          (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x
      = ∫ x : Submission.BoseGases.X N, ∫ u : EuclideanSpace ℝ (Fin 3),
          (Φ x) ^ 2 * Work.BoseKinLoc.potWordU N v g ℓ μ u x :=
        MeasureTheory.integral_integral_swap hswap
    _ = ∫ x : Submission.BoseGases.X N,
          (Φ x) ^ 2 * (∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.potWordU N v g ℓ μ u x) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
          (fun x => MeasureTheory.integral_const_mul _ _))
    _ = ∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 *
          (-μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)
            + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
          (fun x => by simp only [hpot x]))
    _ = ∫ x : Submission.BoseGases.X N, ((Φ x) ^ 2 *
            (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))
          + (Φ x) ^ 2 * (-μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y))) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    _ = (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 *
            (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
          + ∫ x : Submission.BoseGases.X N,
              (Φ x) ^ 2 * (-μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)) :=
        MeasureTheory.integral_add hintS hintc
    _ = (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2 *
            (∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2)))
          - μ * (N : ℝ) * (∫ y : EuclideanSpace ℝ (Fin 3), g y)
              * (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) := by
        rw [MeasureTheory.integral_mul_const]
        ring

end Work.BoseKinLoc.Compare
