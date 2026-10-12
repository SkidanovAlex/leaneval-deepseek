import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory

/-- **Integrability of the `χ_{B(u)}`-unprojected Dirichlet integrand.**

`kinInt ℓ d Φ u x = Σ_{k : Fin 3} (∂_k (χ_{B(u)}·Φ)(x))²` is a finite sum of the squared
directional derivatives whose integrability is `integrable_fderiv_chiBPhi_sq`.  The only
remaining step is the exchange of the two factors of the product measure `pdMu ℓ`, which is the
measure-preserving swap `Prod.swap` (`MeasureTheory.integrable_swap_iff`). -/
theorem integrable_kinInt {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hcs : HasCompactSupport Φ) :
    MeasureTheory.Integrable
      (fun p : (EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X 1 =>
        Work.UBBInputs9.B.kinInt ℓ d Φ p.1 p.2)
      (Work.UBBInputs9.B.pdMu ℓ) := by
  classical
  -- The single-`k` integrand on `X 1 × ℝ³` (with the box measure on the state variable).
  have hk : ∀ k : Fin 3, MeasureTheory.Integrable
      (fun p : Submission.BoseGases.X 1 × EuclideanSpace ℝ (Fin 3) =>
        (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
          Submission.BoseGases.chiB ℓ d p.2 (y 0) * Φ y) p.1
            (Submission.BoseGases.kcDir 1 0 k)) ^ 2)
      (((MeasureTheory.volume : Measure (Submission.BoseGases.X 1)).restrict
          (Submission.BoseGases.abox 1 ℓ)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    fun k => Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq ℓ d hℓ hd hΦ hcs k
  -- Their finite sum is integrable.
  have hsum : MeasureTheory.Integrable
      (fun p : Submission.BoseGases.X 1 × EuclideanSpace ℝ (Fin 3) =>
        ∑ k : Fin 3,
          (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
            Submission.BoseGases.chiB ℓ d p.2 (y 0) * Φ y) p.1
              (Submission.BoseGases.kcDir 1 0 k)) ^ 2)
      (((MeasureTheory.volume : Measure (Submission.BoseGases.X 1)).restrict
          (Submission.BoseGases.abox 1 ℓ)).prod
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
    exact
      (MeasureTheory.integrable_finsetSum (μ := ((MeasureTheory.volume :
            Measure (Submission.BoseGases.X 1)).restrict (Submission.BoseGases.abox 1 ℓ)).prod
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (s := Finset.univ)
        (f := fun k (p : Submission.BoseGases.X 1 × EuclideanSpace ℝ (Fin 3)) =>
          (fderiv ℝ (fun y : Submission.BoseGases.X 1 =>
            Submission.BoseGases.chiB ℓ d p.2 (y 0) * Φ y) p.1
              (Submission.BoseGases.kcDir 1 0 k)) ^ 2)
        (fun k _ => hk k))
  -- Exchange the two factors of the product measure.
  have hswap := (MeasureTheory.integrable_swap_iff
      (μ := (MeasureTheory.volume : Measure (Submission.BoseGases.X 1)).restrict
        (Submission.BoseGases.abox 1 ℓ))
      (ν := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (E := ℝ)).mpr hsum
  rw [Work.UBBInputs9.B.pdMu]
  refine hswap.congr ?_
  filter_upwards with q
  rfl

end Work.UBBInputs9.B.pd_aux
