import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Compare

/-- **The large-momentum word `momForm` is a.e. strongly measurable along an inserted fibre.**

This is the `Compare`-namespace re-export of `Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable`
(the two statements differ only in the declaration name).  Mathematically: the `u = q.1`
dependence of `momForm ℓ d u ψ` sits in the moving-box indicator `1_{Λ(u)}` and in the box mean
`m_u(ψ)` entering `Q_uψ`; the `v = q.2` dependence sits in the fibre family
`v ↦ (z ↦ Φ(kcInsN n i (z,v)))`.  Both are jointly measurable, the box mean being an integral
over the fixed cube `acube ℓ` of a shift of that family, and the momentum transform being an
integral against the jointly measurable kernel `(p,y) ↦ exp(−i⟨p,y⟩)`; the Bochner integral is
defined unconditionally, so `MeasureTheory.StronglyMeasurable.integral_prod_right'` gives strong
measurability of the `p`-integral with no integrability hypothesis. -/
theorem momForm_fibre_aemeasurable_v2 {ℓ d : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.momForm ℓ d q.1
          (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :=
  Work.BoseKinLoc.Kinetic.momForm_fibre_aemeasurable hΦ i

end Work.BoseKinLoc.Compare
