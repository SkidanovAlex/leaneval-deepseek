import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

/-- The `aQ`-squared integral over the full `(N₁+N₂)`-box equals the iterated
`w`-outer / `u`-inner integral of the same squared integrand along the block
concatenation `mergeBlock`.  This is the `w`-outer Fubini identity
`Submission.BoseGases.aboxFubini_swapped` applied to the integrand
`x ↦ (aQ s (N₁+N₂) (castAdd N₂ j) Φ x)²`, whose integrability over the compact
box is `Submission.BoseGases.integrableOn_sq_aQ`. -/
theorem fubini_aQ_fst {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) (j : Fin N1)
    {Φ : Submission.BoseGases.X (N1 + N2) → ℝ} (hΦ : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox (N1 + N2) s,
        (@Submission.BoseGases.aQ s (N1 + N2) (Fin.castAdd N2 j) Φ x)^2)
      = ∫ w in Submission.BoseGases.abox N2 s,
          ∫ u in Submission.BoseGases.abox N1 s,
            (@Submission.BoseGases.aQ s (N1 + N2) (Fin.castAdd N2 j) Φ
              (Submission.BoseGases.mergeBlock N1 N2 (u, w)))^2 := by
  have hG : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (N1 + N2) =>
        (@Submission.BoseGases.aQ s (N1 + N2) (Fin.castAdd N2 j) Φ x)^2)
      (Submission.BoseGases.abox (N1 + N2) s) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_sq_aQ hs (Fin.castAdd N2 j) hΦ
  exact (Submission.BoseGases.aboxFubini_swapped (N1 := N1) (N2 := N2) s
    (fun x => (@Submission.BoseGases.aQ s (N1 + N2) (Fin.castAdd N2 j) Φ x)^2) hG).symm

end Work.KinPSuperadd
