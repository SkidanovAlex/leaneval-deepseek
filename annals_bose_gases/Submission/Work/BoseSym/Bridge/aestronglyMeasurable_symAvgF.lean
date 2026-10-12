import ChallengeDeps
import Submission.Work.BoseSym.Perm.integral_sq_symAvgF_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A.e. strong measurability of the symmetrisation average

The symmetrisation average

`symAvgF N f x = (N!)⁻¹ · ∑_σ f (actPerm σ x)`

is a finite average of precompositions of `f` with the particle permutations
`actPerm σ`.  Every `actPerm σ` preserves Lebesgue measure restricted to the box
`box N L` (`Work.BoseSym.Perm.IntegralSqSymAvg.measurePreserving_tauPerm_box`),
i.e. it is quasi-measure preserving for that restricted measure; hence each
`f ∘ actPerm σ` is a.e. strongly measurable on the box as soon as `f` is
(`AEStronglyMeasurable.comp_quasiMeasurePreserving`).  The claim then follows
from closure of a.e. strong measurability under finite sums
(`Finset.aestronglyMeasurable_sum`) and under multiplication by a constant
(`AEStronglyMeasurable.const_mul`).
-/

namespace Work.BoseSym.Bridge

/-- The symmetrisation average of an a.e. strongly measurable function on the
box is again a.e. strongly measurable on the box. -/
theorem aestronglyMeasurable_symAvgF {N : ℕ} {L : ℝ} {f : Work.BoseSym.Conf N → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (BoseGases.box N L))) :
    MeasureTheory.AEStronglyMeasurable (Work.BoseSym.symAvgF N f)
      (MeasureTheory.volume.restrict (BoseGases.box N L)) := by
  -- unfold the symmetrisation average
  change MeasureTheory.AEStronglyMeasurable (fun x : Work.BoseSym.Conf N =>
      (1 / (Nat.factorial N : ℝ)) * ∑ σ : Equiv.Perm (Fin N),
        f (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L))
  -- each summand `f ∘ actPerm σ` is a.e. strongly measurable, since `actPerm σ`
  -- is quasi-measure preserving for the restricted measure
  have hterm : ∀ σ : Equiv.Perm (Fin N),
      MeasureTheory.AEStronglyMeasurable
        (fun x : Work.BoseSym.Conf N => f (Submission.BoseGases.actPerm N σ x))
        (MeasureTheory.volume.restrict (BoseGases.box N L)) := by
    intro σ
    have hmp := Work.BoseSym.Perm.IntegralSqSymAvg.measurePreserving_tauPerm_box (N := N) L σ
    exact hf.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  -- finite sums and constant multiples preserve a.e. strong measurability
  have h₁ : MeasureTheory.AEStronglyMeasurable
      (∑ σ : Equiv.Perm (Fin N), fun x : Work.BoseSym.Conf N =>
        f (Submission.BoseGases.actPerm N σ x))
      (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
    Finset.aestronglyMeasurable_sum Finset.univ (fun σ _ => hterm σ)
  have h₂ := h₁.const_mul (1 / (Nat.factorial N : ℝ))
  convert h₂ using 1
  funext x
  simp [Finset.sum_apply]

end Work.BoseSym.Bridge
