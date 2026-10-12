import ChallengeDeps
import Submission.Work.BoseSym.Perm.integral_sq_symAvgF_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSym.Bridge.intOnBox_symAvgF`

Integrability on the box is preserved by the symmetrisation average.  If
`f : Conf N → ℝ` is integrable on `box N L`, then so is

`symAvgF N f = (N!)⁻¹ · ∑_σ f ∘ actPerm σ`.

Indeed, each relabelling `f ∘ actPerm σ` is integrable on the box (a
relabelling of the particles leaves both `box N L` and Lebesgue measure on it
invariant), and `symAvgF N f` is a finite linear combination of these; this is
exactly `Work.BoseSym.Perm.IntegralSqSymAvg.integrableOn_actPerm_box_iff`
together with `integrable_finsetSum` and `Integrable.const_mul`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory

theorem intOnBox_symAvgF {N : ℕ} {L : ℝ} {f : Work.BoseSym.Conf N → ℝ}
    (hf : Work.BoseSym.IntOnBox N L f) :
    Work.BoseSym.IntOnBox N L (Work.BoseSym.symAvgF N f) := by
  classical
  have hσ : ∀ σ : Equiv.Perm (Fin N),
      Integrable (fun x => f (Submission.BoseGases.actPerm N σ x))
        (volume.restrict (BoseGases.box N L)) :=
    fun σ =>
      (Work.BoseSym.Perm.IntegralSqSymAvg.integrableOn_actPerm_box_iff L σ f).mpr hf
  have hsum : Integrable (fun x => ∑ σ : Equiv.Perm (Fin N),
      f (Submission.BoseGases.actPerm N σ x))
      (volume.restrict (BoseGases.box N L)) := by
    have h := integrable_finsetSum (μ := volume.restrict (BoseGases.box N L))
      (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (f := fun σ x => f (Submission.BoseGases.actPerm N σ x))
      (fun σ _ => hσ σ)
    simpa using h
  have hfin : Integrable (Work.BoseSym.symAvgF N f)
      (volume.restrict (BoseGases.box N L)) :=
    hsum.const_mul (1 / (Nat.factorial N : ℝ))
  exact hfin

end Work.BoseSym.Bridge
