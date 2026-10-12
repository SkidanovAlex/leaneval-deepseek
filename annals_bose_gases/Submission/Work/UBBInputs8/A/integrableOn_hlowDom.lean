import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.integral_abox_comp_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

/-- **Integrability over the analysis box of the dominating function.**

`x ↦ S·(μ·KL·T·Σᵢχ_{B(u)}(xᵢ) + ½·KP·Σ_{p ∈ pairSet N} χ_{B(u)}(x_p1)χ_{B(u)}(x_p2))` is a
finite sum of products of the continuous functions `x ↦ χ_{B(u)}(xᵢ)` (each
`Submission.BoseGases.chiSmallB_continuous` composed with `continuous_apply`), hence continuous
on the compact `abox N L`; `ContinuousOn.integrableOn_compact` finishes. -/
theorem integrableOn_hlowDom {N : ℕ} {M : ℕ} (hM : 1 ≤ M) {L dd μ S KL KP T : ℝ}
    (hL : 0 < L) (hd : 0 < dd) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        S * (μ * (KL * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
              KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
                * Submission.BoseGases.chiSmallB M L dd u (x p.2))))
      (Submission.BoseGases.abox N L) := by
  -- Continuity of every coordinate insertion of the box cutoff `χ_{B(u)}`.
  have hchi : ∀ i : Fin N, Continuous (fun x : Submission.BoseGases.X N =>
      Submission.BoseGases.chiSmallB M L dd u (x i)) := fun i =>
    (Submission.BoseGases.chiSmallB_continuous hM hL hd u).comp (continuous_apply i)
  -- Continuity of the one-particle kinetic sum and of the pair sum.
  have hsum : Continuous (fun x : Submission.BoseGases.X N =>
      ∑ i : Fin N, Submission.BoseGases.chiSmallB M L dd u (x i)) :=
    continuous_finsetSum _ (fun i _ => hchi i)
  have hpair : Continuous (fun x : Submission.BoseGases.X N =>
      ∑ p ∈ Submission.BoseGases.pairSet N,
        KP * Submission.BoseGases.chiSmallB M L dd u (x p.1)
          * Submission.BoseGases.chiSmallB M L dd u (x p.2)) := by
    apply continuous_finsetSum
    intro p hp
    exact (continuous_const.mul (hchi p.1)).mul (hchi p.2)
  -- Hence the whole dominating function is continuous, so integrable on the compact box.
  exact Submission.BoseGases.integrableOn_abox_of_continuous hL (by fun_prop)

end Work.UBBInputs8.A
