import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.Dim2.circle_log_facts
import Submission.Work.KT.Dim2.exists_log_of_nullhomotopic

namespace Work.KT.D2

/-- A continuous nowhere-zero complex function on the closed unit disc restricts to a loop on the
boundary circle that admits a continuous logarithm (equivalently, by `Work.KT.Dim2.circle_log_facts`,
is null-homotopic).  It follows that such a boundary loop has degree `0` for any additive
winding number.

The two ingredients are:

* the closed unit disc `D² = Ball ℝ²` is contractible (`Metric.contractibleSpace_closedBall`),
  hence every map out of the disc is null-homotopic; in particular the boundary loop
  `x ↦ g (inBall x)` is null-homotopic;
* a null-homotopic map into the units `ℂˣ` lifts through the covering map `exp : ℂ → ℂˣ`
  (`Work.KT.Dim2.exists_log_of_nullhomotopic`), and the resulting lift is the required
  logarithm. -/
theorem disc_boundary_log (g : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), ℂˣ)) :
    ∃ F : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ℂ),
      ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        Complex.exp (F x) = ((g (Work.KT.D2.inBall x) : ℂˣ) : ℂ) := by
  -- The inclusion of the boundary circle in the disc, as a continuous map.
  have hcont : Continuous Work.KT.D2.inBall :=
    Continuous.subtype_mk continuous_subtype_val _
  -- The disc is contractible, so its identity is null-homotopic, hence so is `g ∘ inBall`
  -- (null-homotopy survives pre- and post-composition).
  haveI : ContractibleSpace (Work.KT.Ball (EuclideanSpace ℝ (Fin 2))) :=
    Metric.contractibleSpace_closedBall (x := 0) (by norm_num)
  have hnull : ContinuousMap.Nullhomotopic (g.comp ⟨Work.KT.D2.inBall, hcont⟩) := by
    have h1 : (g.comp (ContinuousMap.id (Work.KT.Ball (EuclideanSpace ℝ (Fin 2))))).Nullhomotopic :=
      (id_nullhomotopic _).comp_right g
    rw [ContinuousMap.comp_id] at h1
    exact h1.comp_left _
  -- Lift the null-homotopy of the boundary loop through the exponential covering.
  obtain ⟨F, hF⟩ := Work.KT.Dim2.exists_log_of_nullhomotopic _ hnull
  exact ⟨F, fun x => by simpa using hF x⟩

end Work.KT.D2
