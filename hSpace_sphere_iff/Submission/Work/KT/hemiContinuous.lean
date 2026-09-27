import Mathlib
import Submission.Work.KT.Hemi

namespace Work.KT

theorem hemiContinuous {V : Type} [NormedAddCommGroup V] :
    Continuous (hemiUp (V := V)) ∧ Continuous (hemiDown (V := V)) ∧
      Continuous (hemiProj (V := V)) := by
  -- the two coordinates of the parametrisations, as functions of `v : Ball V`
  have hval : Continuous fun v : Ball V => (v : V) := continuous_subtype_val
  have hsqrt : Continuous fun v : Ball V => √(1 - ‖(v : V)‖ ^ 2) := by
    have h1 : Continuous fun v : Ball V => ‖(v : V)‖ := continuous_norm.comp hval
    exact Real.continuous_sqrt.comp (continuous_const.sub (h1.pow 2))
  have hUpFun : Continuous (hemiUpFun (V := V)) := by
    change Continuous fun v : Ball V => WithLp.toLp 2 ((v : V), √(1 - ‖(v : V)‖ ^ 2))
    exact (WithLp.prod_continuous_toLp 2 V ℝ).comp (hval.prodMk hsqrt)
  have hDownFun : Continuous (hemiDownFun (V := V)) := by
    change Continuous fun v : Ball V => WithLp.toLp 2 ((v : V), -√(1 - ‖(v : V)‖ ^ 2))
    exact (WithLp.prod_continuous_toLp 2 V ℝ).comp (hval.prodMk hsqrt.neg)
  -- the membership proofs of the two parametrisations
  have hUpMem : ∀ v : Ball V,
      hemiUpFun v ∈ Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 := by
    intro v
    rw [Metric.mem_sphere]
    simpa [dist_eq_norm] using norm_hemiUpFun v
  have hDownMem : ∀ v : Ball V,
      hemiDownFun v ∈ Metric.sphere (0 : WithLp 2 (V × ℝ)) 1 := by
    intro v
    rw [Metric.mem_sphere]
    simpa [dist_eq_norm] using norm_hemiDownFun v
  have hProjFun : Continuous fun x : Sph (WithLp 2 (V × ℝ)) =>
      (x : WithLp 2 (V × ℝ)).fst :=
    (WithLp.continuous_fst 2 V ℝ).comp continuous_subtype_val
  have hProjMem : ∀ x : Sph (WithLp 2 (V × ℝ)),
      (x : WithLp 2 (V × ℝ)).fst ∈ Metric.closedBall (0 : V) 1 := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
      have h := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    exact (WithLp.norm_fst_le V _).trans (le_of_eq hx)
  refine ⟨?_, ?_, ?_⟩
  · exact Continuous.subtype_mk hUpFun hUpMem
  · exact Continuous.subtype_mk hDownFun hDownMem
  · exact Continuous.subtype_mk hProjFun hProjMem

end Work.KT
