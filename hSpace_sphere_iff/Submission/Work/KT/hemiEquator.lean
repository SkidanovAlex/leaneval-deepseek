import Mathlib
import Submission.Work.KT.Hemi

namespace Work.KT

noncomputable section

variable {V : Type} [NormedAddCommGroup V]

theorem hemiEquator {V : Type} [NormedAddCommGroup V] :
    (∀ s : Sph V, hemiUp (sphToBall V s) = hemiDown (sphToBall V s)) ∧
    (∀ x : Sph (WithLp 2 (V × ℝ)), (x : WithLp 2 (V × ℝ)).snd = 0 →
      ‖((hemiProj x : Ball V) : V)‖ = 1) ∧
    (∀ v : Ball V, 0 ≤ (hemiDownFun v).snd → ‖(v : V)‖ = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs : ‖((sphToBall V s : Ball V) : V)‖ = 1 := by
      rw [sphToBall_apply]; exact mem_sphere_zero_iff_norm.mp s.2
    apply Subtype.ext
    rw [hemiUp_coe, hemiDown_coe]
    show hemiUpFun (sphToBall V s) = hemiDownFun (sphToBall V s)
    rw [hemiUpFun, hemiDownFun, hs]
    simp
  · intro x hx
    have hx1 : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
      have h := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    have h2 := WithLp.prod_norm_sq_eq_of_L2 (x : WithLp 2 (V × ℝ))
    rw [hx1, hx, norm_zero] at h2
    have hsq : ‖(x : WithLp 2 (V × ℝ)).fst‖ ^ 2 = 1 := by
      nlinarith [h2]
    rw [hemiProj_coe]
    nlinarith [norm_nonneg (x : WithLp 2 (V × ℝ)).fst, hsq]
  · intro v hv
    have hvle : ‖(v : V)‖ ≤ 1 := by
      have h := Metric.mem_closedBall.mp v.2
      rwa [dist_eq_norm, sub_zero] at h
    have h1 : (0 : ℝ) ≤ 1 - ‖(v : V)‖ ^ 2 := by
      nlinarith [hvle, norm_nonneg (v : V)]
    have hs : Real.sqrt (1 - ‖(v : V)‖ ^ 2) = 0 := by
      have h := hv
      rw [hemiDownFun_snd] at h
      have hnn := Real.sqrt_nonneg (1 - ‖(v : V)‖ ^ 2)
      linarith
    have hzero : 1 - ‖(v : V)‖ ^ 2 = 0 := by
      have h := Real.sq_sqrt h1
      rw [hs] at h
      simpa using h.symm
    nlinarith [norm_nonneg (v : V)]

end

end Work.KT
