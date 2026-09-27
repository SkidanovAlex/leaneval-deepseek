import Mathlib
import Submission.Work.KT.Hemi

namespace Work.KT

theorem hemiParam {V : Type} [NormedAddCommGroup V] :
    (∀ v : Ball V, hemiProj (hemiUp v) = v) ∧
    (∀ v : Ball V, hemiProj (hemiDown v) = v) ∧
    (∀ v : Ball V, 0 ≤ (hemiUpFun v).snd) ∧
    (∀ v : Ball V, (hemiDownFun v).snd ≤ 0) ∧
    (∀ x : Sph (WithLp 2 (V × ℝ)), 0 ≤ (x : WithLp 2 (V × ℝ)).snd → hemiUp (hemiProj x) = x) ∧
    (∀ x : Sph (WithLp 2 (V × ℝ)),
      (x : WithLp 2 (V × ℝ)).snd ≤ 0 → hemiDown (hemiProj x) = x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; ext; simp
  · intro v; ext; simp
  · intro v; simp
  · intro v; simp
  · intro x hx
    apply Subtype.ext
    show hemiUpFun (hemiProj x) = (x : WithLp 2 (V × ℝ))
    rw [WithLp.ext_iff]
    apply Prod.ext
    · show (hemiUpFun (hemiProj x)).fst = (x : WithLp 2 (V × ℝ)).fst
      simp
    · show (hemiUpFun (hemiProj x)).snd = (x : WithLp 2 (V × ℝ)).snd
      have hxnorm : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
        have h := Metric.mem_sphere.mp x.2
        rwa [dist_eq_norm, sub_zero] at h
      have hprod := WithLp.prod_norm_sq_eq_of_L2 (x : WithLp 2 (V × ℝ))
      rw [hxnorm] at hprod
      have hns : ‖(x : WithLp 2 (V × ℝ)).snd‖ = (x : WithLp 2 (V × ℝ)).snd :=
        Real.norm_of_nonneg hx
      have hsq : ‖(x : WithLp 2 (V × ℝ)).snd‖ ^ 2 = (x : WithLp 2 (V × ℝ)).snd ^ 2 := by
        rw [hns]
      have key : 1 - ‖(x : WithLp 2 (V × ℝ)).fst‖ ^ 2 = (x : WithLp 2 (V × ℝ)).snd ^ 2 := by
        nlinarith [hprod, hsq]
      rw [show (hemiUpFun (hemiProj x)).snd =
        √(1 - ‖((hemiProj x : Ball V) : V)‖ ^ 2) from rfl]
      simp only [hemiProj_coe]
      rw [key, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]
  · intro x hx
    apply Subtype.ext
    show hemiDownFun (hemiProj x) = (x : WithLp 2 (V × ℝ))
    rw [WithLp.ext_iff]
    apply Prod.ext
    · show (hemiDownFun (hemiProj x)).fst = (x : WithLp 2 (V × ℝ)).fst
      simp
    · show (hemiDownFun (hemiProj x)).snd = (x : WithLp 2 (V × ℝ)).snd
      have hxnorm : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
        have h := Metric.mem_sphere.mp x.2
        rwa [dist_eq_norm, sub_zero] at h
      have hprod := WithLp.prod_norm_sq_eq_of_L2 (x : WithLp 2 (V × ℝ))
      rw [hxnorm] at hprod
      have hns : ‖(x : WithLp 2 (V × ℝ)).snd‖ = -(x : WithLp 2 (V × ℝ)).snd :=
        Real.norm_of_nonpos hx
      have hsq : ‖(x : WithLp 2 (V × ℝ)).snd‖ ^ 2 = (x : WithLp 2 (V × ℝ)).snd ^ 2 := by
        rw [hns]; ring
      have key : 1 - ‖(x : WithLp 2 (V × ℝ)).fst‖ ^ 2 = (x : WithLp 2 (V × ℝ)).snd ^ 2 := by
        nlinarith [hprod, hsq]
      rw [show (hemiDownFun (hemiProj x)).snd =
        -√(1 - ‖((hemiProj x : Ball V) : V)‖ ^ 2) from rfl]
      simp only [hemiProj_coe]
      rw [key, Real.sqrt_sq_eq_abs, abs_of_nonpos hx]
      ring

end Work.KT
