import Mathlib
import Submission.Work.Drive.chordSweepSmooth

namespace Work.Drive

theorem gluePsi_facts :
    Work.Drive.gluePsi 0 = 0 ∧ Work.Drive.gluePsi 1 = 1 ∧
    (∀ s ∈ Set.Icc (0:ℝ) 1, Work.Drive.gluePsi s ∈ Set.Icc (0:ℝ) 1) ∧
    (∀ x : ℝ, HasDerivAt Work.Drive.gluePsi (6*x*(1-x)) x) ∧
    ContDiff ℝ 1 Work.Drive.gluePsi := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [gluePsi]
  · norm_num [gluePsi]
  · intro s hs
    simp only [Set.mem_Icc] at hs ⊢
    constructor
    · rw [gluePsi]
      exact mul_nonneg (sq_nonneg s) (by linarith [hs.2])
    · rw [gluePsi]
      nlinarith [sq_nonneg (s - 1), hs.1, hs.2]
  · intro x
    have h1 : HasDerivAt (fun s : ℝ => s^2) (2*x) x := by simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun s : ℝ => 3 - 2*s) (-2) x := by
      have h := ((hasDerivAt_id x).const_mul (2:ℝ)).const_sub (3:ℝ)
      simpa using h
    have hprod := h1.mul h2
    have hfun : (fun s : ℝ => s^2) * (fun s => 3 - 2*s) = fun s => s^2 * (3 - 2*s) := rfl
    have hval : 2*x*(3-2*x) + x^2 * (-2) = 6*x*(1-x) := by ring
    rw [hfun, hval] at hprod
    exact hprod
  · unfold gluePsi
    fun_prop

end Work.Drive
