import Mathlib
import Submission.Work.CLift.bridge
import Submission.Work.CLift.Phi_ne_root
import Submission.Work.CLift.q4_roots
import Submission.Work.CLift.basic_aux
import Submission.Work.CLift.defs

namespace Work.CLift

open Submission.CDTPlan Metric

/-- `R2p m n x = (x-1)·x·Q₄(x)`, with `Q₄` written in the form used by `q4_roots`. -/
lemma R2p_factor (m n : ℕ) (x : ℂ) :
    R2p m n x = (x - 1) * x *
      (x ^ 4 - 4 * ((2 * m + 1 : ℕ) : ℂ) * ((2 * n + 1 : ℕ) : ℂ) * x ^ 3
        + (4 * ((2 * m + 1 : ℕ) : ℂ) ^ 2 + 4 * ((2 * n + 1 : ℕ) : ℂ) ^ 2 - 2) * x ^ 2
        - 4 * ((2 * m + 1 : ℕ) : ℂ) * ((2 * n + 1 : ℕ) : ℂ) * x + 1) := by
  simp only [R2p, aa, bb]
  push_cast
  ring

/-- The value `Φ z` of a lift `Φ` of `φ_C` at a point `3.2e-4 < ‖z‖ < 1` is not a root of
`R2p = (x-1)xQ₄`: it is neither `0` (by `hΦ0`), nor `1` (`basic_aux.Phi_ne_one`), nor any of the
four roots `xRoot m n (±1) (±1)` of `Q₄` (`q4_roots` together with `Phi_ne_root`). -/
theorem R2p_ne_zero (m n : ℕ) (ra rb rab r0 : ℤ) (hL : Submission.CDTPlan.CLocation)
    (hN : Submission.CDTPlan.CNumerics) (hM : Submission.CDTPlan.HauptFacts)
    (hP : Submission.CDTPlan.PsiCFacts) (hAdm : Submission.CDTPlan.CAdm m n)
    (hRel : Submission.CDTPlan.CRel m n ra rb rab r0) (Φ : ℂ → ℂ)
    (hΦeq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Φ z + Φ (-z) = Submission.CDTPlan.phiC (z ^ 2) ∧ Φ z * Φ (-z) = Submission.CDTPlan.phiC (z ^ 2))
    (hΦ0 : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z = 0 → z = 0)
    {z : ℂ} (hzr : 3.2e-4 < ‖z‖) (hz1 : ‖z‖ < 1) :
    Work.CLift.R2p m n (Φ z) ≠ 0 := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz1
  intro hcon
  rw [R2p_factor m n (Φ z)] at hcon
  rcases mul_eq_zero.mp hcon with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · -- `Φ z = 1`, impossible by `Phi_ne_one`
      exact Phi_ne_one Φ hΦeq z hzmem (sub_eq_zero.mp h2)
    · -- `Φ z = 0`, impossible since `z ≠ 0`
      have hz0 : z = 0 := hΦ0 z hzmem h2
      rw [hz0, norm_zero] at hzr
      norm_num at hzr
  · -- `Q₄ (Φ z) = 0`, so `Φ z` is one of the four roots, excluded by `Phi_ne_root`
    rcases q4_roots m n (Φ z) (by linear_combination h1) with h2 | h2 | h2 | h2
    · exact Phi_ne_root m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 z hzmem hzr
        1 1 (Or.inl rfl) (Or.inl rfl) h2
    · exact Phi_ne_root m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 z hzmem hzr
        1 (-1) (Or.inl rfl) (Or.inr rfl) h2
    · exact Phi_ne_root m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 z hzmem hzr
        (-1) 1 (Or.inr rfl) (Or.inl rfl) h2
    · exact Phi_ne_root m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 z hzmem hzr
        (-1) (-1) (Or.inr rfl) (Or.inr rfl) h2

end Work.CLift
