import Mathlib
import Submission.Work.Octonion.Basic

open scoped Quaternion
open WithLp

namespace Work.Octonion

/-- The Cayley–Dickson product `cdMul` on `ℍ × ℍ` underlies the octonion multiplication
(`Submission.Octonion` is `WithLp 2 (ℍ × ℍ)`); here we record that it is continuous. -/
theorem continuous_cdMul :
    Continuous fun p : (ℍ × ℍ) × (ℍ × ℍ) => Submission.Octonion.cdMul p.1 p.2 := by
  simp only [Submission.Octonion.cdMul]
  fun_prop

theorem continuous_mul :
    Continuous fun p : Submission.Octonion × Submission.Octonion => p.1 * p.2 := by
  -- `Octonion` is `WithLp 2 (ℍ × ℍ)`, so the multiplication is the `WithLp`-transport of `cdMul`.
  have hfun : (fun p : Submission.Octonion × Submission.Octonion => p.1 * p.2)
      = fun p => WithLp.toLp 2 (Submission.Octonion.cdMul (WithLp.ofLp p.1) (WithLp.ofLp p.2)) := by
    funext p
    rfl
  rw [hfun]
  have hg : Continuous fun p : Submission.Octonion × Submission.Octonion =>
      (WithLp.ofLp p.1, WithLp.ofLp p.2) :=
    Continuous.prodMk ((WithLp.prod_continuous_ofLp 2 ℍ ℍ).comp continuous_fst)
      ((WithLp.prod_continuous_ofLp 2 ℍ ℍ).comp continuous_snd)
  exact (WithLp.prod_continuous_toLp 2 ℍ ℍ).comp (continuous_cdMul.comp hg)

end Work.Octonion
