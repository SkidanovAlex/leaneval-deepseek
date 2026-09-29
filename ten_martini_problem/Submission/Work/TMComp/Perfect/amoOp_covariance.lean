import Mathlib
import Submission.Work.TMComp.PerfectDefs

/-!
# Covariance of the almost Mathieu family under the shift

The canonical almost Mathieu operator `amoOp α lam θ` of
`Submission/Work/TMComp/PerfectDefs.lean` is covariant under the shift `sh k` on `ℓ²(ℤ)`,
the phase being transported by `θ ↦ θ + kα`:

  `sh k * amoOp α lam θ = amoOp α lam (θ + kα) * sh k`.

Both sides are evaluated coordinatewise: for `f : ℓ²(ℤ)` and `n : ℤ` the left hand side is
the almost Mathieu expression at the index `n + k`, and the right hand side the same
expression at the index `n` for the shifted sequence, with the phase `θ + kα`.  The two
agree because `θ + (n + k)α = (θ + kα) + nα`.
-/

namespace Work.TMComp.Perfect

open Work.TMContract (amoPot)

/-- The almost Mathieu potential is transported by a shift of the index. -/
theorem amoPot_shift (α lam θ : ℝ) (k n : ℤ) :
    amoPot α lam θ (n + k) = amoPot α lam (θ + (k : ℝ) * α) n := by
  simp only [amoPot]
  congr 2
  push_cast
  ring

/-- Covariance of the almost Mathieu family under the shift: `sh k * amoOp θ = amoOp (θ + kα) * sh k`. -/
theorem amoOp_covariance (α lam θ : ℝ) (k : ℤ) :
    Work.TMComp.Perfect.sh k * Work.TMComp.Perfect.amoOp α lam θ
      = Work.TMComp.Perfect.amoOp α lam (θ + (k : ℝ) * α) * Work.TMComp.Perfect.sh k := by
  refine ContinuousLinearMap.ext (fun f => ellTwo_ext (fun n => ?_))
  simp only [ContinuousLinearMap.mul_apply, amoOp_coord, sh_apply]
  rw [amoPot_shift α lam θ k n]
  have e1 : (n + k + 1 : ℤ) = n + 1 + k := by ring
  have e2 : (n + k - 1 : ℤ) = n - 1 + k := by ring
  rw [e1, e2]

end Work.TMComp.Perfect
