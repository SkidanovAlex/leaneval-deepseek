import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

/-- `T̃⁻¹ ∘ T̃ = id`. -/
theorem psiFlatL_phiArrL (r : ℕ) (ts' : List ℕ) (hr : 0 < r)
    (w : Fin ((ts' ++ [r]).prod) → ℂ) :
    Work.Transform.psiFlatL r ts' (Work.Transform.phiArrL r ts' w) = w := by
  funext i
  simp only [Work.Transform.psiFlatL, Work.Transform.phiArrL]
  -- `ψ` reads the flattened index `i` back as `(i / r, i % r)`.
  have hval : (i : ℕ) / r * r + (i : ℕ) % r = (i : ℕ) := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
  have hidx : (⟨(i : ℕ) / r * r + (i : ℕ) % r, by rw [hval]; exact i.isLt⟩ :
      Fin ((ts' ++ [r]).prod)) = i := by
    apply Fin.ext; exact hval
  rw [hidx, inv_mul_cancel_left₀ (Work.Transform.zeta_ne_zero r _) _]

end Work.Transform
