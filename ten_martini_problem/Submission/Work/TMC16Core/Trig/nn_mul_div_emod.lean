import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist

namespace Work.TMC16Core.Trig

open Work.TMC16Core.Basic

/-- `nn` only sees the argument modulo integers: adding an integer does not change it. -/
lemma nn_add_intCast' (w : ℝ) (m : ℤ) : nn (w + (m : ℝ)) = nn w := nn_add_intCast w m

/-- For `0 < q`, `k * (p/q)` differs from `((k*p) % q)/q` by an integer:
`k * (p/q) = ((k*p) % q)/q + (k*p)/q`. -/
lemma mul_div_sub_emod_div {q : ℕ} (hq : 0 < q) (p : ℤ) (k : ℕ) :
    (k : ℝ) * ((p : ℝ) / (q : ℝ))
      = ((((k : ℤ) * p) % q : ℤ) : ℝ) / (q : ℝ) + ((((k : ℤ) * p) / q : ℤ) : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
    exact_mod_cast this
  have hk : (k : ℝ) * ((p : ℝ) / (q : ℝ)) = (((k : ℤ) * p : ℤ) : ℝ) / (q : ℝ) := by
    push_cast
    ring
  have hcast : (((k : ℤ) * p : ℤ) : ℝ)
      = ((((k : ℤ) * p) % q : ℤ) : ℝ) + (q : ℝ) * ((((k : ℤ) * p) / q : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ))
      (Int.emod_add_mul_ediv ((k : ℤ) * p) (q : ℤ))
    push_cast at h
    simpa using h.symm
  have hmod : (((k : ℤ) * p : ℤ) : ℝ) / (q : ℝ)
      = ((((k : ℤ) * p) % q : ℤ) : ℝ) / (q : ℝ) + ((((k : ℤ) * p) / q : ℤ) : ℝ) := by
    rw [hcast]
    rw [add_div]
    congr 1
    rw [mul_div_cancel_left₀ _ hqR]
  rw [hk, hmod]

theorem nn_mul_div_emod {q : ℕ} (hq : 0 < q) (p : ℤ) (x : ℝ) (k : ℕ) :
    Work.TMC16Core.Basic.nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) =
      Work.TMC16Core.Basic.nn (2 * x + ((((k : ℤ) * p) % q : ℤ) : ℝ) / (q : ℝ)) := by
  have h := mul_div_sub_emod_div hq p k
  have harg : 2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))
      = (2 * x + ((((k : ℤ) * p) % q : ℤ) : ℝ) / (q : ℝ))
        + ((((k : ℤ) * p) / q : ℤ) : ℝ) := by
    rw [h]; ring
  rw [harg, nn_add_intCast]

end Work.TMC16Core.Trig
