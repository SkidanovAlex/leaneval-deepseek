import Mathlib
import Submission.Work.CR.Flat.Polydisc

namespace Work.CR.Flat.Polydisc

/-- Scaling a polydisc: for `s > 0` the preimage under `z ↦ s • z` of the
polydisc with centre `s • c` and multiradii `r j * s` is the polydisc with
centre `c` and multiradii `r`. -/
theorem setOf_smul_mem_polydisc {n : ℕ} {s : ℝ} (hs : 0 < s) (c : Fin n → ℂ) (r : Fin n → ℝ) :
    {z : Fin n → ℂ | s • z ∈ Work.CR.Flat.polydisc (s • c) (fun j => r j * s)}
      = Work.CR.Flat.polydisc c r := by
  ext z
  simp only [Set.mem_ofPred_eq, Work.CR.Flat.mem_polydisc, Pi.smul_apply]
  constructor
  · intro h j
    have h1 := h j
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs.le, mul_comm (r j) s] at h1
    exact (mul_lt_mul_iff_of_pos_left hs).mp h1
  · intro h j
    have h1 := h j
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs.le, mul_comm (r j) s]
    exact (mul_lt_mul_iff_of_pos_left hs).mpr h1

end Work.CR.Flat.Polydisc
