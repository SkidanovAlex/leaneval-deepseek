import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPCore.Flow

/-- Composing two `2π`-shifts of the angle `q₂` (`l` first, then `k`). -/
private theorem Tk_comp (k l : ℤ) (x : Work.RPV.PS) :
    Work.RPV.Tk k (Work.RPV.Tk l x) = Work.RPV.Tk (l + k) x := by
  ext <;> simp only [Work.RPV.Tk]; push_cast; ring

/-- The shift by `0` is the identity. -/
private theorem Tk_zero_self (x : Work.RPV.PS) : Work.RPV.Tk (0 : ℤ) x = x := by
  simp [Work.RPV.Tk]

/-- A function on `ℝ × PS` which is invariant under the `2π`-shift of the angle `q₂` is
invariant under `Tk m` for every integer `m`. -/
theorem periodic_Tk_int {V : Type*} (f : ℝ × Work.RPV.PS → V)
    (hper : ∀ z, f (z.1, Work.RPV.Tk 1 z.2) = f z) (m : ℤ) (t : ℝ) (x : Work.RPV.PS) :
    f (t, Work.RPV.Tk m x) = f (t, x) := by
  have key : ∀ k : ℤ, f (t, Work.RPV.Tk 1 (Work.RPV.Tk k x)) = f (t, Work.RPV.Tk k x) :=
    fun k => hper (t, Work.RPV.Tk k x)
  induction m using Int.induction_on with
  | zero => simp [Tk_zero_self]
  | succ i ih =>
      have h := key (i : ℤ)
      rw [Tk_comp] at h
      exact h.trans ih
  | pred i ih =>
      have h := key (-(i : ℤ) - 1)
      rw [Tk_comp] at h
      rw [show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring] at h
      exact h.symm.trans ih

end Work.RPCore.Flow
