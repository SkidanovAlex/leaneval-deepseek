import Mathlib
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Norm

universe w

/-- If deleting the `b`-th entry of `x` leaves a strictly increasing tuple, then any two
distinct positions at which `x` takes the same value must include `b`: the only way `del x b`
can fail to see a repetition of `x` is if the repeated value sits at the deleted position. -/
theorem strictMono_del_apply_eq {ι : Type w} [LinearOrder ι] {n : ℕ} {x : Fin (n + 2) → ι}
    {b a a' : Fin (n + 2)} (hb : StrictMono (Work.DSCOH.Norm.del x b)) (haa' : a ≠ a')
    (h : x a = x a') : b = a ∨ b = a' := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨hba, hba'⟩ := hc
  -- both `a` and `a'` are in the range of `b.succAbove`
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (Ne.symm hba)
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hba')
  have hij : i ≠ j := by
    intro hijeq
    exact haa' (by rw [← hi, ← hj, hijeq])
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · -- `del x b i < del x b j` becomes `x a' < x a'`
    have h1 := hb hlt
    simp only [Work.DSCOH.Norm.del_apply, hi, hj, h] at h1
    exact absurd h1 (lt_irrefl _)
  · have h1 := hb hlt
    simp only [Work.DSCOH.Norm.del_apply, hi, hj, h] at h1
    exact absurd h1 (lt_irrefl _)

end Work.DSCOH.Norm
