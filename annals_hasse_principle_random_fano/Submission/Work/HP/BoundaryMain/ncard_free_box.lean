import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.BoundaryMain.ncard_Sset
import Submission.Work.HP.BoundaryMain.ncard_free_coords

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.HP.BoundaryMain

open Work.HP

/-- The "free box" `{g : Mon d n → ℤ | g = 0 on the n+1 special monomials, |g| ≤ A off them}`
is finite, and has at most `(2A+1)^{N_{d,n} - (n+1)}` elements: there are `NN d n - (n+1)` free
coordinates, each with at most `2⌊A⌋+1 ≤ 2A+1` possible values. -/
theorem ncard_free_box (d n : ℕ) (hd : 1 ≤ d) (j : Fin (n + 1)) (A : ℝ) (hA : 1 ≤ A) :
    ({g : Work.HP.Mon d n → ℤ | (∀ m, m ∈ Work.HP.Sset d n hd j → g m = 0) ∧
        (∀ m, m ∉ Work.HP.Sset d n hd j → |g m| ≤ (Nat.floor A : ℤ))} :
        Set (Work.HP.Mon d n → ℤ)).Finite ∧
    ((({g : Work.HP.Mon d n → ℤ | (∀ m, m ∈ Work.HP.Sset d n hd j → g m = 0) ∧
        (∀ m, m ∉ Work.HP.Sset d n hd j → |g m| ≤ (Nat.floor A : ℤ))} :
        Set (Work.HP.Mon d n → ℤ)).ncard : ℝ)
      ≤ (2 * A + 1) ^ (Work.HP.NN d n - (n + 1))) := by
  obtain ⟨hfin, hle⟩ := ncard_free_coords (Sset d n hd j) (Nat.floor A)
  refine ⟨hfin, ?_⟩
  have hc2 : (Sset d n hd j)ᶜ.ncard = NN d n - (n + 1) := (ncard_Sset d n hd j).2
  have hle' : ({g : Mon d n → ℤ | (∀ m, m ∈ Sset d n hd j → g m = 0) ∧
      (∀ m, m ∉ Sset d n hd j → |g m| ≤ (Nat.floor A : ℤ))} :
      Set (Mon d n → ℤ)).ncard ≤ (2 * Nat.floor A + 1) ^ (NN d n - (n + 1)) := by
    rw [hle, hc2]
  have h0 : (0 : ℝ) ≤ A := by linarith
  have hfl := Nat.floor_le h0
  calc (({g : Mon d n → ℤ | (∀ m, m ∈ Sset d n hd j → g m = 0) ∧
        (∀ m, m ∉ Sset d n hd j → |g m| ≤ (Nat.floor A : ℤ))} :
        Set (Mon d n → ℤ)).ncard : ℝ)
      ≤ (((2 * Nat.floor A + 1) ^ (NN d n - (n + 1)) : ℕ) : ℝ) := by exact_mod_cast hle'
    _ = ((2 * Nat.floor A + 1 : ℕ) : ℝ) ^ (NN d n - (n + 1)) := by push_cast; ring
    _ ≤ (2 * A + 1) ^ (NN d n - (n + 1)) := by
        gcongr
        push_cast
        linarith

end Work.HP.BoundaryMain
