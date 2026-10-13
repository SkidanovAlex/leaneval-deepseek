import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

namespace Work.WilG4c

open Work.WilG0

/-! ## The glueing map `snocIt` versus `Fin.append` / `Fin.snoc`

`AlBadPar p n f L` projects `AlBad p n f L ⊆ ℝ^{p+(n+1)+1}` onto the first `p` coordinates
by an explicit existential over the block of `n+1` cube coordinates followed by the single
last coordinate.  The iterate `projLastIter p (n+2)` projects the last `n+2` coordinates away
one at a time; its description (`projLastIter_eq`) uses the glueing map `snocIt`.  The two
descriptions agree because `snocIt p (n+2)` glues `l` and `w` with `Fin.append` and `Fin.snoc`.
-/

/-- `snocIt` is exactly `Fin.append`: it puts the first block of coordinates in front and the
second block behind. -/
theorem snocIt_eq_append (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    snocIt n m x w = Fin.append x w := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i; rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  · intro j; rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- The successor unfolding of `snocIt`. -/
theorem snocIt_succ (n m : ℕ) (x : Fin n → ℝ) (w : Fin (m + 1) → ℝ) :
    snocIt n (m + 1) x w = Fin.snoc (snocIt n m x (Fin.init w)) (w (Fin.last m)) := by
  rw [snocIt.eq_def]

/-- `snocIt p (n+2) l w` is `Fin.snoc (Fin.append l (Fin.init w)) (w (last))`: the first `p`
coordinates are `l`, then the rest of `w`. -/
theorem snocIt_init_last (p n : ℕ) (l : Fin p → ℝ) (w : Fin (n + 2) → ℝ) :
    snocIt p (n + 2) l w =
      Fin.snoc (Fin.append l (Fin.init w)) (w (Fin.last (n + 1))) := by
  rw [snocIt_succ, snocIt_eq_append]

/-- `snocIt p (n+2)` of a vector glued as `Fin.snoc u s`: this is `Fin.snoc (Fin.append l u) s`.
This is the form appearing in the definition of `AlBadPar`. -/
theorem snocIt_two (p n : ℕ) (l : Fin p → ℝ) (u : Fin (n + 1) → ℝ) (s : ℝ) :
    snocIt p (n + 2) l (Fin.snoc u s) = Fin.snoc (Fin.append l u) s := by
  rw [snocIt_succ, Fin.init_snoc, Fin.snoc_last, snocIt_eq_append]

theorem AlBadParProj (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Work.WilkG4c.AlBadPar p n f L =
      Work.WilG0.projLastIter p (n + 2) (Work.WilkG4c.AlBad p n f L) := by
  rw [Work.WilG0.projLastIter_eq]
  ext l
  simp only [Work.WilkG4c.AlBadPar, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, s, hs⟩
    exact ⟨Fin.snoc u s, by rw [snocIt_two]; exact hs⟩
  · rintro ⟨w, hw⟩
    exact ⟨Fin.init w, w (Fin.last (n + 1)), by simpa [snocIt_init_last] using hw⟩

end Work.WilG4c
