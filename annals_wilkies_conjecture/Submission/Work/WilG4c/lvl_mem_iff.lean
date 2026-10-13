import Mathlib
import Submission.Work.WilG4c.CellParamDefs
import Submission.Work.WilG4c.prefl_mem_lvl
import Submission.Work.WilG4c.exists_prefl_aux

namespace Work.WilG4c

set_option autoImplicit false

/-- The trailing part of a point `z : ℝ^{p+N}` below level `m`: the coordinates
`p+m, …, p+N-1`, indexed by `Fin (N-m)` (so the `j`-th coordinate of the result is the
coordinate `p+m+j` of `z`).  This is the canonical `w` such that `gluePt p N m hm (prefl m hm z) w = z`. -/
def sufPt (p N m : ℕ) (z : Fin (p+N) → ℝ) : Fin (N-m) → ℝ :=
  fun j => z ⟨p+m+j.val, by omega⟩

theorem sufPt_apply (p N m : ℕ) (z : Fin (p+N) → ℝ) (j : Fin (N-m)) :
    sufPt p N m z j = z ⟨p+m+j.val, by omega⟩ := rfl

/-- `gluePt` keeps the prefix: the first `p+m` coordinates of a glued point form the original
level-`m` point. -/
theorem prefl_gluePt (p N m : ℕ) (hm : m ≤ N) (x : Fin (p+m) → ℝ) (w : Fin (N-m) → ℝ) :
    prefl m hm (gluePt p N m hm x w) = x := by
  funext i
  rw [prefl_apply]
  exact gluePt_idxL p N m hm x w i

/-- Reassembly: a point of `ℝ^{p+N}` is the gluing of its level-`m` prefix with its tail. -/
theorem gluePt_prefl_sufPt (p N m : ℕ) (hm : m ≤ N) (z : Fin (p+N) → ℝ) :
    gluePt p N m hm (prefl m hm z) (sufPt p N m z) = z := by
  funext i
  rw [gluePt]
  split_ifs with h
  · show z ⟨i.val, _⟩ = z i
    exact congrArg z (Fin.ext rfl)
  · show z ⟨p + m + (i.val - (p + m)), _⟩ = z i
    have hv : p + m + (i.val - (p + m)) = i.val := by omega
    exact congrArg z (Fin.ext hv)

theorem lvl_mem_iff (p N : ℕ) (κ : Set (Fin (p+N) → ℝ)) (m : ℕ) (hm : m ≤ N)
    (x : Fin (p+m) → ℝ) :
    x ∈ Work.WilG4c.lvl p N κ m ↔
      ∃ w : Fin (N-m) → ℝ, Work.WilG4c.gluePt p N m hm x w ∈ κ := by
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := exists_prefl_aux p N κ m hm x hx
    refine ⟨sufPt p N m z, ?_⟩
    rw [← hzx, gluePt_prefl_sufPt]
    exact hz
  · rintro ⟨w, hw⟩
    have hpre := prefl_gluePt p N m hm x w
    rw [← hpre]
    exact prefl_mem_lvl p N κ m hm (gluePt p N m hm x w) hw

end Work.WilG4c
