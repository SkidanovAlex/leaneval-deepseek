import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Norm.Defs
import Submission.Work.DSCOH.Norm.strictMono_del_apply_eq

namespace Work.DSCOH.Struct

/-- If `y` is nondecreasing but not strictly increasing, then deleting an entry strictly after
the last occurrence `frA2 y` of the first repeated value `frV y` still leaves a repeated value:
the two positions `frA y` and `frA y + 1` of `y` survive the deletion and carry the same value.
Hence `del y b` is not strictly increasing. -/
theorem del_not_strictMono_gt {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (Work.DSCOH.Norm.frA2 y hy hh : ℕ) < (b : ℕ)) :
    ¬ StrictMono (Work.DSCOH.Norm.del y b) := by
  intro hsm
  -- The two positions `frA y` and `frA y + 1` both carry `frV y`.
  have hsucc_spec : y (Work.DSCOH.Norm.frA y hy hh).succ = Work.DSCOH.Norm.frV y hy hh :=
    (Work.DSCOH.Norm.firstRepeat_spec y hy hh).symm
  -- `frA2 y` is the maximum of the positions carrying `frV y`, hence `frA y + 1 ≤ frA2 y`.
  have hle : (Work.DSCOH.Norm.frA y hy hh).succ ≤ Work.DSCOH.Norm.frA2 y hy hh := by
    have hmem : (Work.DSCOH.Norm.frA y hy hh).succ ∈
        Finset.univ.filter (fun i : Fin (k + 2) => y i = Work.DSCOH.Norm.frV y hy hh) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc_spec⟩
    unfold Work.DSCOH.Norm.frA2
    exact Finset.le_max' _ _ hmem
  -- Consequently both surviving positions are strictly before `b`.
  have hb_succ : ((Work.DSCOH.Norm.frA y hy hh).succ : ℕ) < (b : ℕ) :=
    lt_of_le_of_lt (Fin.le_def.mp hle) hb
  have hb_cast : ((Work.DSCOH.Norm.frA y hy hh).castSucc : ℕ) < (b : ℕ) := by
    rw [Fin.val_castSucc]; rw [Fin.val_succ] at hb_succ; omega
  have hne_cast : b ≠ (Work.DSCOH.Norm.frA y hy hh).castSucc := by
    intro h; rw [h] at hb_cast; exact lt_irrefl _ hb_cast
  have hne_succ : b ≠ (Work.DSCOH.Norm.frA y hy hh).succ := by
    intro h; rw [h] at hb_succ; exact lt_irrefl _ hb_succ
  -- A strictly increasing deletion would force the deleted position to be one of them.
  have hne : (Work.DSCOH.Norm.frA y hy hh).castSucc ≠ (Work.DSCOH.Norm.frA y hy hh).succ :=
    Fin.castSucc_lt_succ.ne
  have heq : y (Work.DSCOH.Norm.frA y hy hh).castSucc = y (Work.DSCOH.Norm.frA y hy hh).succ :=
    Work.DSCOH.Norm.firstRepeat_spec y hy hh
  rcases Work.DSCOH.Norm.strictMono_del_apply_eq hsm hne heq with h | h
  · exact hne_cast h
  · exact hne_succ h

end Work.DSCOH.Struct
