import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs
import Submission.Work.DSCOH.Norm.Defs

namespace Work.DSCOH.Struct

open Work.DSCOH.Norm

/-- If `b` lies strictly to the right of the block of entries of `y` equal to `frV y`, then
deleting the `b`-th entry of `y` does not change the position of the first repeat: the first
repeat of `del y b` sits at `frA y`.

Concretely, `frA y ≤ frA2 y` are positions of the repeated value `frV y`, and `frA2 y < b`, so
both `frA y` and `frA y + 1` are `< b`; `del y b` agrees with `y` on all indices below `b`, whence
it has a repeat at `frA y` and, since any repeat of `del y b` at an index below `frA y` would
already be a repeat of `y`, `frA y` is again the first one. -/
theorem firstRepeat_del_gt {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (b : Fin (k + 2))
    (hb : (Work.DSCOH.Norm.frA2 y hy hh : ℕ) < (b : ℕ))
    (hns : ¬ StrictMono (Work.DSCOH.Norm.del y b)) :
    (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y b)
        (Work.DSCOH.Norm.monotone_del y b hy) hns).castSucc =
      Work.DSCOH.Norm.frA y hy hh := by
  set A := frA y hy hh with hA
  -- `A` is a position of the repeated value `frV y`: `y A.castSucc = y A.succ = frV y`.
  have hA_spec : y A.castSucc = y A.succ := firstRepeat_spec y hy hh
  have hfrV : frV y hy hh = y A.castSucc := rfl
  have hA_succ_frV : y A.succ = frV y hy hh := hA_spec.symm.trans hfrV.symm
  -- `frA2 y` is the last position carrying the value `frV y`, so `A.succ ≤ frA2 y`.
  have hmax : ∀ j : Fin (k + 2), y j = frV y hy hh → j ≤ frA2 y hy hh := by
    intro j hj
    unfold frA2
    exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  have hA2 : A.succ ≤ frA2 y hy hh := hmax A.succ hA_succ_frV
  have hA2v : A.val + 1 ≤ (frA2 y hy hh).val := by
    have := Fin.le_def.mp hA2
    simpa [Fin.val_succ] using this
  -- arithmetic: `A` and `A + 1` are both below `b`, and `A` is a valid position of `Fin k`.
  have hbA : A.val < (b : ℕ) := by have := b.isLt; omega
  have hbA1 : A.val + 1 < (b : ℕ) := by have := b.isLt; omega
  have hkA : A.val < k := by have := b.isLt; omega
  let a : Fin k := ⟨A.val, hkA⟩
  have ha_castSucc : (a.castSucc : Fin (k+1)) = A := Fin.ext rfl
  -- `del y b` has a repeat at the position `a` corresponding to `frA y`.
  have hrep : del y b a.castSucc = del y b a.succ := by
    have e1 : b.succAbove a.castSucc = A.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt b a.castSucc
        (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)]
      exact Fin.ext rfl
    have e2 : b.succAbove a.succ = A.succ := by
      rw [Fin.succAbove_of_castSucc_lt b a.succ
        (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)]
      exact Fin.ext rfl
    simp only [del_apply]
    rw [e1, e2]
    exact firstRepeat_spec y hy hh
  -- ... and any repeat of `del y b` sits at a position `≥ a`.
  have key : ∀ i : Fin k, del y b i.castSucc = del y b i.succ → a ≤ i := by
    intro i hi
    by_contra hcon
    -- assume `i` is a repeat of `del y b` strictly below `frA y`;
    -- then it is also a repeat of `y` below `frA y`, contradicting minimality.
    have hilt : i.val < A.val := by
      have h' := Fin.lt_def.mp (not_le.mp hcon)
      simpa [a] using h'
    have hi_lt_b : i.val < (b:ℕ) := by omega
    have hi_lt_b1 : i.val + 1 < (b:ℕ) := by omega
    have e1 : b.succAbove i.castSucc = (i.castSucc).castSucc :=
      Fin.succAbove_of_castSucc_lt b i.castSucc
        (by simp only [Fin.lt_def, Fin.val_castSucc]; omega)
    have e2 : b.succAbove i.succ = (i.succ).castSucc :=
      Fin.succAbove_of_castSucc_lt b i.succ
        (by simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)
    have hrep_y : y (i.castSucc).castSucc = y (i.castSucc).succ := by
      have h := hi
      simp only [del_apply] at h
      rw [e1, e2] at h
      have hp : (i.castSucc : Fin (k+1)).succ = (i.succ).castSucc :=
        Fin.ext (by simp [Fin.val_succ])
      rw [← hp] at h
      exact h
    have hle := firstRepeat_le y hy hh (i.castSucc) hrep_y
    have hle' : (firstRepeat y hy hh).val ≤ i.val := by
      have := Fin.le_def.mp hle
      simpa [Fin.val_castSucc] using this
    have : A.val ≤ i.val := by simpa [hA, frA] using hle'
    omega
  have hXa : firstRepeat (del y b) (monotone_del y b hy) hns ≤ a :=
    firstRepeat_le (del y b) (monotone_del y b hy) hns a hrep
  have haX : a ≤ firstRepeat (del y b) (monotone_del y b hy) hns :=
    key _ (firstRepeat_spec (del y b) (monotone_del y b hy) hns)
  have hXeq : firstRepeat (del y b) (monotone_del y b hy) hns = a := le_antisymm hXa haX
  rw [hXeq]
  exact ha_castSucc

end Work.DSCOH.Struct
