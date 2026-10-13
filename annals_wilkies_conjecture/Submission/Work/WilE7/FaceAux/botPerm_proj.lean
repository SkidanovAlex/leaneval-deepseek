import Mathlib
import Submission.Work.WilE7.FaceAux.BotDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.FaceAux

open WilkiesDesign WilkiesDesign.E

/-- `botPerm` is the transposition of the coordinate `p` with the vertical coordinate
`botIdx p m`; any index strictly inside the base block `[0, p)` is fixed by it. -/
theorem botPerm_symm_of_val_lt {p m : ℕ} {j : Fin (botK p m)} (hj : (j : ℕ) < p) :
    (botPerm p m).symm j = j := by
  rw [botPerm, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne]
  · intro hcon
    have : (j : ℕ) = p := by simpa using congrArg Fin.val hcon
    omega
  · intro hcon
    have h2 : (j : ℕ) = (botIdx p m).val := congrArg Fin.val hcon
    rw [botIdx_val] at h2
    simp only [botN] at h2
    omega

/-- `botPerm` sends the coordinate `p` (the last coordinate of the base block) to the vertical
coordinate `botIdx p m`. -/
theorem botPerm_symm_of_val_eq {p m : ℕ} (j : Fin (botK p m)) (hj : (j : ℕ) = p) :
    (botPerm p m).symm j = botIdx p m := by
  rw [botPerm, Equiv.symm_swap]
  have h : j = (⟨p, by simp only [botK]; omega⟩ : Fin (botK p m)) :=
    Fin.ext (by simpa using hj)
  rw [h, Equiv.swap_apply_left]

/-- `botPinPt` on a base coordinate: the vertical index `-1` is out of the way, so the value is
just `x` at the corresponding base index. -/
theorem botPinPt_of_val_lt {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) {u : Fin (botK p m)}
    (h : (u : ℕ) < botN p m) : botPinPt x u = x ⟨(u : ℕ), h⟩ := by
  rw [botPinPt_apply, dite_eq_left h]

/-- **The coordinate permutation of the bottom face.**  Permuting the coordinates by `botPerm`
turns the pinned point of the base into `(x, -1)`: the first `p+1` coordinates of the permuted
pinned point are exactly `x` followed by `-1`. -/
theorem botPerm_proj {p m : ℕ} (x : Fin (p + (m + 1)) → ℝ) :
    WilkiesDesign.E.projFirst (p + 1) (m + 1)
        (fun j : Fin ((p + 1) + (m + 1)) =>
          Work.WilE7.FaceAux.botPinPt x ((Work.WilE7.FaceAux.botPerm p m).symm j))
      = Fin.snoc (WilkiesDesign.E.projFirst p (m + 1) x) (-1) := by
  funext i
  rw [projFirst]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
  · rw [hj]
    have hlt : (Fin.castAdd (m+1) j.castSucc : Fin (botK p m)).val < p := by
      rw [Fin.val_castAdd, Fin.val_castSucc]; exact j.isLt
    have hlt2 : (Fin.castAdd (m+1) j.castSucc : Fin (botK p m)).val < botN p m :=
      Nat.lt_of_lt_of_le hlt (Nat.le_add_right p (m+1))
    rw [botPerm_symm_of_val_lt hlt, Fin.snoc_castSucc, botPinPt_of_val_lt x hlt2]
    exact congrArg x (Fin.ext (by simp [Fin.val_castAdd, Fin.val_castSucc]))
  · rw [hlast]
    rw [botPerm_symm_of_val_eq (Fin.castAdd (m+1) (Fin.last p))
      (by rw [Fin.val_castAdd, Fin.val_last])]
    rw [Fin.snoc_last, botPinPt_idx]

end Work.WilE7.FaceAux
