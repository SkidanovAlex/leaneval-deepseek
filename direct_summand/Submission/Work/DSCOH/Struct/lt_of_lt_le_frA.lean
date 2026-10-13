import Mathlib
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.HomoDefs

namespace Work.DSCOH.Struct

theorem lt_of_lt_le_frA {k : ℕ} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy : Monotone y) (hh : ¬ StrictMono y) (i j : Fin (k + 2))
    (h : (i : ℕ) < (j : ℕ)) (hj : (j : ℕ) ≤ (Work.DSCOH.Norm.frA y hy hh : ℕ)) :
    y i < y j := by
  -- Positions strictly before the first repeat step up strictly.
  have hstep : ∀ m : Fin (k + 1), m < Work.DSCOH.Norm.frA y hy hh → y m.castSucc < y m.succ := by
    intro m hm
    rcases lt_or_eq_of_le (hy (Fin.castSucc_le_succ m)) with hlt | heq
    · exact hlt
    · exact absurd (Work.DSCOH.Norm.firstRepeat_le y hy hh m heq) (not_le.mpr hm)
  -- Hence `y` is strictly increasing up to (and including) the first repeat.
  have key : ∀ j : Fin (k + 2), (j : ℕ) ≤ (Work.DSCOH.Norm.frA y hy hh : ℕ) →
      ∀ i : Fin (k + 2), (i : ℕ) < (j : ℕ) → y i < y j :=
    Fin.induction
      (motive := fun j : Fin (k + 2) => (j : ℕ) ≤ (Work.DSCOH.Norm.frA y hy hh : ℕ) →
        ∀ i : Fin (k + 2), (i : ℕ) < (j : ℕ) → y i < y j)
      (fun _ i hi => by simp only [Fin.val_zero] at hi; omega)
      (fun m ihm => by
        intro hj i hi
        simp only [Fin.val_succ] at hj hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
        · have hm : m < Work.DSCOH.Norm.frA y hy hh := by simp only [Fin.lt_def]; omega
          exact lt_trans
            (ihm (by simp only [Fin.val_castSucc]; omega) i
              (by simp only [Fin.val_castSucc]; omega))
            (hstep m hm)
        · have hieq : i = m.castSucc := Fin.ext (by simp only [Fin.val_castSucc]; omega)
          rw [hieq]
          exact hstep m (by simp only [Fin.lt_def]; omega))
  exact key j hj i h

end Work.DSCOH.Struct
