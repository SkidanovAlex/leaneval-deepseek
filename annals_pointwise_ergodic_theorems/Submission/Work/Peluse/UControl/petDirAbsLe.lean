import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs2

/-!
# The uniform direction bound of a datum

`IdxDatum.dir_abs_leH` and its evaluated form `petDir_abs_leH` (rescued from the stale
`petChapter5_of_levelChainV2.lean`): the datum's direction `p_i(a)` is bounded on the box
`|a| ≤ H` by a constant **independent of `H`** times `H^(l-1)`.  The independence of `H` is what the
bookkeeping of `PetChapter5` needs (`Cne` is chosen before the datum's window), and `petDir_abs_leH`
supplies the `hShell` hypothesis of `petChapter5_of_levelChainV3_aux`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

/-- **The uniform direction bound.**  The direction of the datum is bounded by a constant depending
only on `(D, l, c)` times `H^j` on the box of radius `H`; the constant is *independent of `H`*
(which is what the bookkeeping of `PetChapter5` needs: `Cne` is chosen before the datum's window). -/
lemma IdxDatum.dir_abs_leH (D : IdxDatum) (l : ℕ) (c : ℤ) :
    ∀ j : ℕ, ∃ C : ℤ, 0 ≤ C ∧ ∀ (H : ℕ) (a : (i : ℕ) → D.S i → ℤ) (w : D.I j),
      (∀ i s, |a i s| ≤ (H : ℤ)) → |D.dir l c j w a| ≤ C * (H : ℤ) ^ j := by
  intro j
  induction j with
  | zero =>
    refine ⟨|c|, abs_nonneg c, ?_⟩
    intro H a w _
    have h0 : D.dir l c 0 w a = c := rfl
    rw [h0, pow_zero, mul_one]
  | succ k ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨(Fintype.card (D.S (k+1)) : ℤ) * |(l : ℤ) - (k : ℤ)| * C, ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg (Int.natCast_nonneg _) (abs_nonneg _)) hC
    · intro H a w ha
      rw [IdxDatum.dir]
      have hHK : (0 : ℤ) ≤ (H : ℤ) ^ k := pow_nonneg (Int.natCast_nonneg H) k
      have hHZ : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg H
      calc |∑ s ∈ w.val, ((l : ℤ) - (k : ℤ)) * D.dir l c k (D.par k s) a * a (k+1) s|
          ≤ ∑ s ∈ w.val,
              |((l : ℤ) - (k : ℤ)) * D.dir l c k (D.par k s) a * a (k+1) s| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ s ∈ w.val,
              |(l : ℤ) - (k : ℤ)| * |D.dir l c k (D.par k s) a| * |a (k+1) s| := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [abs_mul, abs_mul]
        _ ≤ ∑ _s ∈ w.val, |(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k) * (H : ℤ) := by
            refine Finset.sum_le_sum fun s _ => ?_
            have hd : |D.dir l c k (D.par k s) a| ≤ C * (H : ℤ) ^ k := hbound H a (D.par k s) ha
            have ha' : |a (k+1) s| ≤ (H : ℤ) := ha (k+1) s
            have hle : |(l : ℤ) - (k : ℤ)| * |D.dir l c k (D.par k s) a|
                ≤ |(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k) :=
              mul_le_mul_of_nonneg_left hd (abs_nonneg _)
            calc |(l : ℤ) - (k : ℤ)| * |D.dir l c k (D.par k s) a| * |a (k+1) s|
                ≤ (|(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k)) * (H : ℤ) :=
                  mul_le_mul hle ha' (abs_nonneg _)
                    (mul_nonneg (abs_nonneg _) (mul_nonneg hC hHK))
              _ = |(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k) * (H : ℤ) := by ring
        _ = (w.val.card : ℤ) * (|(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k) * (H : ℤ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card (D.S (k+1)) : ℤ)
              * (|(l : ℤ) - (k : ℤ)| * (C * (H : ℤ) ^ k) * (H : ℤ)) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast Finset.card_le_univ w.val
            · exact mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg hC hHK)) hHZ
        _ = (Fintype.card (D.S (k+1)) : ℤ) * |(l : ℤ) - (k : ℤ)| * C * (H : ℤ) ^ (k+1) := by
            rw [pow_succ]
            ring

/-- **The uniform `petDir` bound** (the shell bound of `PetChapter5`). -/
theorem petDir_abs_leH (D : IdxDatum) (l : ℕ) (hl : 1 ≤ l) (c : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : ℕ), 1 ≤ H →
      ∀ (a : D.Idx l) (i : Fin (Fintype.card (D.I (l - 1)))),
      a ∈ D.parBox l H → ((|petDir D l c a i| : ℤ) : ℝ) ≤ C * (H : ℝ) ^ (l - 1) := by
  obtain ⟨C, hC, hbound⟩ := D.dir_abs_leH l c (l - 1)
  refine ⟨(C : ℝ), by exact_mod_cast hC, ?_⟩
  intro H hH a i ha
  have hpad : ∀ j s, |(D.pad l a) j s| ≤ (H : ℤ) := by
    intro j s
    by_cases h : j < l
    · have hmem := (IdxDatum.mem_parBox.mp ha) ⟨j, h⟩ s
      show |(if h' : j < l then a ⟨j, h'⟩ s else 0)| ≤ (H : ℤ)
      rw [dif_pos h]
      exact abs_le.mpr hmem
    · show |(if h' : j < l then a ⟨j, h'⟩ s else 0)| ≤ (H : ℤ)
      rw [dif_neg h, abs_zero]
      exact Int.natCast_nonneg H
  show ((|D.dir l c (l - 1) ((Fintype.equivFin (D.I (l - 1))).symm i) (D.pad l a)| : ℤ) : ℝ)
      ≤ (C : ℝ) * (H : ℝ) ^ (l - 1)
  have hb := hbound H (D.pad l a) ((Fintype.equivFin (D.I (l - 1))).symm i) hpad
  have h2 : (((|D.dir l c (l - 1) ((Fintype.equivFin (D.I (l - 1))).symm i) (D.pad l a)| : ℤ)) : ℝ)
      ≤ ((C * (H : ℤ) ^ (l - 1) : ℤ) : ℝ) := by exact_mod_cast hb
  have h3 : ((C * (H : ℤ) ^ (l - 1) : ℤ) : ℝ) = (C : ℝ) * (H : ℝ) ^ (l - 1) := by
    push_cast; ring
  linarith [h2, h3.le, h3.ge]



end

end Work.Peluse.UControl
