import Mathlib
import Submission.Work.Prop36SW.pFlat_dirBound
import Submission.Work.Prop36SW.roundToNextDefs

namespace Work.Prop36SW

/-!
# The flat bound for the top slot coefficient `slotCoeff D d c (d-2)`

At the top slot level `j = d - 2` the slot coefficient is
`slotCoeff D d c (d-2) s a = (d - (d-2)) · dir d c (d-2) (par (d-2) s) a = 2 · dir d c (d-2) …`,
so on the parameter box `D.parBox ((d-2)+1) H` it is controlled by the level-`d-2` direction bound
`Work.Prop36SW.dirBound` with `Cd := sSup D d` (the crude sum of the slot counts).  Multiplying by
the two window factors `(H+1)²` and using `d = (d-2) + 2` gives the stated bound, which is exactly the
shape the round-by-round chain consumes as its coefficient hypothesis.
-/

theorem slotCoeffFlatBoundMul (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (H : ℕ)
    (hd : 2 ≤ d) :
    ∀ (s : D.S ((d - 2) + 1)) (a : D.Idx ((d - 2) + 1)), a ∈ D.parBox ((d - 2) + 1) H →
      |Work.Peluse.slotCoeff D d c (d - 2) s (D.pad ((d - 2) + 1) a)|
          * ((H : ℤ) + 1) * ((H : ℤ) + 1)
        ≤ 2 * |c| * (Nat.factorial d : ℤ) * ((Work.Prop36SW.sSup D d : ℤ) + 1) ^ (d - 2)
            * ((H : ℤ) + 1) ^ d := by
  intro s a ha
  rw [Work.Peluse.UControl.IdxDatum.mem_parBox] at ha
  -- the padded parameter family is bounded on every level `j' ≤ d - 2`
  have hpad : ∀ (j' : ℕ), j' ≤ d - 2 → ∀ s' : D.S j',
      -(H : ℤ) ≤ D.pad ((d - 2) + 1) a j' s' ∧ D.pad ((d - 2) + 1) a j' s' ≤ (H : ℤ) := by
    intro j' hj' s'
    have hlt : j' < (d - 2) + 1 := by omega
    have hval : D.pad ((d - 2) + 1) a j' s' = a ⟨j', hlt⟩ s' := by
      simp only [Work.Peluse.UControl.IdxDatum.pad]
      rw [dif_pos hlt]
    rw [hval]
    exact ha ⟨j', hlt⟩ s'
  -- `sSup D d` bounds every slot count at a level `≤ d`
  have hCd : ∀ (j' : ℕ), j' ≤ d - 2 → Fintype.card (D.S j') ≤ sSup D d :=
    fun j' hj' => card_le_sSup D (by omega)
  have hdir := dirBound D d c (d - 2) H (sSup D d) (D.par (d - 2) s)
    (D.pad ((d - 2) + 1) a) hCd hpad
  -- the top slot coefficient is twice the level-`d-2` direction
  have hsc : Work.Peluse.slotCoeff D d c (d - 2) s (D.pad ((d - 2) + 1) a)
      = 2 * D.dir d c (d - 2) (D.par (d - 2) s) (D.pad ((d - 2) + 1) a) := by
    rw [Work.Peluse.slotCoeff]
    have hc2 : ((d - 2 : ℕ) : ℤ) = (d : ℤ) - 2 := Nat.cast_sub (R := ℤ) hd
    rw [hc2]
    ring
  have hb : |Work.Peluse.slotCoeff D d c (d - 2) s (D.pad ((d - 2) + 1) a)|
      ≤ 2 * (|c| * (Nat.factorial d : ℤ) * ((sSup D d : ℤ) + 1) ^ (d - 2)
          * ((H : ℤ) + 1) ^ (d - 2)) := by
    rw [hsc, abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hdir (by norm_num)
  have hdd : d - 2 + 2 = d := by omega
  have hpow : ((H : ℤ) + 1) ^ d = ((H : ℤ) + 1) ^ (d - 2) * ((H : ℤ) + 1) ^ 2 := by
    conv_lhs => rw [← hdd]
    rw [pow_add]
  calc |Work.Peluse.slotCoeff D d c (d - 2) s (D.pad ((d - 2) + 1) a)|
        * ((H : ℤ) + 1) * ((H : ℤ) + 1)
      ≤ (2 * (|c| * (Nat.factorial d : ℤ) * ((sSup D d : ℤ) + 1) ^ (d - 2)
          * ((H : ℤ) + 1) ^ (d - 2))) * ((H : ℤ) + 1) * ((H : ℤ) + 1) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity))
          (by positivity)
    _ = 2 * |c| * (Nat.factorial d : ℤ) * ((sSup D d : ℤ) + 1) ^ (d - 2)
          * ((H : ℤ) + 1) ^ d := by
        rw [hpow]; ring

end Work.Prop36SW
