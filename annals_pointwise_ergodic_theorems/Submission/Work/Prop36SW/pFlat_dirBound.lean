import Mathlib
import Submission.Work.Prop36SW.dirBound
import Submission.Work.Peluse.Prop36SW.roundDefs

namespace Work.Prop36SW

/-!
# The size of the flat slot coefficient `pFlat` on the closed box

`pFlat D d c m Λ s x = Λ · (d - m) · dir d c m (par m s) (pad (m+1) (decD D (m+1) x))` is the
signed slot coefficient of the chain at slot level `m`, read at the flat parameter `x`.  On the
closed box `Abox D (m+1) H` (i.e. as soon as the decoded family `decD D (m+1) x` runs through the
parameter box `(-H,H)^{Σ_{j<m+1}|S j|}`), its absolute value is bounded by the level-`m` direction
bound `dirBound` of `Submission/Work/Prop36SW/dirBound.lean`, transported along the decoding — this
is the input the Schwartz–Zippel/round estimates need for the coefficient's sup-norm.
-/

theorem pFlat_dirBound (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (m Λ : ℕ) (H Cd : ℕ)
    (hCd : ∀ j : ℕ, j ≤ m → Fintype.card (D.S j) ≤ Cd) :
    ∀ (s : D.S (m + 1)) (x : Fin (Work.Peluse.Prop36SW.nD D (m + 1)) → ℤ),
      x ∈ Work.Peluse.Prop36SW.Abox D (m + 1) H →
      |Work.Peluse.Prop36SW.pFlat D d c m Λ s x| ≤ (Λ : ℤ) * |(d : ℤ) - (m : ℤ)|
        * (|c| * (Nat.factorial d : ℤ) * ((Cd : ℤ) + 1) ^ m * ((H : ℤ) + 1) ^ m) := by
  intro s x hx
  have hbox : Work.Peluse.Prop36SW.decD D (m + 1) x ∈ D.parBox (m + 1) H :=
    Work.Peluse.Prop36SW.decD_mem_parBox_of_mem_Abox hx
  rw [Work.Peluse.UControl.IdxDatum.mem_parBox] at hbox
  have ha : ∀ j' : ℕ, j' ≤ m → ∀ s' : D.S j',
      -(H : ℤ) ≤ (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x)) j' s' ∧
      (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x)) j' s' ≤ (H : ℤ) := by
    intro j' hj' s'
    have hlt : j' < m + 1 := by omega
    have hpad : (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x)) j' s'
        = (Work.Peluse.Prop36SW.decD D (m + 1) x) ⟨j', hlt⟩ s' := by
      simp [Work.Peluse.UControl.IdxDatum.pad, hlt]
    rw [hpad]
    exact hbox ⟨j', hlt⟩ s'
  have hdir := Work.Prop36SW.dirBound D d c m H Cd (D.par m s)
    (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x)) hCd ha
  rw [Work.Peluse.Prop36SW.pFlat]
  calc |(Λ : ℤ) * ((d : ℤ) - (m : ℤ)) *
        D.dir d c m (D.par m s) (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x))|
      = (Λ : ℤ) * |(d : ℤ) - (m : ℤ)| *
        |D.dir d c m (D.par m s)
          (D.pad (m + 1) (Work.Peluse.Prop36SW.decD D (m + 1) x))| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Int.natCast_nonneg Λ)]
    _ ≤ (Λ : ℤ) * |(d : ℤ) - (m : ℤ)|
          * (|c| * (Nat.factorial d : ℤ) * ((Cd : ℤ) + 1) ^ m * ((H : ℤ) + 1) ^ m) :=
        mul_le_mul_of_nonneg_left hdir (by positivity)

end Work.Prop36SW
