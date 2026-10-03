import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily

/-!
# The size of a direction `A_j` as a polynomial in the datum

`IdxDatum.dir D d c j i a` evaluates the direction `A_j` at the parameter family `a`.  Its recursion

`dir D d c 0 _ _ = c`, `dir D d c (j+1) w a = ∑_{s ∈ w} ((d - j) · dir D d c j (par j s) a) · a (j+1) s`

shows that `dir D d c j i a` is an integral polynomial of degree `j` in the parameters
`a 1 s, …, a j s`, with coefficients built from `c`, the descending factorials of `d` and the
cardinalities `|S j'|`.  The lemma `dirBound_aux` below records the resulting *coarse* bound with the
descending factorial `d(d-1)⋯(d-j+1)` (which vanishes for `j > d`), and `dirBound` specialises it
to `d!` using `d(d-1)⋯(d-j+1) ≤ d!`.

The bound is what makes the direction polynomial `dirPolyMv` bounded uniformly on the parameter box.
-/

namespace Work.Prop36SW

open Work.Peluse.UControl

/-- The descending factorial of `d` (of any length) is at most `d!`. -/
lemma nat_descFactorial_le_factorial (d j : ℕ) : Nat.descFactorial d j ≤ d.factorial := by
  rcases le_or_gt j d with h | h
  · calc Nat.descFactorial d j ≤ (d - j).factorial * Nat.descFactorial d j :=
        Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
      _ = d.factorial := Nat.factorial_mul_descFactorial h
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    exact Nat.zero_le _

/-- `|d - j|` times the descending factorial `d(d-1)⋯(d-j+1)` is the descending factorial of
length `j+1`. -/
lemma abs_int_sub_mul_descFactorial (d j : ℕ) :
    |(d : ℤ) - (j : ℤ)| * (Nat.descFactorial d j : ℤ) = (Nat.descFactorial d (j + 1) : ℤ) := by
  rcases le_or_gt j d with h | h
  · have hnonneg : (0 : ℤ) ≤ (d : ℤ) - (j : ℤ) := by
      have hc : ((d - j : ℕ) : ℤ) = (d : ℤ) - (j : ℤ) := Nat.cast_sub h
      rw [← hc]
      exact Nat.cast_nonneg _
    rw [abs_of_nonneg hnonneg, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub h]
  · have hz : Nat.descFactorial d j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
    have hz' : Nat.descFactorial d (j + 1) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hz, hz']
    simp

/-- **The size of a direction.**  If every slot type `D.S j'`, `j' ≤ j`, has at most `Cd` elements
and every parameter `a j' s` lies in `[-H, H]`, then the level-`j` direction is bounded by
`|c| · d(d-1)⋯(d-j+1) · (Cd+1)^j · (H+1)^j`. -/
theorem dirBound_aux (D : IdxDatum) (d : ℕ) (c : ℤ) (H Cd : ℕ)
    (a : (j' : ℕ) → D.S j' → ℤ) :
    ∀ j : ℕ,
      (∀ j' : ℕ, j' ≤ j → Fintype.card (D.S j') ≤ Cd) →
      (∀ j' : ℕ, j' ≤ j → ∀ s : D.S j', -(H : ℤ) ≤ a j' s ∧ a j' s ≤ (H : ℤ)) →
      ∀ i : D.I j,
        |D.dir d c j i a| ≤
          |c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j := by
  intro j
  induction j with
  | zero =>
    intro hCd ha i
    rw [IdxDatum.dir]
    simp
  | succ j ih =>
    intro hCd ha w
    have hCd' : ∀ j' : ℕ, j' ≤ j → Fintype.card (D.S j') ≤ Cd :=
      fun j' hj' => hCd j' (by omega)
    have ha' : ∀ j' : ℕ, j' ≤ j → ∀ s : D.S j', -(H : ℤ) ≤ a j' s ∧ a j' s ≤ (H : ℤ) :=
      fun j' hj' s => ha j' (by omega) s
    rw [IdxDatum.dir]
    have hstep : ∀ s ∈ w.val,
        |((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s) a * a (j + 1) s| ≤
          |(d : ℤ) - (j : ℤ)|
            * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j)
            * ((H : ℤ) + 1) := by
      intro s _
      have hdir : |D.dir d c j (D.par j s) a| ≤
          |c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j :=
        ih hCd' ha' (D.par j s)
      have ha_s : |a (j + 1) s| ≤ (H : ℤ) + 1 := by
        obtain ⟨h1, h2⟩ := ha (j + 1) (le_refl _) s
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hdir (abs_nonneg _)) ha_s (abs_nonneg _)
        (by positivity)
    calc |∑ s ∈ w.val, ((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s) a * a (j + 1) s|
        ≤ ∑ s ∈ w.val,
            |((d : ℤ) - (j : ℤ)) * D.dir d c j (D.par j s) a * a (j + 1) s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ w.val,
            |(d : ℤ) - (j : ℤ)|
              * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j)
              * ((H : ℤ) + 1) := Finset.sum_le_sum hstep
      _ = (w.val.card : ℤ)
              * (|(d : ℤ) - (j : ℤ)|
                  * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j
                      * ((H : ℤ) + 1) ^ j)
                  * ((H : ℤ) + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ |c| * (Nat.descFactorial d (j + 1) : ℤ) * ((Cd : ℤ) + 1) ^ (j + 1)
            * ((H : ℤ) + 1) ^ (j + 1) := by
          have hcard : (w.val.card : ℤ) ≤ (Cd : ℤ) := by
            have h1 : w.val.card ≤ Fintype.card (D.S (j + 1)) := Finset.card_le_univ _
            have h2 : Fintype.card (D.S (j + 1)) ≤ Cd := hCd (j + 1) (le_refl _)
            exact_mod_cast le_trans h1 h2
          have hY : (0 : ℤ) ≤ |(d : ℤ) - (j : ℤ)|
              * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j)
              * ((H : ℤ) + 1) := by positivity
          calc (w.val.card : ℤ)
                * (|(d : ℤ) - (j : ℤ)|
                    * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j
                        * ((H : ℤ) + 1) ^ j)
                    * ((H : ℤ) + 1))
              ≤ (Cd : ℤ)
                * (|(d : ℤ) - (j : ℤ)|
                    * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j
                        * ((H : ℤ) + 1) ^ j)
                    * ((H : ℤ) + 1)) := mul_le_mul_of_nonneg_right hcard hY
            _ ≤ ((Cd : ℤ) + 1)
                * (|(d : ℤ) - (j : ℤ)|
                    * (|c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j
                        * ((H : ℤ) + 1) ^ j)
                    * ((H : ℤ) + 1)) :=
                mul_le_mul_of_nonneg_right (by omega) hY
            _ = |c| * (Nat.descFactorial d (j + 1) : ℤ) * ((Cd : ℤ) + 1) ^ (j + 1)
                  * ((H : ℤ) + 1) ^ (j + 1) := by
                rw [pow_succ, pow_succ, ← abs_int_sub_mul_descFactorial]
                ring

/-- **Bound on the directions.** -/
theorem dirBound (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (j H Cd : ℕ)
    (i : D.I j) (a : (j' : ℕ) → D.S j' → ℤ)
    (hCd : ∀ j' : ℕ, j' ≤ j → Fintype.card (D.S j') ≤ Cd)
    (ha : ∀ j' : ℕ, j' ≤ j → ∀ s : D.S j', -(H : ℤ) ≤ a j' s ∧ a j' s ≤ (H : ℤ)) :
    |D.dir d c j i a| ≤ |c| * (Nat.factorial d : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j := by
  have h := dirBound_aux D d c H Cd a j hCd ha i
  have hdf : (Nat.descFactorial d j : ℤ) ≤ (Nat.factorial d : ℤ) := by
    exact_mod_cast nat_descFactorial_le_factorial d j
  have hp : (0 : ℤ) ≤ ((Cd : ℤ) + 1) ^ j := by positivity
  have hq : (0 : ℤ) ≤ ((H : ℤ) + 1) ^ j := by positivity
  refine le_trans h ?_
  calc |c| * (Nat.descFactorial d j : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j
      = (|c| * (Nat.descFactorial d j : ℤ))
          * (((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j) := by ring
    _ ≤ (|c| * (Nat.factorial d : ℤ))
          * (((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdf (abs_nonneg c))
          (mul_nonneg hp hq)
    _ = |c| * (Nat.factorial d : ℤ) * ((Cd : ℤ) + 1) ^ j * ((H : ℤ) + 1) ^ j := by ring

end Work.Prop36SW
