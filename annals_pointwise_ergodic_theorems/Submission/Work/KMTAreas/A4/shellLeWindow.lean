import Mathlib

set_option linter.unusedVariables false

namespace Work.KMTAreas.A4

/-!
# `shellLeWindow`: the ℓ¹-counting bound for the shell `D < |y + q·m|`

Let `G : ℤ → ℂ` be supported in the symmetric window
`[-D + q·N', D - q·N']` (with `q·N' ≤ D`), and suppose `‖G y‖ ≤ 1` pointwise.  Then

`∑' y, (if D < |y + q·m| then ‖G y‖ else 0) ≤ q · max 0 (|m| - N')` .

The summand vanishes outside the window, so the left-hand side is the number of lattice
points `y` of the window with `|y + q·m| > D`.  Writing `z = y + q·m`, those are the points
of the interval `[q·m - D + q·N', q·m + D - q·N']` with `|z| > D`; the positive and the
negative branch contribute at most `max 0 (q(m - N'))` and `max 0 (-q(m + N'))`
respectively, and these two numbers add up to `q · max 0 (|m| - N')`.

## Main results

* `shellFilterCard` — the underlying cardinality bound for the window.
* `shellLeWindow` — the stated `tsum` bound.
-/

/-- `((m.natAbs : ℕ) : ℝ) = |(m : ℝ)|`. -/
private lemma natAbs_cast_abs (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- The cast of a truncated natural subtraction as a truncated real subtraction. -/
private lemma natCast_sub_max (a b : ℕ) :
    ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - (b : ℝ)) := by
  rcases le_or_gt b a with h | h
  · rw [Nat.cast_sub h, max_eq_right]
    have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    linarith
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h), Nat.cast_zero, max_eq_left]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_of_lt h
    linarith

/-- `D < |z|` for integers, in terms of `z` (with `D : ℕ`). -/
private lemma lt_natAbs_iff (z : ℤ) (D : ℕ) :
    D < z.natAbs ↔ (D : ℤ) < z ∨ z < -(D : ℤ) := by
  have h : (D < z.natAbs) ↔ (D : ℤ) < |z| :=
    (Nat.cast_lt (α := ℤ)).symm.trans (by rw [Int.natCast_natAbs])
  rw [h, lt_abs]
  omega

/-- `(q · (k - N')).toNat = q · (k - N')` (with the natural subtraction on the right). -/
private lemma toNat_mul_sub (q k N' : ℕ) :
    (((q : ℤ) * ((k : ℤ) - (N' : ℤ))).toNat) = q * (k - N') := by
  by_cases h : N' ≤ k
  · have h1 : (0 : ℤ) ≤ (k : ℤ) - (N' : ℤ) := by omega
    rw [Int.toNat_mul (by positivity) h1, Int.toNat_natCast, Int.toNat_sub]
  · have h1 : ((k : ℤ) - (N' : ℤ)) < 0 := by omega
    have h2 : (q : ℤ) * ((k : ℤ) - (N' : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt h1)
    rw [Int.toNat_eq_zero.mpr h2, Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h)), mul_zero]

/-- The two `toNat` contributions of the two branches of `D < |y + q·m|` add up to at most
`q · max 0 (|m| - N')`. -/
private lemma toNat_add_le (q N' : ℕ) (m : ℤ) :
    ((q : ℤ) * (m - (N' : ℤ))).toNat + (-((q : ℤ) * (m + (N' : ℤ)))).toNat
      ≤ q * (m.natAbs - N') := by
  rcases le_or_gt 0 m with hm | hm
  · have hm' : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
    have hb : (-((q : ℤ) * (m + (N' : ℤ)))).toNat = 0 := by
      rw [Int.toNat_eq_zero]
      have : (0 : ℤ) ≤ (q : ℤ) * (m + (N' : ℤ)) :=
        mul_nonneg (by positivity) (by omega)
      linarith
    have key : ((q : ℤ) * (m - (N' : ℤ))).toNat = q * (m.natAbs - N') := by
      have hsub : m - (N' : ℤ) = (m.natAbs : ℤ) - (N' : ℤ) := by rw [hm']
      rw [hsub, toNat_mul_sub]
    rw [key, hb, add_zero]
  · have hm'' : (m.natAbs : ℤ) = -m := Int.ofNat_natAbs_of_nonpos (le_of_lt hm)
    have ha : ((q : ℤ) * (m - (N' : ℤ))).toNat = 0 := by
      rw [Int.toNat_eq_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    have key : (-((q : ℤ) * (m + (N' : ℤ)))).toNat = q * (m.natAbs - N') := by
      have hsub : -((q : ℤ) * (m + (N' : ℤ))) = (q : ℤ) * ((m.natAbs : ℤ) - (N' : ℤ)) := by
        rw [hm'']; ring
      rw [hsub, toNat_mul_sub]
    rw [key, ha, zero_add]

/-- **The cardinality bound.**  Among the integers of the window `[lo, hi]` with
`lo = -D + q·N'` and `hi = D - q·N'`, at most `q · max 0 (m.natAbs - N')` of them satisfy
`D < |y + q·m|`. -/
private lemma shellFilterAux (D q N' : ℕ) (m lo hi : ℤ)
    (hlo : lo = -(D : ℤ) + (q : ℤ) * (N' : ℤ))
    (hhi : hi = (D : ℤ) - (q : ℤ) * (N' : ℤ)) :
    ((Finset.Icc lo hi).filter (fun y => D < (y + (q : ℤ) * m).natAbs)).card
      ≤ q * (m.natAbs - N') := by
  have hsub : (Finset.Icc lo hi).filter (fun y => D < (y + (q : ℤ) * m).natAbs)
      ⊆ ((Finset.Icc lo hi).filter (fun y => (D : ℤ) - (q : ℤ) * m < y))
        ∪ ((Finset.Icc lo hi).filter (fun y => y < -((D : ℤ)) - (q : ℤ) * m)) := by
    intro y hy
    obtain ⟨hy1, h3⟩ := Finset.mem_filter.mp hy
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hy1
    rcases (lt_natAbs_iff (y + (q : ℤ) * m) D).mp h3 with h4 | h4
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, by omega⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, by omega⟩))
  calc ((Finset.Icc lo hi).filter (fun y => D < (y + (q : ℤ) * m).natAbs)).card
      ≤ (((Finset.Icc lo hi).filter (fun y => (D : ℤ) - (q : ℤ) * m < y))
          ∪ ((Finset.Icc lo hi).filter (fun y => y < -((D : ℤ)) - (q : ℤ) * m))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Icc lo hi).filter (fun y => (D : ℤ) - (q : ℤ) * m < y)).card
          + ((Finset.Icc lo hi).filter (fun y => y < -((D : ℤ)) - (q : ℤ) * m)).card :=
        Finset.card_union_le _ _
    _ ≤ ((q : ℤ) * m - (q : ℤ) * (N' : ℤ)).toNat
          + (-((q : ℤ) * m + (q : ℤ) * (N' : ℤ))).toNat := by
        apply add_le_add
        · calc ((Finset.Icc lo hi).filter (fun y => (D : ℤ) - (q : ℤ) * m < y)).card
              ≤ (Finset.Icc ((D : ℤ) - (q : ℤ) * m + 1) hi).card :=
                Finset.card_le_card (by
                  intro y hy
                  obtain ⟨hy1, h3⟩ := Finset.mem_filter.mp hy
                  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hy1
                  exact Finset.mem_Icc.mpr ⟨by omega, h2⟩)
            _ = (hi + 1 - ((D : ℤ) - (q : ℤ) * m + 1)).toNat := Int.card_Icc _ _
            _ ≤ ((q : ℤ) * m - (q : ℤ) * (N' : ℤ)).toNat := by
                rw [show hi + 1 - ((D : ℤ) - (q : ℤ) * m + 1) = (q : ℤ) * m - (q : ℤ) * (N' : ℤ)
                      from by rw [hhi]; ring]
        · calc ((Finset.Icc lo hi).filter (fun y => y < -((D : ℤ)) - (q : ℤ) * m)).card
              ≤ (Finset.Icc lo (-((D : ℤ)) - (q : ℤ) * m - 1)).card :=
                Finset.card_le_card (by
                  intro y hy
                  obtain ⟨hy1, h3⟩ := Finset.mem_filter.mp hy
                  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hy1
                  exact Finset.mem_Icc.mpr ⟨h1, by omega⟩)
            _ = (-((D : ℤ)) - (q : ℤ) * m - 1 + 1 - lo).toNat := Int.card_Icc _ _
            _ ≤ (-((q : ℤ) * m + (q : ℤ) * (N' : ℤ))).toNat := by
                rw [show -((D : ℤ)) - (q : ℤ) * m - 1 + 1 - lo
                      = -((q : ℤ) * m + (q : ℤ) * (N' : ℤ)) from by rw [hlo]; ring]
    _ ≤ q * (m.natAbs - N') := by
        simpa only [mul_sub, mul_add] using toNat_add_le q N' m

/-- The cardinality bound in the form of the window of `shellLeWindow`. -/
private lemma shellFilterCard (D q N' : ℕ) (m : ℤ) :
    ((Finset.Icc (-(D : ℤ) + (q : ℤ) * (N' : ℤ)) ((D : ℤ) - (q : ℤ) * (N' : ℤ))).filter
      (fun y => D < (y + (q : ℤ) * m).natAbs)).card ≤ q * (m.natAbs - N') :=
  shellFilterAux D q N' m _ _ rfl rfl

/-- **The shell counting bound.**  If `G` is supported in `[-D + q·N', D - q·N']` and bounded
by `1`, then the part of the `ℓ¹` mass of `G` lying in the shell `D < |y + q·m|` is at most
`q · max 0 (|m| - N')`. -/
theorem shellLeWindow {G : ℤ → ℂ} {D q N' : ℕ} {m : ℤ}
    (hqN' : (q : ℤ) * (N' : ℤ) ≤ (D : ℤ))
    (hGsupp : ∀ y : ℤ, G y ≠ 0 →
      -((D : ℤ)) + (q : ℤ) * (N' : ℤ) ≤ y ∧ y ≤ (D : ℤ) - (q : ℤ) * (N' : ℤ))
    (hG1 : ∀ y : ℤ, ‖G y‖ ≤ 1) :
    (∑' y : ℤ, (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0))
      ≤ (q : ℝ) * max 0 (|(m : ℝ)| - (N' : ℝ)) := by
  have hzero : ∀ y ∉ Finset.Icc (-(D : ℤ) + (q : ℤ) * (N' : ℤ))
      ((D : ℤ) - (q : ℤ) * (N' : ℤ)),
      (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0) = 0 := by
    intro y hy
    by_cases hGy : G y = 0
    · simp [hGy]
    · exfalso
      exact hy (Finset.mem_Icc.mpr (hGsupp y hGy))
  rw [tsum_eq_sum hzero]
  rw [← Finset.sum_filter]
  calc ∑ y ∈ (Finset.Icc (-(D : ℤ) + (q : ℤ) * (N' : ℤ))
            ((D : ℤ) - (q : ℤ) * (N' : ℤ))).filter
            (fun y => D < (y + (q : ℤ) * m).natAbs), ‖G y‖
      ≤ ∑ _y ∈ (Finset.Icc (-(D : ℤ) + (q : ℤ) * (N' : ℤ))
            ((D : ℤ) - (q : ℤ) * (N' : ℤ))).filter
            (fun y => D < (y + (q : ℤ) * m).natAbs), (1 : ℝ) :=
        Finset.sum_le_sum (fun y _ => hG1 y)
    _ = (((Finset.Icc (-(D : ℤ) + (q : ℤ) * (N' : ℤ))
            ((D : ℤ) - (q : ℤ) * (N' : ℤ))).filter
            (fun y => D < (y + (q : ℤ) * m).natAbs)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ((q * (m.natAbs - N') : ℕ) : ℝ) := by exact_mod_cast shellFilterCard D q N' m
    _ = (q : ℝ) * max 0 (|(m : ℝ)| - (N' : ℝ)) := by
        rw [Nat.cast_mul, natCast_sub_max, natAbs_cast_abs]

end Work.KMTAreas.A4
