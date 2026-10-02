import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.LavaursA

/-- **The crossing lemma, pure sequential form.**  Let `s : ℕ → ℝ` be a sequence growing in steps between `7/8` and `9/8` from index `J` on (`hincr`), whose value at `J` exceeds `Xlo`, which eventually reaches the level `Rw` (`hex`), and whose value at `J` is still below `Rw` (`hRw`).  Then the least `j` with `Rw ≤ s j` is strictly after `J`, its value `s j` overshoots `Rw` by at most `9/8`, and `j` is bounded linearly in the depth: `j ≤ J + (8/7)(Rw − Xlo) + 1`. -/
theorem crossing_nat {s : ℕ → ℝ} {J : ℕ} {Xlo Rw : ℝ}
    (hXlo : Xlo < s J)
    (hincr : ∀ j : ℕ, J ≤ j → (7 / 8 : ℝ) ≤ s (j + 1) - s j ∧ s (j + 1) - s j ≤ 9 / 8)
    (hRw : s J < Rw)
    (hex : ∃ j : ℕ, Rw ≤ s j) :
    ∃ j : ℕ, J < j ∧ Rw ≤ s j ∧ s j ≤ Rw + 9 / 8 ∧
      (j : ℝ) ≤ (J : ℝ) + (8 / 7) * (Rw - Xlo) + 1 := by
  classical
  -- Linear growth from index `J`: `s (J + k) ≥ s J + (7/8) * k`.
  have hgrow : ∀ k : ℕ, s J + (7 / 8 : ℝ) * (k : ℝ) ≤ s (J + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (7 / 8 : ℝ) ≤ s (J + (k + 1)) - s (J + k) :=
        (hincr (J + k) (Nat.le_add_right J k)).1
      push_cast
      nlinarith [ih, hstep]
  -- There is an index at or beyond `J` reaching `Rw`.
  have hPne : ∃ j : ℕ, J ≤ j ∧ Rw ≤ s j := by
    obtain ⟨k, hk⟩ := exists_nat_ge ((8 / 7 : ℝ) * (Rw - s J))
    refine ⟨J + k, Nat.le_add_right J k, ?_⟩
    have hk' : Rw - s J ≤ (7 / 8 : ℝ) * (k : ℝ) := by
      have h : (7 / 8 : ℝ) * ((8 / 7 : ℝ) * (Rw - s J)) ≤ (7 / 8 : ℝ) * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hk (by norm_num)
      have he : (7 / 8 : ℝ) * ((8 / 7 : ℝ) * (Rw - s J)) = Rw - s J := by ring
      linarith
    have hg := hgrow k
    linarith
  -- Take the least such index.
  let j := Nat.find hPne
  have hjP : J ≤ j ∧ Rw ≤ s j := Nat.find_spec hPne
  have hmin : ∀ m : ℕ, m < j → ¬ (J ≤ m ∧ Rw ≤ s m) :=
    fun m hm => Nat.find_min hPne hm
  have hJj : J < j := by
    rcases hjP with ⟨hJle, hRwle⟩
    rcases lt_or_eq_of_le hJle with h | h
    · exact h
    · exfalso
      rw [← h] at hRwle
      linarith
  have hjm1J : J ≤ j - 1 := by omega
  have hpred_lt : j - 1 < j := by omega
  have hsjm1 : s (j - 1) < Rw := by
    have hnot : ¬ (J ≤ j - 1 ∧ Rw ≤ s (j - 1)) := hmin (j - 1) hpred_lt
    by_contra hcon
    exact hnot ⟨hjm1J, not_lt.mp hcon⟩
  have hstep := hincr (j - 1) hjm1J
  have hj_eq : (j - 1) + 1 = j := Nat.sub_add_cancel (by omega : 1 ≤ j)
  -- Overshoot bound.
  have hsj_le : s j ≤ Rw + 9 / 8 := by
    have h2 : s j - s (j - 1) ≤ 9 / 8 := by
      have hh := hstep.2
      rwa [hj_eq] at hh
    linarith
  -- Cast bookkeeping.
  have hcast : ((j - 1 - J : ℕ) : ℝ) = (j : ℝ) - 1 - (J : ℝ) := by
    have h1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      norm_num
    have h2 : ((j - 1 - J : ℕ) : ℝ) = ((j - 1 : ℕ) : ℝ) - (J : ℝ) := by
      rw [Nat.cast_sub hjm1J]
    linarith
  -- Linear growth gives the depth bound.
  have hlin7 : (7 / 8 : ℝ) * ((j - 1 - J : ℕ) : ℝ) < Rw - Xlo := by
    have hgm : s J + (7 / 8 : ℝ) * ((j - 1 - J : ℕ) : ℝ) ≤ s (j - 1) := by
      have hg := hgrow (j - 1 - J)
      rwa [Nat.add_sub_cancel' hjm1J] at hg
    linarith
  have hlin : (j : ℝ) < (J : ℝ) + (8 / 7) * (Rw - Xlo) + 1 := by
    have h8 : ((j - 1 - J : ℕ) : ℝ) < (8 / 7) * (Rw - Xlo) := by
      nlinarith [hlin7]
    rw [hcast] at h8
    linarith
  exact ⟨j, hJj, hjP.2, hsj_le, le_of_lt hlin⟩

end Work.PARIMPL2.LavaursA
