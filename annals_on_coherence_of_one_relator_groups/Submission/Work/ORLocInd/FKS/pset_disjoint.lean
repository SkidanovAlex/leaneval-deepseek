import Mathlib
import Submission.Work.ORLocInd.FKS.SL2Defs

namespace Work.ORLocInd.FKS

/-- For natural numbers `a ≤ b`, the norm in `ℂ` of the difference of the two (real) casts is the
natural number `b - a`, cast to `ℝ`. -/
private lemma norm_natCast_sub_natCast {a b : ℕ} (hab : a ≤ b) :
    ‖((a : ℕ) : ℂ) - ((b : ℕ) : ℂ)‖ = ((b - a : ℕ) : ℝ) := by
  have hb : ((b : ℕ) : ℂ) = ((a : ℕ) : ℂ) + ((b - a : ℕ) : ℂ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le hab]
  have hsub : ((a : ℕ) : ℂ) - (((a : ℕ) : ℂ) + ((b - a : ℕ) : ℂ)) = -((b - a : ℕ) : ℂ) := by
    ring
  rw [hb, hsub, norm_neg, Complex.norm_natCast]

/-- The ping-pong sets `pset p j` (open unit discs in `ℍ` centred at the cusps `p*j`) are pairwise
disjoint as soon as `p ≥ 2`: if `z` lay in both `pset p j` and `pset p j'`, then
`p * |j - j'| = ‖p*j - p*j'‖ ≤ ‖z - p*j‖ + ‖z - p*j'‖ < 2`, so `|j - j'| < 1`, i.e. `j = j'`. -/
theorem pset_disjoint (p : ℕ) (hp : 2 ≤ p) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (Work.ORLocInd.FKS.pset p j) (Work.ORLocInd.FKS.pset p j') := by
  rw [Set.disjoint_left]
  intro z hz hz'
  simp only [pset, Set.mem_ofPred_eq] at hz hz'
  -- `z` lies in both unit discs, so the two cusps are at distance `< 2`.
  have h2 : ‖(p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ)‖ < 2 := by
    have htri : ‖(p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ)‖
        ≤ ‖(p : ℂ) * (j : ℂ) - (z : ℂ)‖ + ‖(z : ℂ) - (p : ℂ) * (j' : ℂ)‖ := by
      simpa only [dist_eq_norm] using
        dist_triangle ((p : ℂ) * (j : ℂ)) (z : ℂ) ((p : ℂ) * (j' : ℂ))
    calc ‖(p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ)‖
        ≤ ‖(p : ℂ) * (j : ℂ) - (z : ℂ)‖ + ‖(z : ℂ) - (p : ℂ) * (j' : ℂ)‖ := htri
      _ = ‖(z : ℂ) - (p : ℂ) * (j : ℂ)‖ + ‖(z : ℂ) - (p : ℂ) * (j' : ℂ)‖ := by
            rw [norm_sub_rev]
      _ < 1 + 1 := add_lt_add hz hz'
      _ = 2 := by norm_num
  -- The two cusps are integers at distance `p * |j - j'| ≥ 2`.
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hjn : ‖(j : ℂ) - (j' : ℂ)‖ = ((j' - j : ℕ) : ℝ) :=
      norm_natCast_sub_natCast (le_of_lt hlt)
    have hjR : (1 : ℝ) ≤ ((j' - j : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
    have hge : (2 : ℝ) ≤ ‖(p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ)‖ := by
      rw [show (p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ) = (p : ℂ) * ((j : ℂ) - (j' : ℂ)) by
            ring]
      rw [norm_mul, hjn, Complex.norm_natCast]
      nlinarith [hpR, hjR, Nat.cast_nonneg (j' - j : ℕ) (α := ℝ)]
    exact absurd h2 (not_lt_of_ge hge)
  · have hjn : ‖(j : ℂ) - (j' : ℂ)‖ = ((j - j' : ℕ) : ℝ) := by
      rw [norm_sub_rev]
      exact norm_natCast_sub_natCast (le_of_lt hlt)
    have hjR : (1 : ℝ) ≤ ((j - j' : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sub_pos_of_lt hlt)
    have hge : (2 : ℝ) ≤ ‖(p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ)‖ := by
      rw [show (p : ℂ) * (j : ℂ) - (p : ℂ) * (j' : ℂ) = (p : ℂ) * ((j : ℂ) - (j' : ℂ)) by
            ring]
      rw [norm_mul, hjn, Complex.norm_natCast]
      nlinarith [hpR, hjR, Nat.cast_nonneg (j - j' : ℕ) (α := ℝ)]
    exact absurd h2 (not_lt_of_ge hge)

end Work.ORLocInd.FKS
