/-
# ZeroFreeTables — t23certG

The certificate `RowCertG` of `Submission.Work.ZeroFreeTables.t23Defs`: the four rows

`(41/20, 2/5, 169/100), (21/10, 7/20, 199/100), (43/20, 3/10, 233/100), (9/4, 1/4, 273/100)`

of the top of the second conjunct's range (`λ₁ ∈ (1/5, 2/5]`), each certified by the
inequality

`(1/15)·(G (v/λ) − G ((v−b)/λ)) < 8/9 − CertSlack·(16λ/15)`.

The proof follows the recipe of `t23Gclosed`: the closed form `hb72G_closed` of
`G x = ∫₀² g(u) e^{xu} du`, together with two-sided rational Taylor bounds
`exp_bounds_quart` for the two exponentials `e^{2v/λ}` and `e^{2(v−b)/λ}`, reduces each row
to rational arithmetic.  The margins are all `> 4.6·10⁻³`, so five-decimal bounds on the
exponentials suffice.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.ZeroFreeTables.t23Gclosed

namespace Work.ZeroFreeTables

/-- Row `(λ, b, v) = (41/20, 2/5, 169/100)` of `rowG`, with
`e^{338/205} ≤ 5.20064` and `e^{258/205} ≥ 3.52026`. -/
private lemma rowG_1 :
    (1 / 15) * (hb72G ((169:ℝ) / 100 / (41 / 20)) - hb72G (((169:ℝ) / 100 - 2 / 5) / (41 / 20)))
      < 8 / 9 - CertSlack * (16 * ((41:ℝ) / 20) / 15) := by
  rw [show (169:ℝ) / 100 / (41 / 20) = (169:ℝ) / 205 by norm_num,
      show ((169:ℝ) / 100 - 2 / 5) / (41 / 20) = (129:ℝ) / 205 by norm_num]
  rw [hb72G_closed (by norm_num : ((169:ℝ) / 205) ≠ 0),
      hb72G_closed (by norm_num : ((129:ℝ) / 205) ≠ 0)]
  rw [show 2 * ((169:ℝ) / 205) = (338:ℝ) / 205 by norm_num,
      show 2 * ((129:ℝ) / 205) = (258:ℝ) / 205 by norm_num]
  unfold CertSlack
  obtain ⟨_, h1hi⟩ := exp_bounds_quart (x := (338:ℝ) / 205) (lo := 5.20063) (hi := 5.20064)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, _⟩ := exp_bounds_quart (x := (258:ℝ) / 205) (lo := 3.52026) (hi := 3.52027)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]

/-- Row `(λ, b, v) = (21/10, 7/20, 199/100)` of `rowG`, with
`e^{199/105} ≤ 6.65414` and `e^{164/105} ≥ 4.76789`. -/
private lemma rowG_2 :
    (1 / 15) * (hb72G ((199:ℝ) / 100 / (21 / 10)) - hb72G (((199:ℝ) / 100 - 7 / 20) / (21 / 10)))
      < 8 / 9 - CertSlack * (16 * ((21:ℝ) / 10) / 15) := by
  rw [show (199:ℝ) / 100 / (21 / 10) = (199:ℝ) / 210 by norm_num,
      show ((199:ℝ) / 100 - 7 / 20) / (21 / 10) = (82:ℝ) / 105 by norm_num]
  rw [hb72G_closed (by norm_num : ((199:ℝ) / 210) ≠ 0),
      hb72G_closed (by norm_num : ((82:ℝ) / 105) ≠ 0)]
  rw [show 2 * ((199:ℝ) / 210) = (199:ℝ) / 105 by norm_num,
      show 2 * ((82:ℝ) / 105) = (164:ℝ) / 105 by norm_num]
  unfold CertSlack
  obtain ⟨_, h1hi⟩ := exp_bounds_quart (x := (199:ℝ) / 105) (lo := 6.65413) (hi := 6.65414)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, _⟩ := exp_bounds_quart (x := (164:ℝ) / 105) (lo := 4.76789) (hi := 4.76790)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]

/-- Row `(λ, b, v) = (43/20, 3/10, 233/100)` of `rowG`, with
`e^{466/215} ≤ 8.73591` and `e^{406/215} ≥ 6.60860`. -/
private lemma rowG_3 :
    (1 / 15) * (hb72G ((233:ℝ) / 100 / (43 / 20)) - hb72G (((233:ℝ) / 100 - 3 / 10) / (43 / 20)))
      < 8 / 9 - CertSlack * (16 * ((43:ℝ) / 20) / 15) := by
  rw [show (233:ℝ) / 100 / (43 / 20) = (233:ℝ) / 215 by norm_num,
      show ((233:ℝ) / 100 - 3 / 10) / (43 / 20) = (203:ℝ) / 215 by norm_num]
  rw [hb72G_closed (by norm_num : ((233:ℝ) / 215) ≠ 0),
      hb72G_closed (by norm_num : ((203:ℝ) / 215) ≠ 0)]
  rw [show 2 * ((233:ℝ) / 215) = (466:ℝ) / 215 by norm_num,
      show 2 * ((203:ℝ) / 215) = (406:ℝ) / 215 by norm_num]
  unfold CertSlack
  obtain ⟨_, h1hi⟩ := exp_bounds_quart (x := (466:ℝ) / 215) (lo := 8.73590) (hi := 8.73591)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, _⟩ := exp_bounds_quart (x := (406:ℝ) / 215) (lo := 6.60860) (hi := 6.60861)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]

/-- Row `(λ, b, v) = (9/4, 1/4, 273/100)` of `rowG`, with
`e^{182/75} ≤ 11.32109` and `e^{496/225} ≥ 9.06521`. -/
private lemma rowG_4 :
    (1 / 15) * (hb72G ((273:ℝ) / 100 / (9 / 4)) - hb72G (((273:ℝ) / 100 - 1 / 4) / (9 / 4)))
      < 8 / 9 - CertSlack * (16 * ((9:ℝ) / 4) / 15) := by
  rw [show (273:ℝ) / 100 / (9 / 4) = (91:ℝ) / 75 by norm_num,
      show ((273:ℝ) / 100 - 1 / 4) / (9 / 4) = (248:ℝ) / 225 by norm_num]
  rw [hb72G_closed (by norm_num : ((91:ℝ) / 75) ≠ 0),
      hb72G_closed (by norm_num : ((248:ℝ) / 225) ≠ 0)]
  rw [show 2 * ((91:ℝ) / 75) = (182:ℝ) / 75 by norm_num,
      show 2 * ((248:ℝ) / 225) = (496:ℝ) / 225 by norm_num]
  unfold CertSlack
  obtain ⟨_, h1hi⟩ := exp_bounds_quart (x := (182:ℝ) / 75) (lo := 11.32108) (hi := 11.32109)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  obtain ⟨h2lo, _⟩ := exp_bounds_quart (x := (496:ℝ) / 225) (lo := 9.06521) (hi := 9.06522)
    (by norm_num) (by norm_num) (by norm_num [expErr, Finset.sum_range_succ])
    (by norm_num [expErr, Finset.sum_range_succ])
  norm_num
  linarith [h1hi, h2lo]

/-- **The certificate of `rowG`**: the four top rows of the second conjunct's range. -/
theorem t23certG : Work.ZeroFreeTables.RowCertG := by
  intro p hp
  simp only [rowG, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact rowG_1
  · exact rowG_2
  · exact rowG_3
  · exact rowG_4

end Work.ZeroFreeTables
