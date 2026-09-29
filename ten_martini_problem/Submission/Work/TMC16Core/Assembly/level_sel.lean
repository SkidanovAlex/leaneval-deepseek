import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.RegWin

namespace Work.TMC16Core.Assembly

set_option linter.unusedVariables false

open Filter

/-- Sub-lemma: `q n ≥ n` for a strictly monotone `q : ℕ → ℕ` (the positivity hypothesis is
not needed for this). -/
theorem self_le_of_strictMono {q : ℕ → ℕ} (hmono : StrictMono q) : ∀ n, n ≤ q n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk : q k < q (k + 1) := hmono (Nat.lt_succ_self k)
    omega

/-- Sub-lemma: `bG q n → ∞`, in the form `(q n)^{8/9} → ∞`. -/
theorem tendsto_bG_rpow {q : ℕ → ℕ} (hmono : StrictMono q) :
    Tendsto (fun n : ℕ => ((q n : ℝ)) ^ (8 / 9 : ℝ)) atTop atTop := by
  have hqn : ∀ n, n ≤ q n := self_le_of_strictMono hmono
  have hle : ∀ n : ℕ, ((n : ℝ)) ^ (8 / 9 : ℝ) ≤ ((q n : ℝ)) ^ (8 / 9 : ℝ) := by
    intro n
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    exact_mod_cast hqn n
  have htend_nat : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (8 / 9 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono hle htend_nat

/-- The level function `bG q n = max(qₙ^{8/9}, q(n-1)/20 + 3)` tends to infinity: it dominates
`qₙ^{8/9} ≥ n^{8/9}`. -/
theorem tendsto_bG_atTop {q : ℕ → ℕ} (hmono : StrictMono q) :
    Tendsto (Work.TMC16Core.Assembly.bG q) atTop atTop :=
  tendsto_atTop_mono (fun n => le_max_left _ _) (tendsto_bG_rpow hmono)

/-- `bG q` is (weakly) monotone in nothing in particular, but it is bounded below by
`(q n)^{8/9}`. -/
theorem rpow_le_bG {q : ℕ → ℕ} (n : ℕ) :
    ((q n : ℝ)) ^ (8 / 9 : ℝ) ≤ Work.TMC16Core.Assembly.bG q n :=
  le_max_left ((q n : ℝ) ^ (8 / 9 : ℝ)) ((q (n - 1) : ℝ) / 20 + 3)

/-- Selection of the level `n` at which the level function `bG q` crosses the height `y`:
given `bG q N < y`, there is `n ≥ N` with `bG q n < y ≤ bG q (n+1)`.

This is the least `m ≥ N` with `y ≤ bG q (m+1)` (existence by `tendsto_bG_atTop`). -/
theorem level_sel {q : ℕ → ℕ} (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) :
    ∀ N : ℕ, ∀ y : ℤ, Work.TMC16Core.Assembly.bG q N < (y : ℝ) →
      ∃ n : ℕ, N ≤ n ∧ Work.TMC16Core.Assembly.bG q n < (y : ℝ) ∧
        (y : ℝ) ≤ Work.TMC16Core.Assembly.bG q (n + 1) := by
  intro N y hN
  have htend := tendsto_bG_rpow hmono
  have hev : ∀ᶠ n : ℕ in atTop, (y : ℝ) ≤ ((q n : ℝ)) ^ (8 / 9 : ℝ) :=
    htend.eventually (eventually_ge_atTop (y : ℝ))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hex : ∃ m, N ≤ m ∧ (y : ℝ) ≤ Work.TMC16Core.Assembly.bG q (m + 1) := by
    refine ⟨max N N₀, le_max_left _ _, ?_⟩
    have h1 : (y : ℝ) ≤ ((q (max N N₀ + 1) : ℝ)) ^ (8 / 9 : ℝ) :=
      hN₀ _ (le_trans (le_max_right _ _) (Nat.le_succ _))
    linarith [rpow_le_bG (q := q) (max N N₀ + 1)]
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  by_cases hn : Nat.find hex = N
  · rw [hn]; exact hN
  · have hlt : N < Nat.find hex := lt_of_le_of_ne (Nat.find_spec hex).1 (Ne.symm hn)
    have hpos : 0 < Nat.find hex := Nat.lt_of_le_of_lt (Nat.zero_le N) hlt
    have hsucc : (Nat.find hex).pred + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos hpos
    refine lt_of_not_ge fun hc => ?_
    have hp : N ≤ (Nat.find hex).pred ∧
        (y : ℝ) ≤ Work.TMC16Core.Assembly.bG q ((Nat.find hex).pred + 1) := by
      refine ⟨Nat.le_pred_of_lt hlt, ?_⟩
      rw [hsucc]
      exact hc
    have hfin : Nat.find hex ≤ (Nat.find hex).pred := Nat.find_min' hex hp
    exact absurd (Nat.lt_of_le_pred hpos hfin) (lt_irrefl _)

end Work.TMC16Core.Assembly
