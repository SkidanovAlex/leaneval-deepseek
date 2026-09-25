import Mathlib
import Submission.Work.RHContract.A.CaDeltaDefs
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_small_59
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_finite_range

/-!
# The lower bound `caL t ≤ θ t` for `3 ≤ t < 1530`

`caL` (the lower bounding function of the colossally abundant parametrisation) equals
`0.35 t` on `[3, 39)` and `0.7 t` on `[39, 1530)`.  Both are checked on finite ranges:

* on `[3, 39)` we use the tabulated lower bounds for `θ` on `[2, 59]`
  (`Commons.NumberTheory.Chebyshev.theta_lower_small_59`);
* on `[39, 1530)` we use the scaled integer table of
  `Commons.NumberTheory.Chebyshev.theta_lower_finite_range`: its entries `(p, c)` record
  `c = Σ_{q < p} termOf q` with `termOf q ≤ 10^9 log q` (error at most `10^6` per prime),
  and the arithmetic check `7 · 10^8 · p ≤ c` holds for every entry with `p ≥ 40`.
-/

set_option maxRecDepth 1000000

namespace Work.RHContract.A

/-- Arithmetic check on the Chebyshev table: for every entry `e` of the table with
`40 ≤ e.1`, the scaled cumulative logarithm `e.2` is at least `0.7 · e.1`. -/
theorem caTheta_table_bound :
    ∀ e ∈ Commons.NumberTheory.Chebyshev.ThetaFinite.C,
      40 ≤ e.1 → 7 * 10 ^ 8 * e.1 ≤ e.2 := by
  decide

/-- `θ n ≥ 0.7 (n+1)` for `39 ≤ n ≤ 1529`, from the Chebyshev table. -/
theorem caTheta_lower_mid (n : ℕ) (h39 : 39 ≤ n) (hn : n ≤ 1529) :
    (0.7 : ℝ) * ((n : ℝ) + 1) ≤ Chebyshev.theta (n : ℝ) := by
  have hmem : (30001, 29519910398000) ∈ Commons.NumberTheory.Chebyshev.ThetaFinite.C := by
    unfold Commons.NumberTheory.Chebyshev.ThetaFinite.C
    exact List.mem_append_right _ (by simp [Commons.NumberTheory.Chebyshev.ThetaFinite.lastEnt])
  obtain ⟨b, hb⟩ : ∃ b, Commons.NumberTheory.Chebyshev.ThetaFinite.bnd
      Commons.NumberTheory.Chebyshev.ThetaFinite.C n = some b :=
    Option.isSome_iff_exists.mp
      (Commons.NumberTheory.Chebyshev.ThetaFinite.bnd_isSome_of_mem hmem (by omega))
  have hb_mem : b ∈ Commons.NumberTheory.Chebyshev.ThetaFinite.C :=
    Commons.NumberTheory.Chebyshev.ThetaFinite.bnd_some_mem hb
  have hb_gt : n < b.1 := Commons.NumberTheory.Chebyshev.ThetaFinite.bnd_some_gt hb
  have hb_spec : b.2
      = (Commons.NumberTheory.Chebyshev.ThetaFinite.C.head?.map Prod.snd).getD 0
        + Commons.NumberTheory.Chebyshev.ThetaFinite.psum
            Commons.NumberTheory.Chebyshev.ThetaFinite.C n :=
    Commons.NumberTheory.Chebyshev.ThetaFinite.bnd_spec _ _
      Commons.NumberTheory.Chebyshev.ThetaFinite.chain_curried hb
  have hhead : (Commons.NumberTheory.Chebyshev.ThetaFinite.C.head?.map Prod.snd).getD 0 = 0 := by
    rw [Commons.NumberTheory.Chebyshev.ThetaFinite.chk_head]; rfl
  rw [hhead, Nat.zero_add] at hb_spec
  have hb_bound : 7 * 10 ^ 8 * b.1 ≤ b.2 := caTheta_table_bound b hb_mem (by omega)
  have hb1 : n + 1 ≤ b.1 := by omega
  have hkey : 7 * 10 ^ 8 * (n + 1) ≤
      Commons.NumberTheory.Chebyshev.ThetaFinite.psum
        Commons.NumberTheory.Chebyshev.ThetaFinite.C n := by
    rw [← hb_spec]
    exact le_trans (Nat.mul_le_mul_left _ hb1) hb_bound
  have hle := Commons.NumberTheory.Chebyshev.ThetaFinite.psum_le_theta n (by omega)
  have hcast : ((7 * 10 ^ 8 * (n + 1) : ℕ) : ℝ) ≤
      (Commons.NumberTheory.Chebyshev.ThetaFinite.psum
        Commons.NumberTheory.Chebyshev.ThetaFinite.C n : ℝ) := by
    exact_mod_cast hkey
  have hmain : (7 * 10 ^ 8 : ℝ) * ((n : ℝ) + 1) ≤ 10 ^ 9 * Chebyshev.theta (n : ℝ) := by
    push_cast at hcast ⊢
    linarith
  linarith

/-- `θ n ≥ 0.35 (n+1)` for `3 ≤ n ≤ 38`. -/
theorem caTheta_lower_small (n : ℕ) (h3 : 3 ≤ n) (h38 : n ≤ 38) :
    (0.35 : ℝ) * ((n : ℝ) + 1) ≤ Chebyshev.theta (n : ℝ) := by
  interval_cases n <;>
    · refine le_trans ?_
        (Commons.NumberTheory.Chebyshev.theta_lower_small_59 _ (by omega) (by omega))
      norm_num

theorem theta_ge_frac_small (t : ℝ) (h1 : 3 ≤ t) (h2 : t < 1530) :
    Work.RHContract.A.caL t ≤ Chebyshev.theta t := by
  set n : ℕ := ⌊t⌋₊ with hn
  have ht0 : 0 ≤ t := by linarith
  have htn : (n : ℝ) ≤ t := by rw [hn]; exact Nat.floor_le ht0
  have htn1 : t < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one t
  have hth : Chebyshev.theta t = Chebyshev.theta (n : ℝ) :=
    Commons.NumberTheory.Chebyshev.theta_eq_theta_floor t
  rw [hth]
  have hn3 : 3 ≤ n := Nat.le_floor (by exact_mod_cast h1)
  have hn1530 : n < 1530 := by
    rw [hn, Nat.floor_lt ht0]; exact_mod_cast h2
  have hn1529 : n ≤ 1529 := by omega
  rcases lt_or_ge t 39 with h39 | h39
  · have hL : Work.RHContract.A.caL t = (0.35 : ℝ) * t := by
      unfold Work.RHContract.A.caL
      rw [if_neg (by linarith : ¬ t < 3), if_pos h39]
    rw [hL]
    have hn38 : n ≤ 38 := by
      have : n < 39 := (Nat.floor_lt ht0).mpr h39
      omega
    have hkey := caTheta_lower_small n hn3 hn38
    linarith
  · have hL : Work.RHContract.A.caL t = (0.7 : ℝ) * t := by
      unfold Work.RHContract.A.caL
      rw [if_neg (by linarith : ¬ t < 3), if_neg (by linarith : ¬ t < 39), if_pos h2]
    rw [hL]
    have hn39 : 39 ≤ n := Nat.le_floor (by exact_mod_cast h39)
    have hkey := caTheta_lower_mid n hn39 hn1529
    linarith

end Work.RHContract.A
