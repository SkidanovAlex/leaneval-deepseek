import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Work.BoseBogFS.latticeSumBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Moment sums over the lattice cube `[-J,J]³`

The four elementary estimates on the dual-lattice cube `cube J = {n | mn n ≤ J}` used by the
Bogoliubov/Fourier chapter of the dilute Bose gas proof:

* `Σ_{n ∈ cube J} 1 = (2J+1)³ ≤ 27 (J+1)³` (a pure count);
* `Σ_{n ∈ cube J} (mn n + 1) ≤ 27 (J+1)⁴` (a pure count, since `mn n ≤ J` on the cube);
* `Σ_{n ∈ cube J} (mn n + 1)⁻² ≤ 26 (J+1)` (shell decomposition: the shell `{mn = j}` has
  `24 j² + 2` points, each of maximal norm `j`, and each contributes at most `26`); and
* `Σ_{n ∈ cube J} (mn n + 1)⁻³ ≤ 30 (1 + log (2 + J))` (the same shell decomposition, each shell
  contributing at most `24/(j+1)`, which telescopes against `log`).

The shell decomposition `sum_cube_mn_le` below is the `mn`-analogue of `sum_cube_le`.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

set_option maxHeartbeats 1000000

/-! ## 1. The shell decomposition for the maximal norm -/

/-- The lattice origin has maximal norm zero. -/
lemma mn_zero : mn (0 : Fin 3 → ℤ) = 0 := by
  simp [mn]

/-- **Shell decomposition for the maximal norm.**  For a nonnegative profile `f` on `ℕ`, the sum
over the cube `{mn ≤ J}` is bounded by the one-dimensional shell series. -/
lemma sum_cube_mn_le {f : ℕ → ℝ} (hf0 : ∀ j, 0 ≤ f j) (J : ℕ) :
    ∑ n ∈ cube J, f (mn n) ≤ ∑ j ∈ Finset.range (J + 1), prof j * f j := by
  induction J with
  | zero =>
    have hsub : cube 0 ⊆ ({0} : Finset (Fin 3 → ℤ)) := by
      intro n hn
      rw [mem_cube] at hn
      rw [Finset.mem_singleton]
      funext i
      have h1 : (n i).natAbs ≤ mn n := mn_coord_le n i
      exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero (le_trans h1 hn))
    have hp0 : prof 0 = 2 := by simp only [prof]; norm_num
    calc ∑ n ∈ cube 0, f (mn n)
        ≤ ∑ n ∈ ({0} : Finset (Fin 3 → ℤ)), f (mn n) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hf0 _
      _ = f 0 := by rw [Finset.sum_singleton, mn_zero]
      _ ≤ prof 0 * f 0 := by rw [hp0]; linarith [hf0 0]
      _ = ∑ j ∈ Finset.range (0 + 1), prof j * f j := by
            rw [Finset.range_one, Finset.sum_singleton]
  | succ J ih =>
    have hsub : cube J ⊆ cube (J + 1) := cube_mono (Nat.le_succ J)
    have hsplit := Finset.sum_sdiff hsub (f := fun n => f (mn n))
    rw [← hsplit, Finset.sum_range_succ]
    have hmn : ∀ n ∈ cube (J + 1) \ cube J, mn n = J + 1 := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hn
      have ha : mn n ≤ J + 1 := mem_cube.mp h1
      have hb : ¬ (mn n ≤ J) := fun h => h2 (mem_cube.mpr h)
      omega
    have hcardle : ((cube (J + 1) \ cube J).card : ℝ) ≤ prof (J + 1) := by
      have hc := card_shell_le J
      have hcast : ((24 * (J + 1) ^ 2 + 2 : ℕ) : ℝ) = prof (J + 1) := by
        simp only [prof]; push_cast; ring
      calc ((cube (J + 1) \ cube J).card : ℝ)
          ≤ ((24 * (J + 1) ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast hc
        _ = prof (J + 1) := hcast
    have hshell : ∑ n ∈ cube (J + 1) \ cube J, f (mn n) ≤ prof (J + 1) * f (J + 1) := by
      calc ∑ n ∈ cube (J + 1) \ cube J, f (mn n)
          = ∑ n ∈ cube (J + 1) \ cube J, f (J + 1) :=
            Finset.sum_congr rfl fun n hn => by rw [hmn n hn]
        _ = ((cube (J + 1) \ cube J).card : ℝ) * f (J + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ prof (J + 1) * f (J + 1) := mul_le_mul_of_nonneg_right hcardle (hf0 _)
    linarith

/-! ## 2. The logarithmic telescoping bound for the harmonic sum -/

/-- `1/(j+1) ≤ log (j+1) - log j` for `j ≥ 1`: the elementary fact behind the telescoping bound
on the harmonic sum. -/
lemma inv_succ_le_log_sub (j : ℕ) (hj : 1 ≤ j) :
    1 / ((j : ℝ) + 1) ≤ Real.log ((j : ℝ) + 1) - Real.log (j : ℝ) := by
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hpos : 0 < ((j : ℝ) + 1) / (j : ℝ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  rw [Real.log_div (by positivity) (ne_of_gt hj0), inv_div] at h
  have hL : 1 - (j : ℝ) / ((j : ℝ) + 1) = 1 / ((j : ℝ) + 1) := by
    have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hsum : (j : ℝ) / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) = 1 := by
      rw [← add_div]
      exact div_self hne
    linarith
  rw [hL] at h
  exact h

/-- **The harmonic sum telescoped against `log`.** -/
lemma sum_range_inv_succ_le (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), 1 / ((j : ℝ) + 1) ≤ 1 + Real.log ((J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    show ∑ j ∈ Finset.range (J + 1 + 1), 1 / ((j : ℝ) + 1)
        ≤ 1 + Real.log (((J + 1 : ℕ) : ℝ) + 1)
    rw [Finset.sum_range_succ]
    have hc : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
    have hkey := inv_succ_le_log_sub (J + 1) (by omega)
    rw [hc] at hkey
    rw [hc]
    linarith

/-! ## 3. The four estimates -/

/-- `Σ_{n ∈ cube J} 1 = (2J+1)³ ≤ 27 (J+1)³`. -/
lemma cube_sum_one (J : ℕ) :
    ∑ n ∈ cube J, (1 : ℝ) ≤ 27 * ((J : ℝ) + 1) ^ 3 := by
  have hcard : ∑ n ∈ cube J, (1 : ℝ) = ((cube J).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hle : ((2 * J + 1 : ℕ) : ℝ) ≤ 3 * ((J : ℝ) + 1) := by
    have hcast : ((2 * J + 1 : ℕ) : ℝ) = 2 * (J : ℝ) + 1 := by push_cast; ring
    rw [hcast]; linarith
  rw [hcard, card_cube, Nat.cast_pow]
  calc (((2 * J + 1 : ℕ) : ℝ)) ^ 3 ≤ (3 * ((J : ℝ) + 1)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hle 3
    _ = 27 * ((J : ℝ) + 1) ^ 3 := by ring

/-- `Σ_{n ∈ cube J} (mn n + 1) ≤ 27 (J+1)⁴`. -/
lemma cube_sum_mn_add_one (J : ℕ) :
    ∑ n ∈ cube J, ((mn n : ℝ) + 1) ≤ 27 * ((J : ℝ) + 1) ^ 4 := by
  have hbound : ∑ n ∈ cube J, ((mn n : ℝ) + 1) ≤ ((cube J).card : ℝ) * ((J : ℝ) + 1) := by
    calc ∑ n ∈ cube J, ((mn n : ℝ) + 1)
        ≤ ∑ _n ∈ cube J, ((J : ℝ) + 1) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h : (mn n : ℝ) ≤ (J : ℝ) := by exact_mod_cast mem_cube.mp hn
          linarith
      _ = ((cube J).card : ℝ) * ((J : ℝ) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  refine hbound.trans ?_
  rw [card_cube, Nat.cast_pow]
  have hle : ((2 * J + 1 : ℕ) : ℝ) ≤ 3 * ((J : ℝ) + 1) := by
    have hcast : ((2 * J + 1 : ℕ) : ℝ) = 2 * (J : ℝ) + 1 := by push_cast; ring
    rw [hcast]; linarith
  have hcube : (((2 * J + 1 : ℕ) : ℝ)) ^ 3 ≤ (3 * ((J : ℝ) + 1)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hle 3
  have hJ1 : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
  calc (((2 * J + 1 : ℕ) : ℝ)) ^ 3 * ((J : ℝ) + 1)
      ≤ (27 * ((J : ℝ) + 1) ^ 3) * ((J : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hJ1
        calc (((2 * J + 1 : ℕ) : ℝ)) ^ 3 ≤ (3 * ((J : ℝ) + 1)) ^ 3 := hcube
          _ = 27 * ((J : ℝ) + 1) ^ 3 := by ring
    _ = 27 * ((J : ℝ) + 1) ^ 4 := by ring

/-- `Σ_{n ∈ cube J} 1/(mn n + 1)² ≤ 26 (J+1)`. -/
lemma cube_sum_invSq (J : ℕ) :
    ∑ n ∈ cube J, 1 / ((mn n : ℝ) + 1) ^ 2 ≤ 26 * ((J : ℝ) + 1) := by
  refine (sum_cube_mn_le (f := fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2)
    (fun j => by positivity) J).trans ?_
  calc ∑ j ∈ Finset.range (J + 1), prof j * (1 / ((j : ℝ) + 1) ^ 2)
      ≤ ∑ _j ∈ Finset.range (J + 1), (26 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [prof, mul_one_div]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)]
        nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity, sq_nonneg (j : ℝ)]
    _ = 26 * ((J : ℝ) + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- `Σ_{n ∈ cube J} 1/(mn n + 1)³ ≤ 30 (1 + log (2 + J))`. -/
lemma cube_sum_invCube (J : ℕ) :
    ∑ n ∈ cube J, 1 / ((mn n : ℝ) + 1) ^ 3 ≤ 30 * (1 + Real.log (2 + (J : ℝ))) := by
  refine (sum_cube_mn_le (f := fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 3)
    (fun j => by positivity) J).trans ?_
  have hpt : ∀ j ∈ Finset.range (J + 1),
      prof j * (1 / ((j : ℝ) + 1) ^ 3) ≤ 24 * (1 / ((j : ℝ) + 1)) := by
    intro j _
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hnum : 24 * (j : ℝ) ^ 2 + 2 ≤ 24 * ((j : ℝ) + 1) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
    have hmain : (24 * (j : ℝ) ^ 2 + 2) / ((j : ℝ) + 1) ^ 3 ≤ 24 / ((j : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 3) hj1]
      calc (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) + 1)
          ≤ (24 * ((j : ℝ) + 1) ^ 2) * ((j : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hnum hj1.le
        _ = 24 * ((j : ℝ) + 1) ^ 3 := by ring
    calc prof j * (1 / ((j : ℝ) + 1) ^ 3)
        = (24 * (j : ℝ) ^ 2 + 2) / ((j : ℝ) + 1) ^ 3 := by simp only [prof, mul_one_div]
      _ ≤ 24 / ((j : ℝ) + 1) := hmain
      _ = 24 * (1 / ((j : ℝ) + 1)) := by rw [mul_one_div]
  calc ∑ j ∈ Finset.range (J + 1), prof j * (1 / ((j : ℝ) + 1) ^ 3)
      ≤ ∑ j ∈ Finset.range (J + 1), 24 * (1 / ((j : ℝ) + 1)) := Finset.sum_le_sum hpt
    _ = 24 * ∑ j ∈ Finset.range (J + 1), 1 / ((j : ℝ) + 1) := by rw [Finset.mul_sum]
    _ ≤ 24 * (1 + Real.log ((J : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_range_inv_succ_le J) (by norm_num)
    _ ≤ 30 * (1 + Real.log (2 + (J : ℝ))) := by
        have hl : Real.log ((J : ℝ) + 1) ≤ Real.log (2 + (J : ℝ)) :=
          Real.log_le_log (by positivity) (by linarith [show (0 : ℝ) ≤ (J : ℝ) by positivity])
        have h1 : (0 : ℝ) ≤ 1 + Real.log ((J : ℝ) + 1) := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ (J : ℝ) + 1 by
            linarith [show (0 : ℝ) ≤ (J : ℝ) by positivity])
          linarith
        nlinarith [hl, h1]

/-! ## 4. The target -/

theorem cubeMomSums (J : ℕ) :
    (∑ n ∈ Work.BoseBogFS.cube J, (1 : ℝ)) ≤ 27 * ((J : ℝ) + 1) ^ 3 ∧
    (∑ n ∈ Work.BoseBogFS.cube J, ((Work.BoseBogFS.mn n : ℝ) + 1)) ≤ 27 * ((J : ℝ) + 1) ^ 4 ∧
    (∑ n ∈ Work.BoseBogFS.cube J, 1 / ((Work.BoseBogFS.mn n : ℝ) + 1) ^ 2) ≤ 26 * ((J : ℝ) + 1) ∧
    (∑ n ∈ Work.BoseBogFS.cube J, 1 / ((Work.BoseBogFS.mn n : ℝ) + 1) ^ 3)
      ≤ 30 * (1 + Real.log (2 + (J : ℝ))) := by
  exact ⟨cube_sum_one J, cube_sum_mn_add_one J, cube_sum_invSq J, cube_sum_invCube J⟩

end Work.BoseBogFS
