import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.latticeSumBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.summable_profile_three`

Summability of the lattice profiles `1 / ((1 + m‖n‖)^k ‖n‖^l)` over the dual lattice
`n : Fin 3 → ℤ` embedded as `lpt 1 n`.  This is the `Summable` companion of the *bound* family
`Work.BoseBogFS.latticeSumBounds` (`tsum_two_cube`, `tsum_two_sq`, `tsum_three_four`): those were
proved with `Real.tsum_le_of_sum_le`, which controls only the value of the `tsum`, while for a
general profile that is not *a priori* summable (where Lean's `tsum` is the junk value `0`) the
summability itself is a strictly stronger statement.

## Method

`summable_lattice_of_profile` is the general mechanism: for a nonnegative profile `g` decreasing on
`(0,∞)` whose one-dimensional shell series is bounded, `n ↦ g ‖lpt 1 n‖` is summable.  The proof
bounds every finite partial sum by the shell decomposition of `latticeSumBounds`,

`∑_{n ∈ s} g ‖n‖ ≤ ∑_{n ∈ cube (s.sup mn)} g ‖n‖ ≤ ∑_{j ≤ s.sup mn} prof j * g j ≤ L`,

(after computing `cube` via `sum_le_cube_sum` and `sum_cube_le`) and then applies
`summable_of_sum_le`.  The three requested profiles are instances, with the one-dimensional bounds
`latSumOneDTwoCube` / `latSumOneDTwoSq` / `latSumOneDThreeFour`; `latSumProfile` supplies the same
kind of bound for an arbitrary exponent pair `k ≥ 1`, `l ≥ 1`, `k + l ≥ 4`, giving the general
`summable_profile_general`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

/-- **Summability reduction.**  If the profile `g` is nonnegative, decreasing on `(0,∞)`, and its
one-dimensional shell series is bounded by `L`, then `n ↦ g ‖lpt 1 n‖` is summable on the lattice
`ℤ³`.  This is the `Summable` companion of `Work.BoseBogFS.tsum_le_of_cube`. -/
lemma summable_lattice_of_profile {g : ℝ → ℝ} (hg0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ g r)
    (hdec : ∀ ⦃a b : ℝ⦄, 0 < a → a ≤ b → g b ≤ g a) {L : ℝ}
    (hL : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), prof j * g (j : ℝ) ≤ L) :
    Summable fun n : Fin 3 → ℤ => g ‖lpt 1 n‖ := by
  refine summable_of_sum_le (c := L) (fun n => hg0 _ (norm_nonneg _)) fun s => ?_
  calc ∑ n ∈ s, g ‖lpt 1 n‖
      ≤ ∑ n ∈ cube (s.sup mn), g ‖lpt 1 n‖ := sum_le_cube_sum hg0 s
    _ ≤ ∑ j ∈ Finset.range (s.sup mn + 1), prof j * g (j : ℝ) := sum_cube_le hg0 hdec _
    _ ≤ L := hL _

/-- `Σ_n 1 / ((1 + m‖n‖)² ‖n‖³)` is summable over the lattice `ℤ³` (`m > 0`). -/
lemma summable_two_cube_profile (m : ℝ) (hm : 0 < m) :
    Summable (fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 3)) :=
  summable_lattice_of_profile (g := fun r : ℝ => 1 / ((1 + m * r) ^ 2 * r ^ 3))
    (fun r _ => by positivity)
    (antitone_inv_mul m hm 2 3 (by norm_num) (by norm_num))
    (fun J => by simpa only [prof] using latSumOneDTwoCube m hm J)

/-- `Σ_n 1 / ((1 + m‖n‖)² ‖n‖²)` is summable over the lattice `ℤ³` (`m > 0`). -/
lemma summable_two_sq_profile (m : ℝ) (hm : 0 < m) :
    Summable (fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 2 * ‖lpt 1 n‖ ^ 2)) :=
  summable_lattice_of_profile (g := fun r : ℝ => 1 / ((1 + m * r) ^ 2 * r ^ 2))
    (fun r _ => by positivity)
    (antitone_inv_mul m hm 2 2 (by norm_num) (by norm_num))
    (fun J => by simpa only [prof] using latSumOneDTwoSq m hm J)

/-- `Σ_n 1 / ((1 + m‖n‖)³ ‖n‖⁴)` is summable over the lattice `ℤ³` (`m > 0`). -/
lemma summable_three_four_profile (m : ℝ) (hm : 0 < m) :
    Summable (fun n : Fin 3 → ℤ =>
      1 / ((1 + m * ‖lpt 1 n‖) ^ 3 * ‖lpt 1 n‖ ^ 4)) :=
  summable_lattice_of_profile (g := fun r : ℝ => 1 / ((1 + m * r) ^ 3 * r ^ 4))
    (fun r _ => by positivity)
    (antitone_inv_mul m hm 3 4 (by norm_num) (by norm_num))
    (fun J => by simpa only [prof] using latSumOneDThreeFour m hm J)

/-! ## A general exponent pair -/

/-- The one-dimensional shell series of the profile `1 / ((1 + m r)^k r^l)` is bounded by
`52 / m^k` whenever `k ≥ 1`, `l ≥ 1` and `k + l ≥ 4`. -/
lemma latSumProfile (m : ℝ) (hm : 0 < m) (k l : ℕ) (hl : 1 ≤ l) (hkl : 4 ≤ k + l) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1),
        prof j * (1 / ((1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l))) ≤ 52 / m ^ k := by
  have hmk : (0 : ℝ) < m ^ k := pow_pos hm k
  have hterm : ∀ j : ℕ,
      prof j * (1 / ((1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l))
        ≤ (26 / m ^ k) * (1 / (j : ℝ) ^ 2) := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hl0 : l ≠ 0 := by omega
      norm_num [prof, zero_pow hl0]
    · have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
      have hjne : (j : ℝ) ≠ 0 := ne_of_gt hj0
      have hmkne : m ^ k ≠ 0 := ne_of_gt hmk
      have hpow : (j : ℝ) ^ 4 ≤ (j : ℝ) ^ k * (j : ℝ) ^ l := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (by linarith) hkl
      have hnum : prof j ≤ 26 * (j : ℝ) ^ 2 := by
        have hsq : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
        simp only [prof]
        nlinarith
      have hmj : m ^ k * (j : ℝ) ^ k = (m * (j : ℝ)) ^ k := (mul_pow m (j : ℝ) k).symm
      have hden : m ^ k * ((j : ℝ) ^ k * (j : ℝ) ^ l)
          ≤ (1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l := by
        have h1 : (m * (j : ℝ)) ^ k ≤ (1 + m * (j : ℝ)) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) k
        rw [← mul_assoc, hmj]
        exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hj0.le l)
      calc prof j * (1 / ((1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l))
          = prof j / ((1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l) := by rw [mul_one_div]
        _ ≤ (26 * (j : ℝ) ^ 2) / ((1 + m * (j : ℝ)) ^ k * (j : ℝ) ^ l) :=
              div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (26 * (j : ℝ) ^ 2) / (m ^ k * ((j : ℝ) ^ k * (j : ℝ) ^ l)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ ≤ (26 * (j : ℝ) ^ 2) / (m ^ k * (j : ℝ) ^ 4) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (mul_le_mul_of_nonneg_left hpow hmk.le)
        _ = (26 / m ^ k) * (1 / (j : ℝ) ^ 2) := by
              field_simp [hmkne, hjne]
  rw [Finset.sum_range_succ']
  have h0 : prof 0 * (1 / ((1 + m * ((0 : ℕ) : ℝ)) ^ k * ((0 : ℕ) : ℝ) ^ l)) = 0 := by
    have hl0 : l ≠ 0 := by omega
    norm_num [prof, zero_pow hl0]
  rw [h0, add_zero]
  calc (∑ j ∈ Finset.range J,
        prof (j + 1) * (1 / ((1 + m * ((j + 1 : ℕ) : ℝ)) ^ k * ((j + 1 : ℕ) : ℝ) ^ l)))
      ≤ ∑ j ∈ Finset.range J, (26 / m ^ k) * (1 / ((j : ℝ) + 1) ^ 2) := by
        refine Finset.sum_le_sum fun j _ => ?_
        simpa only [Nat.cast_add, Nat.cast_one] using hterm (j + 1)
    _ = (26 / m ^ k) * (∑ j ∈ Finset.range J, 1 / ((j : ℝ) + 1) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ (26 / m ^ k) * 2 := by
        refine mul_le_mul_of_nonneg_left (latTelescopeSuccSq J) (by positivity)
    _ = 52 / m ^ k := by ring

/-- `Σ_n 1 / ((1 + m‖n‖)^k ‖n‖^l)` is summable for `k ≥ 1`, `l ≥ 1`, `k + l ≥ 4`. -/
lemma summable_profile_general (m : ℝ) (hm : 0 < m) (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hkl : 4 ≤ k + l) :
    Summable (fun n : Fin 3 → ℤ => 1 / ((1 + m * ‖lpt 1 n‖) ^ k * ‖lpt 1 n‖ ^ l)) :=
  summable_lattice_of_profile (g := fun r : ℝ => 1 / ((1 + m * r) ^ k * r ^ l))
    (fun r _ => by positivity)
    (antitone_inv_mul m hm k l (by omega) (by omega))
    (fun J => latSumProfile m hm k l hl hkl J)

theorem summable_profile_three (m : ℝ) (hm : 0 < m) :
    Summable (fun n : Fin 3 → ℤ =>
        1 / ((1 + m * ‖Work.BoseBogFS.lpt 1 n‖) ^ 2 * ‖Work.BoseBogFS.lpt 1 n‖ ^ 3))
      ∧ Summable (fun n : Fin 3 → ℤ =>
        1 / ((1 + m * ‖Work.BoseBogFS.lpt 1 n‖) ^ 2 * ‖Work.BoseBogFS.lpt 1 n‖ ^ 2))
      ∧ Summable (fun n : Fin 3 → ℤ =>
        1 / ((1 + m * ‖Work.BoseBogFS.lpt 1 n‖) ^ 3 * ‖Work.BoseBogFS.lpt 1 n‖ ^ 4)) :=
  ⟨summable_two_cube_profile m hm, summable_two_sq_profile m hm,
    summable_three_four_profile m hm⟩


end Work.BoseBogFS
