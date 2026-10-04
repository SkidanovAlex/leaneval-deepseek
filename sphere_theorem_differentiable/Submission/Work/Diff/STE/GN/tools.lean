import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tools for the Gagliardo–Nirenberg inequality on the torus

This file sets up the Nirenberg levels and records the elementary facts about the exponents
`p k = 2m/k` that are used in the discrete log-convexity argument.

For a `C^∞`, `1`-periodic `f : (ι → ℝ) → ℂ` and `1 ≤ k ≤ m` we put

* `gnP m k = 2m/k` (the `L^p` exponent of the `k`-th level),
* `gnLev m f k = (∑_{l : Fin k → ι} ∫_{cube} ‖∂^l f‖ ^ (gnP m k)) ^ (1 / gnP m k)` `=: P k`,
* `gnSeq m U f k = if k = 0 then U else gnLev m f k` (the level `0` is the sup bound `U`).

The two identities that make Nirenberg's induction work are
`1/(p (k-1)) + 1/(p (k+1)) = 2/(p k)` (so that the three exponents
`p (k-1)`, `m/(m-k)`, `p (k+1)` sum to `1` in reciprocals) and `(p k - 2) * m/(m-k) = p k`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gagliardo–Nirenberg exponents `p k = 2m/k`. -/
noncomputable def gnP (m k : ℕ) : ℝ := (2 * (m : ℝ)) / (k : ℝ)

/-- The middle Hölder exponent in the `k`-th step (`k ≥ 2`). -/
noncomputable def gnB (m k : ℕ) : ℝ := (m : ℝ) / ((m - k : ℕ) : ℝ)

/-- The constant of the `k`-th Nirenberg step. -/
noncomputable def gnC (m k : ℕ) : ℝ :=
  max 0 (((Fintype.card (Fin k → ι) : ℕ) : ℝ) ^ (2 / gnP m k) * (gnP m k - 1))

/-- The level-`k` norm `P k`. -/
noncomputable def gnLev (m : ℕ) (f : (ι → ℝ) → ℂ) (k : ℕ) : ℝ :=
  (∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l f x‖ ^ (gnP m k)) ^ (1 / gnP m k)

/-- The sequence of Nirenberg levels with the `0`-th term replaced by the sup bound `U`. -/
noncomputable def gnSeq (m : ℕ) (U : ℝ) (f : (ι → ℝ) → ℂ) (k : ℕ) : ℝ :=
  if k = 0 then U else gnLev m f k

/-! ### Elementary facts about the exponents -/

lemma gnP_pos {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : 0 < gnP m k := by
  rw [gnP]
  have hk0 : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  exact div_pos (by linarith) hk0

lemma gnP_ne_zero {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : gnP m k ≠ 0 :=
  ne_of_gt (gnP_pos hk hkm)

lemma gnP_two_le {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : 2 ≤ gnP m k := by
  have hk0 : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkm' : ((k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have key : (2 : ℝ) * ((k : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by linarith
  calc (2 : ℝ) = (2 * ((k : ℕ) : ℝ)) / ((k : ℕ) : ℝ) := by field_simp
    _ ≤ (2 * (m : ℝ)) / ((k : ℕ) : ℝ) := div_le_div_of_nonneg_right key (le_of_lt hk0)
    _ = gnP m k := by rw [gnP]

lemma gnP_ge_one {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) : 1 ≤ gnP m k :=
  le_trans (by norm_num) (gnP_two_le hk hkm)

lemma gnC_nonneg (m k : ℕ) : 0 ≤ gnC (ι := ι) m k := le_max_left _ _

/-- `(p k - 2) * m/(m-k) = p k`, the identity that makes the middle Hölder exponent work. -/
lemma gnB_mul (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) :
    (gnP m k - 2) * gnB m k = gnP m k := by
  rw [gnP, gnB, Nat.cast_sub (by omega : k ≤ m)]
  have hk0 : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  have hmk : (m : ℝ) - ((k : ℕ) : ℝ) ≠ 0 := by
    have : ((k : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : k < m)
    linarith
  field_simp

/-- The three Hölder exponents in the `k`-th step sum to one in reciprocals. -/
lemma gnB_holder_sum (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) :
    1 / gnP m (k - 1) + 1 / gnB m k + 1 / gnP m (k + 1) = 1 := by
  rw [gnP, gnP, gnB, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub (by omega : k ≤ m)]
  have hk0 : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hmk : (m : ℝ) - ((k : ℕ) : ℝ) ≠ 0 := by
    have : ((k : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : k < m)
    linarith
  field_simp
  push_cast
  ring

lemma gnB_ge_one (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) : 1 ≤ gnB m k := by
  rw [gnB]
  have hpos : (0 : ℝ) < (m : ℝ) - ((k : ℕ) : ℝ) := by
    have : ((k : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : k < m)
    linarith
  have hpos' : (0 : ℝ) < ((m - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ m)]
    exact hpos
  have hle : ((m - k : ℕ) : ℝ) ≤ (m : ℝ) := by
    rw [Nat.cast_sub (by omega : k ≤ m)]
    have : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := by positivity
    linarith
  calc (1 : ℝ) = ((m - k : ℕ) : ℝ) / ((m - k : ℕ) : ℝ) := (div_self (ne_of_gt hpos')).symm
    _ ≤ (m : ℝ) / ((m - k : ℕ) : ℝ) := div_le_div_of_nonneg_right hle (le_of_lt hpos')

/-- The `k = 1` case of `gnB_mul`. -/
lemma gnB_one_mul (m : ℕ) (hm : 2 ≤ m) : (gnP m 1 - 2) * gnB m 1 = gnP m 1 := by
  rw [gnP, gnB, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    linarith
  field_simp

/-- The conjugate exponents in the `k = 1` step. -/
lemma gnB_one_holder_sum (m : ℕ) (hm : 2 ≤ m) : 1 / gnB m 1 + 1 / gnP m 2 = 1 := by
  rw [gnP, gnB, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    linarith
  field_simp
  ring

lemma gnB_one_ge_one (m : ℕ) (hm : 2 ≤ m) : 1 ≤ gnB m 1 := by
  rw [gnB, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  have hpos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    linarith
  calc (1 : ℝ) = ((m : ℝ) - 1) / ((m : ℝ) - 1) := (div_self (ne_of_gt hpos)).symm
    _ ≤ (m : ℝ) / ((m : ℝ) - 1) := div_le_div_of_nonneg_right (by linarith) (le_of_lt hpos)

/-- The exponents at the endpoints of the Nirenberg chain. -/
lemma gnP_endpoint (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (1 - (j : ℝ) / m) * gnP m j = gnP m j - 2 ∧ ((j : ℝ) / m) * gnP m j = 2 := by
  rw [gnP]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  have hj0 : ((j : ℕ) : ℝ) ≠ 0 := by positivity
  constructor <;> field_simp <;> ring

lemma gnP_self (m : ℕ) (hm : 1 ≤ m) : gnP m m = 2 := by
  rw [gnP]
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  field_simp

/-! ### Positivity and the defining identity of the levels -/

lemma gnLev_nonneg (m : ℕ) (f : (ι → ℝ) → ℂ) (k : ℕ) : 0 ≤ gnLev m f k := by
  rw [gnLev]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun l _ =>
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _

/-- The defining identity `(P k) ^ (p k) = ∑_l ∫ ‖∂^l f‖ ^ (p k)`. -/
lemma gnLev_rpow (m : ℕ) (f : (ι → ℝ) → ℂ) {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (gnLev m f k) ^ (gnP m k)
      = ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l f x‖ ^ (gnP m k) := by
  have hA : 0 ≤ ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l f x‖ ^ (gnP m k) :=
    Finset.sum_nonneg fun l _ => integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hp0 : gnP m k ≠ 0 := gnP_ne_zero hk hkm
  rw [gnLev, ← Real.rpow_mul hA (1 / gnP m k) (gnP m k)]
  rw [show (1 / gnP m k) * gnP m k = 1 by field_simp, Real.rpow_one]

lemma gnSeq_zero (m : ℕ) (U : ℝ) (f : (ι → ℝ) → ℂ) : gnSeq m U f 0 = U := if_pos rfl

lemma gnSeq_of_pos (m : ℕ) (U : ℝ) (f : (ι → ℝ) → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    gnSeq m U f k = gnLev m f k := if_neg (by omega)

lemma gnSeq_nonneg (m : ℕ) {U : ℝ} (hU : 0 ≤ U) (f : (ι → ℝ) → ℂ) (k : ℕ) :
    0 ≤ gnSeq m U f k := by
  rw [gnSeq]
  split
  · exact hU
  · exact gnLev_nonneg m f k

/-! ### Smoothness and periodicity of iterated derivatives -/

lemma contDiff_pdVec_top {k : ℕ} (l : Fin k → ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (pdVec k l f) := by
  rw [contDiff_infty]
  intro n
  have h1 : ContDiff ℝ (((k + n : ℕ)) : ℕ∞) f := (contDiff_infty.mp hf) (k + n)
  have h2 := contDiff_pdList_of_contDiff (List.ofFn l) n f (by simpa [List.length_ofFn] using h1)
  simpa [pdVec] using h2

lemma periodic1_pdVec {k : ℕ} (l : Fin k → ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Periodic1 f) : Periodic1 (pdVec k l f) :=
  (pdVec_contDiff_periodic k k le_rfl l f ((contDiff_infty.mp hf) k) hper).2

end Work.Diff.STE
