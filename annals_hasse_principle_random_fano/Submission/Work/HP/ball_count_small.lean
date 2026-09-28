import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.sum_range_rank_two
import Submission.Work.HP.sum_bound_rank2

/-!
# Small-height consequences of the Schmidt (Schanuel) upper bound

Given the Schmidt upper bound for the number of lattice points in a ball,
`ballCount L T ≤ K (1 + T/λ₁ + T²/(λ₁λ₂) + … + T^R/(λ₁⋯λ_R))` with `R = rk L`,
this file extracts the three specialisations used downstream:

* `T = X` with `λ₁ ≤ X`  ⟹  `ballCount L X ≪ X^R / λ₁^R`  (rank-`1` shape),
* `T = Y` with `λ₂ ≤ Y`  ⟹  `ballCount L Y ≪ Y^R / (λ₁ λ₂^{R-1})`,
* `R = 2`                 ⟹  `ballCount L X ≪ X²/(λ₁λ₂) + X/λ₁ + 1`.

The constants produced by the reduction depend only on the ambient type `ι` (through
`#ι + 1`, the number of summands), which is exactly what the callers need.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product `∏_{j<e} lam L (j+1)` is at least `lam L 1 ^ e`, as long as `e ≤ rk L`. -/
lemma prod_range_lam_ge_one (L : Submodule ℤ (ι → ℤ)) {e : ℕ} (he : e ≤ rk L) :
    lam L 1 ^ e ≤ ∏ j ∈ Finset.range e, lam L (j + 1) := by
  have hconst : lam L 1 ^ e = ∏ _j ∈ Finset.range e, lam L 1 := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hconst]
  refine Finset.prod_le_prod₀ (fun j _ => lam_nonneg L 1) (fun j hj => ?_)
  have hjlt : j < e := Finset.mem_range.mp hj
  exact lam_mono L (by omega) (by omega)

/-- Each term of the Schmidt sum is at most `X ^ rk L / lam L 1 ^ rk L`, when `lam L 1 ≤ X`. -/
lemma term_le_one (L : Submodule ℤ (ι → ℤ)) {X : ℝ} (hX : 1 ≤ X) (hlam : lam L 1 ≤ X)
    {e : ℕ} (he : e ≤ rk L) :
    X ^ e / ∏ j ∈ Finset.range e, lam L (j + 1) ≤ X ^ rk L / lam L 1 ^ rk L := by
  by_cases he0 : e = 0
  · subst he0
    rw [Finset.range_zero, Finset.prod_empty, pow_zero, div_one]
    by_cases hr0 : rk L = 0
    · rw [hr0]; simp
    · have hr1 : 1 ≤ rk L := by omega
      have hpos : 0 < lam L 1 := lam_pos L le_rfl hr1
      have hb : 1 ≤ X / lam L 1 := (one_le_div hpos).mpr hlam
      have h1 : 1 ≤ (X / lam L 1) ^ rk L := one_le_pow₀ hb
      rwa [div_pow] at h1
  · have he1 : 1 ≤ e := by omega
    have hprod : lam L 1 ^ e ≤ ∏ j ∈ Finset.range e, lam L (j + 1) :=
      prod_range_lam_ge_one L he
    have hlam1pos : 0 < lam L 1 := lam_pos L le_rfl (le_trans he1 he)
    have hXe : 0 ≤ X ^ e := pow_nonneg (by linarith) e
    have hstep : X ^ e / (∏ j ∈ Finset.range e, lam L (j + 1)) ≤ X ^ e / lam L 1 ^ e :=
      div_le_div_of_nonneg_left hXe (pow_pos hlam1pos e) hprod
    have hb : 1 ≤ X / lam L 1 := (one_le_div hlam1pos).mpr hlam
    have hstep2 : X ^ e / lam L 1 ^ e ≤ X ^ rk L / lam L 1 ^ rk L := by
      rw [← div_pow, ← div_pow]
      exact pow_le_pow_right₀ hb he
    exact hstep.trans hstep2

/-- Goal-1 sum bound: the Schmidt sum is `≪_ι X ^ rk L / lam L 1 ^ rk L` when `lam L 1 ≤ X`. -/
lemma sum_bound_rank1 (L : Submodule ℤ (ι → ℤ)) {X : ℝ} (hX : 1 ≤ X) (hlam : lam L 1 ≤ X) :
    (∑ i ∈ Finset.range (rk L + 1),
        X ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
      ≤ (Fintype.card ι + 1 : ℝ) * (X ^ rk L / lam L 1 ^ rk L) := by
  have hCnn : 0 ≤ X ^ rk L / lam L 1 ^ rk L :=
    div_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (lam_nonneg L 1) _)
  have hterm : ∀ i ∈ Finset.range (rk L + 1),
      X ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1)
        ≤ X ^ rk L / lam L 1 ^ rk L := fun i _ => term_le_one L hX hlam (Nat.sub_le _ _)
  calc (∑ i ∈ Finset.range (rk L + 1),
          X ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
      ≤ ∑ _i ∈ Finset.range (rk L + 1), (X ^ rk L / lam L 1 ^ rk L) :=
        Finset.sum_le_sum hterm
    _ = (rk L + 1 : ℝ) * (X ^ rk L / lam L 1 ^ rk L) := by
        rw [Finset.sum_const, Finset.card_range]; simp [nsmul_eq_mul]
    _ ≤ (Fintype.card ι + 1 : ℝ) * (X ^ rk L / lam L 1 ^ rk L) := by
        apply mul_le_mul_of_nonneg_right _ hCnn
        have h := rk_le_card L
        have h' : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h
        linarith

theorem ball_count_small (ι : Type) [Fintype ι] [DecidableEq ι]
    (hsch : ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∑ i ∈ Finset.range (rk L + 1),
        T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1)) :
    ∃ K : ℝ, 0 < K ∧
      ((∀ (L : Submodule ℤ (ι → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
          (ballCount L X : ℝ) ≤ K * X ^ rk L / lam L 1 ^ rk L) ∧
       (∀ (L : Submodule ℤ (ι → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
          (ballCount L Y : ℝ) ≤ K * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) ∧
       (∀ (L : Submodule ℤ (ι → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
          (ballCount L X : ℝ) ≤ K * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1))) := by
  obtain ⟨Ks, hKs, hbound⟩ := hsch
  have hKpos : (0 : ℝ) < Ks * (Fintype.card ι + 1 : ℝ) :=
    mul_pos hKs (by exact_mod_cast Nat.succ_pos (Fintype.card ι))
  refine ⟨Ks * (Fintype.card ι + 1 : ℝ), hKpos, ?_, ?_, ?_⟩
  · intro L X hX hlam
    have hb := hbound L X hX
    have hs := sum_bound_rank1 L hX hlam
    refine le_trans hb ?_
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hs (le_of_lt hKs)
  · intro L Y hY hr hlam
    have hb := hbound L Y hY
    have hs := sum_bound_rank2 L hY hr hlam
    refine le_trans hb ?_
    rw [mul_div_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hs (le_of_lt hKs)
  · intro L X hrk hX
    have hb := hbound L X hX
    rw [sum_range_rank_two L X hrk] at hb
    have hSnn : 0 ≤ X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1 := by
      have h1 : 0 ≤ X ^ 2 / (lam L 1 * lam L 2) :=
        div_nonneg (sq_nonneg X) (mul_nonneg (lam_nonneg L 1) (lam_nonneg L 2))
      have h2 : 0 ≤ X / lam L 1 := div_nonneg (by linarith) (lam_nonneg L 1)
      linarith
    refine le_trans hb ?_
    have hle : Ks ≤ Ks * (Fintype.card ι + 1 : ℝ) := by
      have hc : (1 : ℝ) ≤ (Fintype.card ι + 1 : ℝ) := by
        have h : (1 : ℕ) ≤ Fintype.card ι + 1 := Nat.succ_le_succ (Nat.zero_le _)
        exact_mod_cast h
      nlinarith [hKs]
    exact mul_le_mul_of_nonneg_right hle hSnn

end Work.HP
