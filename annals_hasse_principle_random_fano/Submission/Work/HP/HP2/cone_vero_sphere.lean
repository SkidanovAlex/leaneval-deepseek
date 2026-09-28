import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic

namespace Work.HP.HP2

open Finset

/-- At least one coordinate of a vector of `rNorm` exactly `1` has modulus `≥ (√(n+1))⁻¹`. -/
lemma sqrt_inv_card_le_abs_coord (n : ℕ) (u : Fin (n + 1) → ℝ) (hu : rNorm u = 1) :
    ∃ j : Fin (n + 1), (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ |u j| := by
  obtain ⟨j, _, hjmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1))) (fun i => |u i|)
      Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hsum : ∑ i : Fin (n + 1), (u i) ^ 2 = 1 := by
    have h := rNorm_sq u
    rw [hu] at h
    simpa using h.symm
  have hle : ∀ i : Fin (n + 1), (u i) ^ 2 ≤ (u j) ^ 2 := fun i => by
    have h := hjmax i (Finset.mem_univ i)
    calc (u i) ^ 2 = |u i| ^ 2 := by rw [sq_abs]
      _ ≤ |u j| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (u j) ^ 2 := by rw [sq_abs]
  have hsum2 : ∑ _i : Fin (n + 1), (u j) ^ 2 = ((n : ℝ) + 1) * (u j) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hprod : (1 : ℝ) ≤ ((n : ℝ) + 1) * (u j) ^ 2 := by
    calc (1 : ℝ) = ∑ i : Fin (n + 1), (u i) ^ 2 := hsum.symm
      _ ≤ ∑ _i : Fin (n + 1), (u j) ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = ((n : ℝ) + 1) * (u j) ^ 2 := hsum2
  have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ (u j) ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    calc (1 : ℝ) ≤ ((n : ℝ) + 1) * (u j) ^ 2 := hprod
      _ = (u j) ^ 2 * ((n : ℝ) + 1) := by ring
  have hsq : ((Real.sqrt ((n : ℝ) + 1))⁻¹) ^ 2 = 1 / ((n : ℝ) + 1) := by
    rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
  have h4 : ((Real.sqrt ((n : ℝ) + 1))⁻¹) ^ 2 ≤ (u j) ^ 2 := by
    rw [hsq]; exact h3
  have h5 : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤ |u j| := by
    have h := (sq_le_sq.mp h4)
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹)] at h
  exact h5

/-- The exponent vector `d·e_j` (the monomial `x_j^d`). -/
def diracMon (d n : ℕ) (j : Fin (n + 1)) : Mon d n :=
  ⟨Function.update (0 : Fin (n + 1) → Fin (d + 1)) j ⟨d, Nat.lt_succ_self d⟩, by
    rw [Finset.sum_eq_single j
      (fun i _ hij => by simp [Function.update_of_ne hij])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp⟩

/-- The Veronese coordinate of the monomial `d·e_j` is `u j ^ d`. -/
lemma veronese_diracMon (d n : ℕ) (u : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    veronese d n u (diracMon d n j) = u j ^ d := by
  rw [veronese, Finset.prod_eq_single j
    (fun i _ hij => by
      have h : (diracMon d n j).1 i = 0 := by simp [diracMon, Function.update_of_ne hij]
      rw [h]; simp)
    (fun h => absurd (Finset.mem_univ j) h)]
  simp [diracMon]

/-- The Veronese map does not come close to vanishing on the unit sphere.
Route: an explicit constant is easiest. Take `j` maximising `|u j|`, so `|u j| ≥ 1 / √(n+1)`, and
the monomial `m = d·e_j` (i.e. `Function.update 0 j ⟨d, Nat.lt_succ_self d⟩`, which lies in `Mon d n`)
satisfies `veronese d n u m = u j ^ d`; hence `rNorm (veronese d n u) ≥ |u j| ^ d ≥ (√(n+1))⁻¹ ^ d`. -/
theorem cone_vero_sphere (d n : ℕ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ u : Fin (n + 1) → ℝ, rNorm u = 1 → c₁ ≤ rNorm (veronese d n u) := by
  refine ⟨((Real.sqrt ((n : ℝ) + 1))⁻¹) ^ d,
    pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) d, fun u hu => ?_⟩
  obtain ⟨j, hj⟩ := sqrt_inv_card_le_abs_coord n u hu
  have hmem : |u j ^ d| ≤ rNorm (veronese d n u) := by
    have h := abs_apply_le_rNorm (veronese d n u) (diracMon d n j)
    rwa [veronese_diracMon d n u j] at h
  rw [abs_pow] at hmem
  exact le_trans (pow_le_pow_left₀ (by positivity) hj d) hmem

end Work.HP.HP2
