import Mathlib
import Submission.Commons.LinearAlgebra.Net.compress_slice_net

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

open Finset


/-- squared distance from `x` to its truncation on `A` equals sum of squares off `A` -/
lemma incompressible_spread_sqNorm_sub_res {n : ℕ} (A : Finset (Fin n)) (x : Fin n → ℝ) :
    sqNorm (x - res A x) = ∑ i ∈ (Finset.univ.filter (fun i : Fin n => i ∉ A)), (x i)^2 := by
  unfold sqNorm res
  calc
    (∑ i : Fin n, ((x i - (if i ∈ A then x i else 0))^2)) = ∑ i : Fin n, (if i ∈ A then 0 else (x i)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hA : i ∈ A <;> simp [hA]
    _ = ∑ i ∈ (Finset.univ.filter (fun i : Fin n => i ∉ A)), (x i)^2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hA : i ∈ A <;> simp [hA]

/-- Rudelson–Vershynin "incompressible vectors are spread" (lower part):
an incompressible unit vector has many coordinates bounded away from zero.
Here `incompressible` is spelled out as: not every truncation within squared
distance `ν²` has support at most `δ·n`.  The conclusion: at least
`(1/2)·ν²·δ·n` coordinates have `|x_i| ≥ ν/(2·√n)`. -/
theorem incompressible_spread {n : ℕ} (hn : 1 ≤ n) {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν)
    (x : Fin n → ℝ) (hx : sqNorm x = 1)
    (hnot : ∀ z : Fin n → ℝ, sqNorm (x - z) ≤ ν ^ 2 →
        ¬ (((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ))) :
    ∃ σ : Finset (Fin n),
      ((σ.card : ℝ) ≥ (1 / 2) * ν ^ 2 * δ * (n : ℝ)) ∧
      (∀ i : Fin n, i ∈ σ → ν / (2 * Real.sqrt (n : ℝ)) ≤ |x i|) := by
  classical
  have hn0r : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hδn_pos : 0 < δ * (n : ℝ) := mul_pos hδ hn0r
  -- (1/2)ν² ≤ 1 must hold, otherwise z=0 would witness compressibility of x.
  have hfrac : (1 / 2) * ν ^ 2 ≤ 1 := by
    by_contra h
    have h1le : 1 ≤ ν ^ 2 := by
      have hgt : 1 < (1 / 2) * ν ^ 2 := lt_of_not_ge h
      nlinarith
    have hsub0 : x - (0 : Fin n → ℝ) = x := by
      funext i
      simp
    have h1sq : sqNorm (x - (0 : Fin n → ℝ)) ≤ ν ^ 2 := by
      rw [hsub0, hx]
      exact h1le
    have hcontra : ¬ (((Finset.univ.filter (fun i => (0 : Fin n → ℝ) i ≠ 0)).card : ℝ) ≤ δ * (n : ℝ)) :=
      hnot (0 : Fin n → ℝ) h1sq
    have hc0 : (Finset.univ.filter (fun i : Fin n => (0 : Fin n → ℝ) i ≠ 0)).card = 0 := by simp
    exact hcontra (by simpa [hc0] using (le_of_lt hδn_pos))
  -- threshold and set of large coordinates
  let t : ℝ := ν / (2 * Real.sqrt (n : ℝ))
  let A : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => t ≤ |x i|)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0r
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hν (mul_pos (by norm_num) hsqrt_pos)
  -- z is the truncation keeping only the large coordinates
  let z : Fin n → ℝ := res A x
  -- bound the squared distance from x to z
  have hzsq : sqNorm (x - z) ≤ ν ^ 2 := by
    let B : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i ∉ A)
    have hterm : ∀ i ∈ B, (x i)^2 ≤ t^2 := by
      intro i hi
      have hiB : i ∉ A := (Finset.mem_filter.mp hi).2
      have hnot1 : ¬ t ≤ |x i| := by
        simpa [A] using hiB
      have hlt : |x i| < t := lt_of_not_ge hnot1
      exact (sq_le_sq).2 (by simpa [abs_of_nonneg (le_of_lt ht_pos)] using le_of_lt hlt)
    have hsumB : (∑ i ∈ B, (x i)^2) ≤ (B.card : ℝ) * t^2 := by
      have h := Finset.sum_le_card_nsmul B (fun i => (x i)^2) (t^2) hterm
      simpa using h
    have hBcard : (B.card : ℝ) ≤ (n : ℝ) := by
      dsimp [B]
      have hc : (Finset.univ.filter (fun i : Fin n => i ∉ A)).card ≤ n := by
        simpa using (Finset.card_le_card
          (Finset.filter_subset (fun i : Fin n => i ∉ A) (Finset.univ : Finset (Fin n))))
      exact_mod_cast hc
    have hBsum : (B.card : ℝ) * t^2 ≤ (n : ℝ) * t^2 :=
      mul_le_mul_of_nonneg_right hBcard (sq_nonneg t)
    have hs : (Real.sqrt (n : ℝ))^2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn0r)
    have hmain : (n : ℝ) * t^2 ≤ ν ^ 2 := by
      have ht2 : t^2 = ν ^ 2 / (4 * (n : ℝ)) := by
        dsimp [t]
        rw [div_pow]
        have hden : (2 * Real.sqrt (n : ℝ))^2 = 4 * (n : ℝ) := by nlinarith [hs]
        rw [hden]
      calc
        (n : ℝ) * t^2 = (n : ℝ) * (ν ^ 2 / (4 * (n : ℝ))) := by rw [ht2]
        _ = ν ^ 2 / 4 := by
          field_simp [show (4 * (n : ℝ)) ≠ 0 by nlinarith]
        _ ≤ ν ^ 2 := by nlinarith [sq_nonneg ν]
    calc
      sqNorm (x - z) = ∑ i ∈ B, (x i)^2 := by
        dsimp [z, B]
        exact incompressible_spread_sqNorm_sub_res A x
      _ ≤ (B.card : ℝ) * t^2 := hsumB
      _ ≤ (n : ℝ) * t^2 := hBsum
      _ ≤ ν ^ 2 := hmain
  -- support of z equals A (t > 0 so large coords are non-zero)
  have hsupp : Finset.univ.filter (fun i : Fin n => z i ≠ 0) = A := by
    ext i
    by_cases hi : i ∈ A
    · constructor
      · intro _
        exact hi
      · intro _
        have hle : t ≤ |x i| := (Finset.mem_filter.mp hi).2
        have hxi : x i ≠ 0 := by
          intro hx0
          have : |x i| = 0 := by simp [hx0]
          linarith
        simpa [z, res, hi] using hxi
    · constructor
      · intro hmem
        have : z i ≠ 0 := (Finset.mem_filter.mp hmem).2
        simp [z, hi] at this
      · intro hmemA
        exact (hi hmemA).elim
  -- incompressibility forces many large coordinates
  have hA_not : ¬ (((A.card : ℝ)) ≤ δ * (n : ℝ)) := by
    simpa [hsupp] using (hnot z hzsq)
  have hlt_card : δ * (n : ℝ) < (A.card : ℝ) := lt_of_not_ge hA_not
  have hval : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤ δ * (n : ℝ) := by
    calc
      (1 / 2) * ν ^ 2 * δ * (n : ℝ) = ((1 / 2) * ν ^ 2) * (δ * (n : ℝ)) := by ring
      _ ≤ 1 * (δ * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfrac (le_of_lt hδn_pos)
      _ = δ * (n : ℝ) := by ring
  have hconcl : (1 / 2) * ν ^ 2 * δ * (n : ℝ) ≤ (A.card : ℝ) :=
    le_trans hval (le_of_lt hlt_card)
  refine ⟨A, hconcl, ?_⟩
  intro i hi
  have ht_le : t ≤ |x i| := (Finset.mem_filter.mp hi).2
  simpa [t] using ht_le

end Commons.LinearAlgebra.Net
