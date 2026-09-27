import Mathlib
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow
open Matrix

noncomputable section

variable {n : ℕ}

/-- The two hyperboloid lifts `hlift ((1/4) e_j)` and `hlift (-(1/4) e_j)` differ by
half the basis vector `e_j` in the spatial part (they have the same time part). -/
private lemma hlift_diff_single (j : Fin n) :
    hlift (EuclideanSpace.single j (1 / 4 : ℝ) : E n) -
      hlift (EuclideanSpace.single j (-(1 / 4) : ℝ) : E n)
    = (1 / 2 : ℝ) • Pi.single (Sum.inl j) (1 : ℝ) := by
  ext k
  rcases k with k | k
  · rw [Pi.sub_apply, hlift_inl, hlift_inl, Pi.smul_apply,
      PiLp.single_apply, PiLp.single_apply]
    by_cases h : k = j
    · simp only [h, ↓reduceIte]; norm_num
    · simp [h]
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    rw [Pi.sub_apply, hlift_inr, hlift_inr, Pi.smul_apply]
    have hp : ‖(EuclideanSpace.single j (1 / 4 : ℝ) : E n)‖ = ‖(1 / 4 : ℝ)‖ :=
      PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (1 / 4)
    have hq : ‖(EuclideanSpace.single j (-(1 / 4) : ℝ) : E n)‖ = ‖(-(1 / 4) : ℝ)‖ :=
      PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (-(1 / 4))
    have htp : tpart (EuclideanSpace.single j (1 / 4 : ℝ) : E n)
        = tpart (EuclideanSpace.single j (-(1 / 4) : ℝ) : E n) := by
      rw [tpart, tpart, hp, hq]; norm_num
    rw [htp]
    simp

/-- A single coordinate of a vector is bounded by `K` as soon as the square root of the
`ℓ²` sum of squares of the vector is `≤ K`. -/
private lemma abs_le_of_sqrt_sum_sq_le {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (K : ℝ) (hv : Real.sqrt (∑ k, v k ^ 2) ≤ K) (i : ι) : |v i| ≤ K := by
  have h1 : v i ^ 2 ≤ ∑ k, v k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  exact le_trans (Real.abs_le_sqrt h1) hv

theorem entry_le_of_hlift_bound (n : ℕ)
    (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ u : Submission.Mostow.E n, ‖u‖ ≤ 1 / 4 →
      Real.sqrt (∑ i, (Matrix.mulVec A (Submission.Mostow.hlift u)) i ^ 2) ≤ K) :
    ∀ i j : Fin n ⊕ Fin 1, |A i j| ≤ 4 * K := by
  -- The time vector: `hlift 0` is the basis vector at `Sum.inr 0`.
  have ht : ∀ i : Fin n ⊕ Fin 1, |A i (Sum.inr 0)| ≤ 4 * K := by
    intro i
    have h0 : Real.sqrt (∑ k, (A *ᵥ hlift (0 : E n)) k ^ 2) ≤ K := h 0 (by simp)
    have hv : (A *ᵥ hlift (0 : E n)) i = A i (Sum.inr 0) := by
      rw [hlift_zero, Matrix.mulVec_single_one]; rfl
    have := abs_le_of_sqrt_sum_sq_le (A *ᵥ hlift (0 : E n)) K h0 i
    rw [hv] at this
    linarith
  -- The spatial vectors: subtract the two lifts of `±(1/4) e_j`.
  have hs : ∀ (i : Fin n ⊕ Fin 1) (j : Fin n), |A i (Sum.inl j)| ≤ 4 * K := by
    intro i j
    set p : E n := EuclideanSpace.single j (1 / 4 : ℝ) with hpdef
    set q : E n := EuclideanSpace.single j (-(1 / 4) : ℝ) with hqdef
    have hpn : ‖p‖ ≤ 1 / 4 := by
      rw [hpdef, PiLp.norm_single 2 (fun _ : Fin n => ℝ)]; norm_num
    have hqn : ‖q‖ ≤ 1 / 4 := by
      rw [hqdef, PiLp.norm_single 2 (fun _ : Fin n => ℝ)]; norm_num
    have hp := abs_le_of_sqrt_sum_sq_le (A *ᵥ hlift p) K (h p hpn) i
    have hq := abs_le_of_sqrt_sum_sq_le (A *ᵥ hlift q) K (h q hqn) i
    have hsub : (A *ᵥ hlift p) - (A *ᵥ hlift q) = (1 / 2 : ℝ) • A.col (Sum.inl j) := by
      rw [← Matrix.mulVec_sub, hpdef, hqdef, hlift_diff_single j, Matrix.mulVec_smul,
        Matrix.mulVec_single_one]
    have hkey : (A *ᵥ hlift p) i - (A *ᵥ hlift q) i = (1 / 2) * A i (Sum.inl j) := by
      have := congrFun hsub i
      simpa [Matrix.col_apply, smul_eq_mul] using this
    have h2 : |A i (Sum.inl j)| = 2 * |(A *ᵥ hlift p) i - (A *ᵥ hlift q) i| := by
      rw [hkey, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    rw [h2]
    calc 2 * |(A *ᵥ hlift p) i - (A *ᵥ hlift q) i|
        ≤ 2 * (|(A *ᵥ hlift p) i| + |(A *ᵥ hlift q) i|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
      _ ≤ 2 * (K + K) := by linarith
      _ = 4 * K := by ring
  intro i j
  rcases j with j | j
  · exact hs i j
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    exact ht i

end

end Work.Mostow
