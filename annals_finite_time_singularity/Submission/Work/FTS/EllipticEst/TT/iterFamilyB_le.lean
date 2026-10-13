import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- Elementary comparison for the `D_θ`-iterates of the factor `2 cos(2θ)`.

Given nonnegative families `A`, `D` and a dominating family `cB ≥ 0` with `A j ≤ cB j`, the
binomial convolution `∑_j C(m,j)² · A j · D (m-j)` is bounded by
`(∑_j 4^m · cB j) · (∑_k D k)`.

Indeed `C(m,j) ≤ 2^m`, so `C(m,j)² ≤ 4^m`, whence each summand is at most
`4^m · cB j · D (m-j)`; and since `m - j ∈ range (m+1)` for `j ∈ range (m+1)` and all `D k ≥ 0`,
each `D (m-j)` is at most `∑_k D k`, the factor `4^m · cB j` being nonnegative. -/
private theorem sum_choose_sq_mul_le {A D cB : ℕ → ℝ} (m : ℕ)
    (hA : ∀ j, 0 ≤ A j) (hD : ∀ k, 0 ≤ D k)
    (hcB : ∀ j, A j ≤ cB j) (hcBnn : ∀ j, 0 ≤ cB j) :
    (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) ^ 2 * (A j * D (m - j)))
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1), D k) := by
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ m := pow_nonneg (by norm_num) m
  have hchoose : ∀ j, (m.choose j : ℝ) ^ 2 ≤ (4 : ℝ) ^ m := by
    intro j
    have h1 : (m.choose j : ℝ) ≤ (2 : ℝ) ^ m := by
      exact_mod_cast Nat.choose_le_two_pow m j
    have h0 : (0 : ℝ) ≤ (m.choose j : ℝ) := Nat.cast_nonneg _
    calc (m.choose j : ℝ) ^ 2 ≤ ((2 : ℝ) ^ m) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (4 : ℝ) ^ m := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have hjmem : ∀ j ∈ Finset.range (m + 1), m - j ∈ Finset.range (m + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  calc (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) ^ 2 * (A j * D (m - j)))
      ≤ ∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j * D (m - j) := by
        apply Finset.sum_le_sum
        intro j _
        have hA' : 0 ≤ A j := hA j
        have hD' : 0 ≤ D (m - j) := hD _
        calc (m.choose j : ℝ) ^ 2 * (A j * D (m - j))
            ≤ (4 : ℝ) ^ m * (cB j * D (m - j)) :=
              mul_le_mul (hchoose j) (mul_le_mul_of_nonneg_right (hcB j) hD')
                (mul_nonneg hA' hD') h4
          _ = (4 : ℝ) ^ m * cB j * D (m - j) := by ring
    _ ≤ ∑ j ∈ Finset.range (m + 1),
          (4 : ℝ) ^ m * cB j * (∑ k ∈ Finset.range (m + 1), D k) := by
        apply Finset.sum_le_sum
        intro j hj
        have hs := Finset.single_le_sum (f := D) (fun i _ => hD i) (hjmem j hj)
        exact mul_le_mul_of_nonneg_left hs (mul_nonneg h4 (hcBnn j))
    _ = (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
          (∑ k ∈ Finset.range (m + 1), D k) := by
        rw [Finset.sum_mul]

theorem iterFamilyB_le {cB : ℕ → ℝ}
    (hcB : ∀ j θ, (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 ≤ cB j)
    (hcBnn : ∀ j, 0 ≤ cB j) (m : ℕ) (α : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (g : ℝ → ℝ) :
    (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2))
      * Work.FTS.EllipticEst.sGam α θ
      ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1),
            (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
  have hsGam : 0 ≤ Work.FTS.EllipticEst.sGam α θ := by
    rw [Work.FTS.EllipticEst.sGam]
    apply Real.rpow_nonneg
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hA : ∀ j, 0 ≤ (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2 :=
    fun j => sq_nonneg _
  have hD : ∀ k, 0 ≤ (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ :=
    fun k => mul_nonneg (sq_nonneg _) hsGam
  have hkey := sum_choose_sq_mul_le (m := m)
    (A := fun j => (Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2)
    (D := fun k => (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
    (cB := cB) hA hD (fun j => hcB j θ) hcBnn
  calc (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
        ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
          * (Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2)) * Work.FTS.EllipticEst.sGam α θ
      = (∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ)) ^ 2 *
          ((Work.Elliptic.Dth1Iter j (fun τ : ℝ => 2 * Real.cos (2 * τ)) θ) ^ 2
            * ((Work.Elliptic.Dth1Iter (m - j) g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ (∑ j ∈ Finset.range (m + 1), (4 : ℝ) ^ m * cB j) *
        (∑ k ∈ Finset.range (m + 1),
            (Work.Elliptic.Dth1Iter k g θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := hkey

end Work.FTS.EllipticEst.TT
