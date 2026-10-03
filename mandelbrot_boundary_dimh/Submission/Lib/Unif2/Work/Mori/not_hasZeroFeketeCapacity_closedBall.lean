import Mathlib
import Submission.Lib.Unif2.Work.Mori.Defs
import Submission.Lib.Unif2.Work.Mori.vandermonde_lower_bound

/-!
# A closed disc has positive logarithmic capacity

`Work.Mori.not_hasZeroFeketeCapacity_closedBall`: for `ε > 0` the closed ball
`Metric.closedBall x ε ⊆ ℂ` does *not* have vanishing Fekete capacity.

The proof is the configuration used in `Work.Mori.exists_sphere_eq_empty`, run "forwards": for each
`n ≥ 2` the `n` points `z k = x + ε (k+1)/n`, `k = 0, …, n-1`, lie on the real diameter of the ball
(since `k + 1 ≤ n`) and their pairwise distances are exactly `‖z i - z j‖ = ε |i-j| / n`.  Hence the
Fekete mean `(∏_{i<j} ‖z i - z j‖)^{1/N}`, `N = n(n-1)/2`, equals

`(ε/n) * (∏_{i<j} (j - i))^{1/N} ≥ (ε/n) * n exp (-3) = ε exp (-3)`,

uniformly in `n`, by `Work.Mori.vandermonde_lower_bound`.  So vanishing Fekete capacity fails
already at `ε₀ = ε exp (-3) / 2`.

The general mechanism is isolated in `feketeMean_lower_of_pairwise`: an `n`-tuple whose `(i,j)`
distance dominates a fixed multiple `D (j - i)` of the pair separation has Fekete mean at least
`D · n e^{-3}`.
-/

namespace Work.Mori

noncomputable section

open Finset

/-- `Fin n` has `n (n-1)/2` pairs `i < j`: the number of factors of a nested product over
`Finset.Ioi`. -/
private lemma sum_card_Ioi_fin (n : ℕ) : ∑ i : Fin n, (Finset.Ioi i).card = n * (n - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => n - 1 - k)]
  rw [Finset.sum_range_reflect (fun k : ℕ => k) n]
  exact Finset.sum_range_id n

/-- Factoring a constant `D` out of a nested product over `Finset.Ioi`: the number of factors is the
number of pairs `i < j`, i.e. `n (n-1)/2`. -/
private lemma prod_Ioi_const_mul (n : ℕ) (a : Fin n → Fin n → ℝ) (D : ℝ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, D * a i j)
      = D ^ (n * (n - 1) / 2) * ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, a i j := by
  have h1 : ∀ i : Fin n, (∏ j ∈ Finset.Ioi i, D * a i j)
      = D ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, a i j := by
    intro i
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum Finset.univ (fun x : Fin n => (Finset.Ioi x).card) D,
    sum_card_Ioi_fin n]

/-- The `N`-th root of `D ^ N` is `D`, for `D ≥ 0` and `N ≠ 0`. -/
private lemma rpow_natCast_inv (D : ℝ) (hD : 0 ≤ D) {N : ℕ} (hN : N ≠ 0) :
    (D ^ N) ^ (1 / (N : ℝ)) = D := by
  rw [← Real.rpow_natCast D N, ← Real.rpow_mul hD (N : ℝ) (1 / (N : ℝ))]
  have h : (N : ℝ) * (1 / (N : ℝ)) = 1 := by
    rw [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN)]
  rw [h, Real.rpow_one]

/-- **The Fekete mean of a separated `n`-tuple is bounded below, uniformly in `n`.**

If the `(i,j)` distance of an `n`-tuple `z` of points of `K` dominates `D (j - i)` for every
`i < j` (with `D ≥ 0`), then `D · n e^{-3} ≤ feketeMean z`. -/
private lemma feketeMean_lower_of_pairwise {n : ℕ} (hn : 2 ≤ n) {K : Set ℂ}
    (z : Fin n → ↥K) {D : ℝ} (hD : 0 ≤ D)
    (hpair : ∀ i j : Fin n, i < j →
      D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ≤ ‖(z i : ℂ) - (z j : ℂ)‖) :
    D * ((n : ℝ) * Real.exp (-3)) ≤ feketeMean z := by
  have hNne : n * (n - 1) / 2 ≠ 0 := by
    have h1 : 2 ≤ n * (n - 1) := by
      calc 2 = 2 * 1 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hNpos : (0 : ℝ) < ((n * (n - 1) / 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hNne
  set V : ℝ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
    (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) with hVdef
  have hVnonneg : 0 ≤ V := by
    rw [hVdef]
    apply Finset.prod_nonneg
    intro i _
    apply Finset.prod_nonneg
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
    linarith
  -- the product of the `D (j - i)` bounds the product of the actual distances
  have hprod_le :
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ≤ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖ := by
    apply Finset.prod_le_prod₀
    · intro i _
      apply Finset.prod_nonneg
      intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
      exact mul_nonneg hD (by linarith)
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j hj
        have hij : i < j := Finset.mem_Ioi.mp hj
        have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
        exact mul_nonneg hD (by linarith)
      · intro j hj
        exact hpair i j (Finset.mem_Ioi.mp hj)
  have hleft_nonneg : 0 ≤ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
    apply Finset.prod_nonneg
    intro i _
    apply Finset.prod_nonneg
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
    exact mul_nonneg hD (by linarith)
  have hstep : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
      ≤ feketeMean z := by
    have h := Real.rpow_le_rpow hleft_nonneg hprod_le (by positivity :
      (0 : ℝ) ≤ 1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
    simpa [feketeMean] using h
  have hsplit : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      = D ^ (n * (n - 1) / 2) * V := by
    rw [hVdef, prod_Ioi_const_mul]
  have hrpow : (D ^ (n * (n - 1) / 2) * V) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
      = D * V ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
    rw [Real.mul_rpow (by positivity) hVnonneg, rpow_natCast_inv D hD hNne]
  have hVroot : (n : ℝ) * Real.exp (-3) ≤ V ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
    rw [hVdef]
    exact vandermonde_lower_bound hn
  calc D * ((n : ℝ) * Real.exp (-3))
      ≤ D * V ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hVroot hD
    _ = (D ^ (n * (n - 1) / 2) * V) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := hrpow.symm
    _ = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          D * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
        rw [hsplit]
    _ ≤ feketeMean z := hstep

/-- **A closed disc has positive logarithmic capacity.**  For `ε > 0` the closed ball
`Metric.closedBall x ε ⊆ ℂ` does *not* have vanishing Fekete capacity.

Route (the same configuration as in `Work.Mori.exists_sphere_eq_empty`): for every `n ≥ 2`, the `n`
points `z k = x + ε (k+1)/n` (on the real diameter of the ball; they lie in the ball since
`k + 1 ≤ n`) have pairwise distances `‖z i - z j‖ = ε |i - j| / n`, so their Fekete mean is at least
`(ε/n) · (∏_{i<j} |i-j|)^{2/(n(n-1))} ≥ ε · exp (-3)` (`Work.Mori.vandermonde_lower_bound`),
uniformly in `n`.  Hence vanishing Fekete capacity fails, with `ε₀ = ε * exp (-3) / 2`. -/
theorem not_hasZeroFeketeCapacity_closedBall (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ¬ HasZeroFeketeCapacity (Metric.closedBall x ε) := by
  intro h
  have hε0 : (0 : ℝ) < ε * Real.exp (-3) / 2 := by positivity
  obtain ⟨n, hn, hbound⟩ := h (ε * Real.exp (-3) / 2) hε0
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set c : Fin n → ℝ := fun k => ε * (((k : ℕ) : ℝ) + 1) / (n : ℝ) with hcdef
  have hc_nonneg : ∀ k : Fin n, 0 ≤ c k := by
    intro k
    rw [hcdef]
    simp only
    positivity
  have hc_le : ∀ k : Fin n, c k ≤ ε := by
    intro k
    have hkn : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have : (k : ℕ) + 1 ≤ n := by have := k.isLt; omega
      exact_mod_cast this
    rw [hcdef]
    simp only
    rw [div_le_iff₀ hnpos]
    nlinarith [hkn, hε]
  let z : Fin n → ↥(Metric.closedBall x ε) := fun k => ⟨x + (c k : ℂ), by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hc_nonneg k)]
    exact hc_le k⟩
  have hzval : ∀ k : Fin n, (z k : ℂ) = x + (c k : ℂ) := fun k => rfl
  have hpair : ∀ i j : Fin n, i < j →
      (ε / (n : ℝ)) * (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) = ‖(z i : ℂ) - (z j : ℂ)‖ := by
    intro i j hij
    have hij' : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
    have hcij : c i - c j = (ε / (n : ℝ)) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) := by
      rw [hcdef]
      simp only
      field_simp
      ring
    have hz : (z i : ℂ) - (z j : ℂ) = ((c i - c j : ℝ) : ℂ) := by
      rw [hzval i, hzval j]
      push_cast
      ring
    rw [hz, Complex.norm_real, Real.norm_eq_abs, hcij, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / (n : ℝ)),
      abs_of_nonpos (by linarith : ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≤ 0)]
    ring
  have hlow := feketeMean_lower_of_pairwise hn z (by positivity : (0 : ℝ) ≤ ε / (n : ℝ))
    (fun i j hij => le_of_eq (hpair i j hij))
  have hprod : (ε / (n : ℝ)) * ((n : ℝ) * Real.exp (-3)) = ε * Real.exp (-3) := by
    field_simp
  have hbig : ε * Real.exp (-3) ≤ feketeMean z := by
    rw [← hprod]
    exact hlow
  have hsmall := hbound z
  linarith

end

end Work.Mori
