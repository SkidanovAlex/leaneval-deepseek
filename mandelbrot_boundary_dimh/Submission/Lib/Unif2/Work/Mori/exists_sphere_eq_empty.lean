import Mathlib
import Submission.Lib.Unif2.Work.Mori.Defs

/-!
# Thinness of a polar set

`Work.Mori.exists_sphere_eq_empty`: a closed polar set `K ⊆ ℂ` is thin at each of its points — for
every `p ∈ K` there is a circle centred at `p` that misses `K`.

The proof is Fekete's capacity argument in the following form.  Suppose `K` met the circle of every
radius `r ∈ (0,1)` around `p`.  Then for every `n ≥ 2` the `n` points of `K` at the radii
`(k+1)/(n+1)`, `k = 0, …, n-1`, lie in the compact set `K ∩ closedBall p 1`; their pairwise distances
are at least `|i-j|/(n+1)`, so their Fekete mean (the geometric mean of the `n(n-1)/2` pairwise
distances) is at least

`(∏_{i<j} (j-i))^{2/(n(n-1))} / (n+1) ≥ (n exp (-4)) / (n+1) ≥ exp (-4)/2 > 0`,

contradicting vanishing Fekete capacity.  The Vandermonde estimate `∏_{i<j}(j-i) = ∏_{d<n} d!`
together with Stirling's bound `log d! ≥ d log d - d` and `log (n/m) ≤ n/m - 1` gives the required
uniform lower bound `≥ n exp (-4)`; everything is proved here, with no classical input.
-/

namespace Work.Mori

open scoped Topology
open Finset

/-- `Fin n` has `n (n-1)/2` pairs `i < j`: the number of factors of a nested product over
`Finset.Ioi`. -/
private lemma sum_card_Ioi_fin (n : ℕ) : ∑ i : Fin n, (Finset.Ioi i).card = n * (n - 1) / 2 := by
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => n - 1 - k)]
  rw [Finset.sum_range_reflect (fun k : ℕ => k) n]
  exact Finset.sum_range_id n

/-- Dividing every factor of a nested product over `Finset.Ioi` by the same constant divides the
whole product by `D ^ (n (n-1)/2)`. -/
private lemma prod_Ioi_div_eq (n : ℕ) (a : Fin n → Fin n → ℝ) (D : ℝ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, a i j / D)
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, a i j) / D ^ (n * (n - 1) / 2) := by
  have h1 : ∀ i : Fin n, (∏ j ∈ Finset.Ioi i, a i j / D)
      = (∏ j ∈ Finset.Ioi i, a i j) / D ^ (Finset.Ioi i).card := by
    intro i
    rw [Finset.prod_div_distrib]
    congr 1
    exact Finset.prod_const D
  rw [Finset.prod_congr rfl (fun i _ => h1 i)]
  rw [Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum Finset.univ (fun x : Fin n => (Finset.Ioi x).card) D]
  rw [sum_card_Ioi_fin n]

/-- The `N`-th root of `D ^ N` is `D` for `D ≥ 0` and `N ≠ 0`. -/
private lemma rpow_natCast_inv (D : ℝ) (hD : 0 ≤ D) {N : ℕ} (hN : N ≠ 0) :
    (D ^ N) ^ (1 / (N : ℝ)) = D := by
  rw [← Real.rpow_natCast D N, ← Real.rpow_mul hD (N : ℝ) (1 / (N : ℝ))]
  have h : (N : ℝ) * (1 / (N : ℝ)) = 1 := by
    rw [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN)]
  rw [h, Real.rpow_one]

/-- `∏_{k < m} (k + 1) = m!`, over the reals. -/
private lemma prod_range_add_one_cast (m : ℕ) :
    (∏ k ∈ Finset.range m, (((k : ℕ) : ℝ) + 1)) = (((m.factorial : ℕ) : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

/-- For a fixed `i : Fin n`, the product of the differences `j - i` over `j > i` is `(n - 1 - i)!`:
these differences run over `1, …, n-1-i`. -/
private lemma prod_Ioi_sub_factorial (n : ℕ) (i : Fin n) :
    (∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      = (((n - 1 - (i : ℕ)).factorial : ℕ) : ℝ) := by
  rw [← show (∏ k : Fin (n - 1 - (i : ℕ)), ((k : ℝ) + 1))
      = ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) from by
    refine Finset.prod_bij
      (fun (k : Fin (n - 1 - (i : ℕ))) (_ : k ∈ Finset.univ) =>
        (⟨(i : ℕ) + (k : ℕ) + 1, by have hk := k.isLt; omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Ioi]; exact Fin.lt_def.mpr (by simp)
    · intro k₁ hk₁ k₂ hk₂ heq
      have : (k₁ : ℕ) = (k₂ : ℕ) := by
        have h := congrArg Fin.val heq; simp at h; omega
      exact Fin.ext this
    · intro j hj
      simp only [Finset.mem_Ioi] at hj
      refine ⟨⟨(j : ℕ) - (i : ℕ) - 1, by have h := j.isLt; have hi := i.isLt; omega⟩,
        Finset.mem_univ _, ?_⟩
      ext; simp; omega
    · intro k hk; push_cast; ring]
  exact (Fin.prod_univ_eq_prod_range (fun j : ℕ => ((j : ℝ) + 1)) (n - 1 - (i:ℕ))).trans
    (prod_range_add_one_cast _)

/-- **The Vandermonde product**: `∏_{i<j<n} (j - i) = ∏_{d<n} d!`. -/
private lemma vandermonde_eq_factorials (n : ℕ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
      = ∏ d ∈ Finset.range n, (((d.factorial : ℕ) : ℝ)) := by
  have h2 : (∏ i : Fin n, (((n - 1 - (i:ℕ)).factorial : ℕ) : ℝ))
        = ∏ d ∈ Finset.range n, (((d.factorial : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (((n - 1 - k).factorial : ℕ) : ℝ)) n]
    exact Finset.prod_range_reflect (fun k : ℕ => (((k.factorial : ℕ) : ℝ))) n
  calc ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))
      = ∏ i : Fin n, (((n - 1 - (i:ℕ)).factorial : ℕ) : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact prod_Ioi_sub_factorial n i
    _ = _ := h2

/-- Stirling's bound in logarithmic form, valid for every `k : ℕ`. -/
private lemma log_factorial_ge (k : ℕ) :
    (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) ≤ Real.log (((k.factorial : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · have h := Stirling.le_log_factorial_stirling (n := k) (by omega)
    have h1 : 0 ≤ Real.log (k : ℝ) / 2 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hk)) (by norm_num)
    have h2 : 0 ≤ Real.log (2 * Real.pi) / 2 :=
      div_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three])) (by norm_num)
    linarith

/-- `log (n/m) ≤ n/m - 1` rearranged: `m log m ≥ m log n + m - n` for `m < n`. -/
private lemma mul_log_ge (n m : ℕ) (hm : m < n) :
    (m : ℝ) * Real.log (n : ℝ) + (m : ℝ) - (n : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0; simp
  · have hn : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le m) hm)
    have hmp : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hlog : Real.log ((n : ℝ) / (m : ℝ)) ≤ (n : ℝ) / (m : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (ne_of_gt hn) (ne_of_gt hmp)] at hlog
    have h1 : Real.log (n : ℝ) - (n : ℝ) / (m : ℝ) + 1 ≤ Real.log (m : ℝ) := by linarith
    have h2 : (m : ℝ) * (Real.log (n : ℝ) - (n : ℝ) / (m : ℝ) + 1)
        ≤ (m : ℝ) * Real.log (m : ℝ) := mul_le_mul_of_nonneg_left h1 hmp.le
    have h3 : (m : ℝ) * (Real.log (n : ℝ) - (n : ℝ) / (m : ℝ) + 1)
        = (m : ℝ) * Real.log (n : ℝ) + (m : ℝ) - (n : ℝ) := by
      field_simp
      ring
    rwa [h3] at h2

/-- `Σ_{m<n} (m log m - m) ≥ (Σ_{m<n} m) log n - n²`. -/
private lemma sum_mul_log_lower (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.range n, (m : ℝ)) * Real.log (n : ℝ) - (n : ℝ) ^ 2
      ≤ ∑ m ∈ Finset.range n, ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ)) := by
  have hterm : ∀ m ∈ Finset.range n,
      (m : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) := by
    intro m hm
    have hm' : m < n := Finset.mem_range.mp hm
    have h := mul_log_ge n m hm'
    linarith
  calc (∑ m ∈ Finset.range n, (m : ℝ)) * Real.log (n : ℝ) - (n : ℝ) ^ 2
      = ∑ m ∈ Finset.range n, ((m : ℝ) * Real.log (n : ℝ) - (n : ℝ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, sq]
    _ ≤ ∑ m ∈ Finset.range n, ((m : ℝ) * Real.log (m : ℝ) - (m : ℝ)) :=
        Finset.sum_le_sum hterm

/-- `(n (n-1)/2 : ℕ)`, cast to `ℝ`, is the sum `Σ_{m<n} m`. -/
private lemma natcast_div_two (n : ℕ) :
    (((n * (n - 1) / 2 : ℕ)) : ℝ) = ∑ m ∈ Finset.range n, (m : ℝ) := by
  rw [← Nat.cast_sum, Finset.sum_range_id]

/-- The elementary real sum `Σ_{m<n} m = n (n-1)/2`. -/
private lemma sum_range_cast_id (n : ℕ) :
    (∑ m ∈ Finset.range n, (m : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **The Vandermonde estimate.**  `∏_{i<j} (j - i) ≥ (n exp (-4))^{n(n-1)/2}` for `n ≥ 2`. -/
private lemma vandermonde_growth (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) * Real.exp (-4)) ^ (n * (n - 1) / 2)
      ≤ ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  set V := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) with hV
  have hVpos : 0 < V := by
    rw [hV]
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  have hsum := sum_range_cast_id n
  have hNsum := natcast_div_two n
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnin : (n : ℝ) ^ 2 ≤ 4 * (∑ m ∈ Finset.range n, (m : ℝ)) := by
    rw [hsum]
    nlinarith
  have hlog : ((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log (n : ℝ) - 4) ≤ Real.log V := by
    have h1 : Real.log V = ∑ m ∈ Finset.range n, Real.log (((m.factorial : ℕ) : ℝ)) := by
      rw [hV, vandermonde_eq_factorials n, Real.log_prod]
      intro d _
      exact ne_of_gt (by exact_mod_cast d.factorial_pos)
    have h2 : (∑ m ∈ Finset.range n, (m : ℝ)) * Real.log (n : ℝ) - (n : ℝ) ^ 2
        ≤ ∑ m ∈ Finset.range n, Real.log (((m.factorial : ℕ) : ℝ)) := by
      refine le_trans (sum_mul_log_lower n hn) ?_
      apply Finset.sum_le_sum
      intro m _
      exact log_factorial_ge m
    have h3 : ((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log (n : ℝ) - 4)
        = (∑ m ∈ Finset.range n, (m : ℝ)) * Real.log (n : ℝ) - 4 * (∑ m ∈ Finset.range n, (m : ℝ)) := by
      rw [hNsum]; ring
    rw [h1, h3]
    linarith
  have hexp : Real.exp (((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log (n : ℝ) - 4))
      = ((n : ℝ) * Real.exp (-4)) ^ (n * (n - 1) / 2) := by
    rw [Real.exp_nat_mul]
    congr 1
    rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, div_eq_mul_inv]
  calc ((n : ℝ) * Real.exp (-4)) ^ (n * (n - 1) / 2)
      = Real.exp (((n * (n - 1) / 2 : ℕ) : ℝ) * (Real.log (n : ℝ) - 4)) := hexp.symm
    _ ≤ Real.exp (Real.log V) := Real.exp_le_exp.mpr hlog
    _ = V := Real.exp_log hVpos

/-- **The pairwise distances of points at the radii `(k+1)/(n+1)` are at least `|i-j|/(n+1)`** by
the triangle inequality. -/
private lemma radii_pair_bound {n : ℕ} {K : Set ℂ} {p : ℂ} (z : Fin n → ↥K)
    (hz : ∀ k : Fin n, ‖(z k : ℂ) - p‖ = (((k : ℕ) + 1 : ℝ)) / ((n : ℝ) + 1))
    {i j : Fin n} (hij : i < j) :
    (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / ((n : ℝ) + 1) ≤ ‖(z i : ℂ) - (z j : ℂ)‖ := by
  have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (le_of_lt hij)
  have h1 : |‖(z i : ℂ) - p‖ - ‖(z j : ℂ) - p‖| ≤ ‖(z i : ℂ) - (z j : ℂ)‖ := by
    have := abs_norm_sub_norm_le ((z i : ℂ) - p) ((z j : ℂ) - p)
    simpa using this
  rw [hz i, hz j] at h1
  have h2 : |(((i : ℕ) : ℝ) + 1) / ((n : ℝ) + 1) - (((j : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)|
      = (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / ((n : ℝ) + 1) := by
    rw [← sub_div]
    have hnum : (((i : ℕ) : ℝ) + 1) - (((j : ℕ) : ℝ) + 1)
        = -(((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by ring
    have hnn : 0 ≤ (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / ((n : ℝ) + 1) :=
      div_nonneg (by linarith) (by positivity)
    rw [hnum, neg_div, abs_neg, abs_of_nonneg hnn]
  linarith [h2 ▸ h1]

/-- **The Fekete mean of `n` points at the radii `(k+1)/(n+1)` is bounded below, uniformly in `n`**,
by `exp (-4)/2 > 0`. -/
private lemma feketeMean_radii_lower_bound {n : ℕ} (hn : 2 ≤ n) {K : Set ℂ} {p : ℂ}
    (z : Fin n → ↥K)
    (hz : ∀ k : Fin n, ‖(z k : ℂ) - p‖ = (((k : ℕ) + 1 : ℝ)) / ((n : ℝ) + 1)) :
    Real.exp (-4) / 2 ≤ feketeMean z := by
  set D : ℝ := (n : ℝ) + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hNne : n * (n - 1) / 2 ≠ 0 := by
    have h1 : 2 ≤ n * (n - 1) := by
      calc 2 = 2 * 1 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  have hVnonneg : 0 ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) := by
    apply Finset.prod_nonneg
    intro i _
    apply Finset.prod_nonneg
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
    linarith
  have hQnonneg : 0 ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / D)) := by
    apply Finset.prod_nonneg
    intro i _
    apply Finset.prod_nonneg
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
    exact div_nonneg (by linarith) hDpos.le
  have hprod : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / D))
      ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖) := by
    apply Finset.prod_le_prod₀
    · intro i _
      apply Finset.prod_nonneg
      intro j hj
      have hij : i < j := Finset.mem_Ioi.mp hj
      have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
      exact div_nonneg (by linarith) hDpos.le
    · intro i _
      apply Finset.prod_le_prod₀
      · intro j hj
        have hij : i < j := Finset.mem_Ioi.mp hj
        have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast le_of_lt hij
        exact div_nonneg (by linarith) hDpos.le
      · intro j hj
        exact radii_pair_bound z hz (Finset.mem_Ioi.mp hj)
  have hsplit : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        ((((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / D))
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
          / D ^ (n * (n - 1) / 2) :=
    prod_Ioi_div_eq n (fun i j => (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ))) D
  have hstep : ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        / D ^ (n * (n - 1) / 2)) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
      ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖)
        ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) :=
    Real.rpow_le_rpow (div_nonneg hVnonneg (by positivity)) (hsplit ▸ hprod) (by positivity)
  have hroot : ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        / D ^ (n * (n - 1) / 2)) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
      = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) / D := by
    rw [Real.div_rpow hVnonneg (by positivity), rpow_natCast_inv D hDpos.le hNne]
  have hVroot : (n : ℝ) * Real.exp (-4)
      ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
    have h : (((n : ℝ) * Real.exp (-4)) ^ (n * (n - 1) / 2)) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ))
        ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
          ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow (by positivity) (vandermonde_growth n hn) (by positivity)
    rwa [rpow_natCast_inv ((n : ℝ) * Real.exp (-4)) (by positivity) hNne] at h
  have hDineq : Real.exp (-4) / 2 ≤ (n : ℝ) * Real.exp (-4) / D := by
    rw [hDdef, div_le_div_iff₀ (by norm_num) (by positivity)]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith [Real.exp_pos (-4)]
  calc Real.exp (-4) / 2
      ≤ (n : ℝ) * Real.exp (-4) / D := hDineq
    _ ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) / D := div_le_div_of_nonneg_right hVroot hDpos.le
    _ = ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))
        / D ^ (n * (n - 1) / 2)) ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := hroot.symm
    _ ≤ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖(z i : ℂ) - (z j : ℂ)‖)
        ^ (1 / ((n * (n - 1) / 2 : ℕ) : ℝ)) := hstep
    _ = feketeMean z := rfl

/-- **A polar closed set is thin at each of its points**: around every `p ∈ K` there is a circle
centred at `p` that misses `K` entirely.

`IsPolar K` says every compact subset of `K` has vanishing Fekete capacity; apply it to the compact
set `K ∩ closedBall p 1` and argue by contradiction: if `K` met the circle of every radius `r ∈ (0,1)`
around `p`, then for each `n ≥ 2` the `n` points at radii `(k+1)/(n+1)` would give an `n`-tuple of
`K ∩ closedBall p 1` whose Fekete mean is bounded below by `exp (-4)/2 > 0`, contradicting
vanishing Fekete capacity for `ε = exp (-4)/2`. -/
theorem exists_sphere_eq_empty {K : Set ℂ} (hK : IsPolar K) (hKc : IsClosed K) {p : ℂ}
    (hp : p ∈ K) : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ K, ‖z - p‖ ≠ r := by
  by_contra hcon
  push_neg at hcon
  have hLc : IsCompact (K ∩ Metric.closedBall p 1) :=
    (isCompact_closedBall p 1).inter_left hKc
  have hzero : HasZeroFeketeCapacity (K ∩ Metric.closedBall p 1) :=
    hK _ Set.inter_subset_left hLc
  have heps : (0 : ℝ) < Real.exp (-4) / 2 := by positivity
  obtain ⟨n, hn, hbound⟩ := hzero (Real.exp (-4) / 2) heps
  choose z hzmem using fun k : Fin n =>
    hcon ((((k : ℕ) + 1 : ℝ)) / ((n : ℝ) + 1)) (by positivity)
  have hzr : ∀ k : Fin n, ‖z k - p‖ = (((k : ℕ) + 1 : ℝ)) / ((n : ℝ) + 1) :=
    fun k => (hzmem k).2
  have hzball : ∀ k : Fin n, z k ∈ Metric.closedBall p 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_eq_norm, hzr k, div_le_one (by positivity)]
    have hk : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have : (k : ℕ) + 1 ≤ n := by have := k.isLt; omega
      exact_mod_cast this
    linarith [hk, Nat.cast_nonneg (α := ℝ) n]
  let w : Fin n → ↥(K ∩ Metric.closedBall p 1) := fun k => ⟨z k, (hzmem k).1, hzball k⟩
  have hw : Real.exp (-4) / 2 ≤ feketeMean w := feketeMean_radii_lower_bound hn w (fun k => hzr k)
  have hlt := hbound w
  linarith

end Work.Mori
