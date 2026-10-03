import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Variation

open Filter

theorem cauchySeq_of_forall_monotone_variation_le {E : Type*} [NormedAddCommGroup E]
    {a : ℕ → E} {r : ℝ} (hr : 1 ≤ r) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (J : ℕ) (N : ℕ → ℕ), Monotone N →
      (∑ i : Fin J, ‖a (N ((i : ℕ) + 1)) - a (N (i : ℕ))‖ ^ r) ≤ C) :
    CauchySeq a := by
  have _hC : 0 ≤ C := hC
  by_contra hnc
  rw [Metric.cauchySeq_iff] at hnc
  push Not at hnc
  obtain ⟨ε, hεpos, hε⟩ := hnc
  -- Step 1: for every k there is l ≥ k with dist (a l) (a k) ≥ ε/2.
  have hfar : ∀ k, ∃ l, k ≤ l ∧ ε / 2 ≤ dist (a l) (a k) := by
    intro k
    obtain ⟨m, hm, n, hn, hmn⟩ := hε k
    have htri : dist (a m) (a n) ≤ dist (a m) (a k) + dist (a n) (a k) := by
      rw [dist_comm (a n) (a k)]
      exact dist_triangle _ _ _
    rcases le_total (dist (a m) (a k)) (dist (a n) (a k)) with hle | hle
    · exact ⟨n, hn, by linarith⟩
    · exact ⟨m, hm, by linarith⟩
  -- Step 2: define the "far" map and the increasing enumeration.
  let far : ℕ → ℕ := fun k => Classical.choose (hfar k)
  have hfar_spec : ∀ k, k ≤ far k ∧ ε / 2 ≤ dist (a (far k)) (a k) :=
    fun k => Classical.choose_spec (hfar k)
  have hfar_gt : ∀ k, k < far k := by
    intro k
    have hpos : 0 < ε / 2 := by linarith
    have hd : 0 < dist (a (far k)) (a k) := lt_of_lt_of_le hpos (hfar_spec k).2
    have hne : far k ≠ k := by
      intro heq
      rw [heq, dist_self] at hd
      exact lt_irrefl _ hd
    exact lt_of_le_of_ne (hfar_spec k).1 (Ne.symm hne)
  let t : ℕ → ℕ := fun j => far^[j] 0
  have ht_succ : ∀ j, t (j + 1) = far (t j) := by
    intro j
    simp only [t]
    rw [Function.iterate_succ_apply']
  have ht_gt : ∀ j, t j < t (j + 1) := by
    intro j
    rw [ht_succ j]
    exact hfar_gt (t j)
  have htmono : Monotone t := (strictMono_nat_of_lt_succ ht_gt).monotone
  -- Step 3: the r-th power step size is positive.
  have hδpos : 0 < (ε / 2) ^ r := Real.rpow_pos_of_pos (by linarith) r
  -- Choose J with (J : ℝ) * (ε/2)^r > C.
  obtain ⟨J, hJ⟩ := exists_nat_gt (C / (ε / 2) ^ r)
  have hJ' : C < (J : ℝ) * (ε / 2) ^ r := by
    rw [div_lt_iff₀ hδpos] at hJ
    linarith
  -- Step 4: lower bound the variation along t.
  have hsum_const : (∑ _i : Fin J, (ε / 2) ^ r) = (J : ℝ) * (ε / 2) ^ r := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hsum_ge : (J : ℝ) * (ε / 2) ^ r
      ≤ ∑ i : Fin J, ‖a (t ((i : ℕ) + 1)) - a (t (i : ℕ))‖ ^ r := by
    rw [← hsum_const]
    apply Finset.sum_le_sum
    intro i _
    have hstep : ε / 2 ≤ dist (a (t ((i : ℕ) + 1))) (a (t (i : ℕ))) := by
      rw [ht_succ (i : ℕ)]
      exact (hfar_spec (t (i : ℕ))).2
    rw [← dist_eq_norm (a (t ((i : ℕ) + 1))) (a (t (i : ℕ)))]
    exact Real.rpow_le_rpow (by linarith) hstep (by linarith)
  -- Step 5: contradiction.
  have hbound := h J t htmono
  linarith

end Commons.Analysis.Variation