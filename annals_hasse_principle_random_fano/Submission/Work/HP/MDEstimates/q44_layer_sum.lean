import Mathlib
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.PairsAux
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.Sig2.ellXY_pair_le
import Submission.Work.HP.MDEstimates.q44_arith_sum
import Submission.Work.HP.MDEstimates.q44_log_bound
import Submission.Work.HP.MDEstimates.q44_window_fiber_le
import Submission.Work.HP.MDEstimates.q44_window_bounds

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

/-- Dyadic layer sum for the `ℓ^{(56)}` bound: over any finite set of primitive rank-`3`
sublattices of `ℤ^5` of covolume at most `Δ+1`, the sum of `λ₁¹⁸λ₂¹⁸λ₃²⁰` is
`O(Δ²⁴)`.

Route: group the lattices by the dyadic window `k = kwin 3 L` (`kwin_spec`); the windows
are monotone `k₁ ≤ k₂ ≤ k₃` and satisfy `∏_j 2^{k_j} ≤ 8 λ₁λ₂λ₃ ≤ 8 K detL L ≤ 16 K Δ`
(Minkowski).  In each window the number of lattices is `≤ Knum ∏ (2^{k_j})^{7-2j}`
(`num_lattices_of`), while `λ₁¹⁸λ₂¹⁸λ₃²⁰ ≤ ∏_j (2^{k_j})^{18,18,20}`, so a window
contributes `≤ Knum 2^{25k₁+23k₂+23k₃}`.  Summing over monotone `k` with `Σ k ≤ N`,
`2^N ≍ Δ`, gives `(N+1)³ 2^{71N/3} = O(Δ^{71/3+1/3}) = O(Δ²⁴)` since
`(log Δ)³ ≪ Δ^{1/3}`. -/
theorem q44_layer_sum :
    ∃ K : ℝ, 0 < K ∧ ∀ (T : Finset (Submodule ℤ (Fin 5 → ℤ))) (Δ : ℝ), 1 ≤ Δ →
      (∀ L ∈ T, Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧ Work.HP.detL L ≤ Δ + 1) →
      (∑ L ∈ T, Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20)
        ≤ K * Δ ^ 24 := by
  classical
  obtain ⟨Kmink0, hKmink0, hmink0⟩ := Work.HP.Sig2.minkowski_prod (ι := Fin 5)
  set Kmink : ℝ := max Kmink0 1 with hKminkdef
  have hKmink : 1 ≤ Kmink := le_max_right _ _
  have hKminkpos : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  have hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (Work.HP.rk L), Work.HP.lam L (j + 1)) ≤ Kmink * Work.HP.detL L := by
    intro L
    exact le_trans (hmink0 L)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.HP.detL_nonneg L))
  obtain ⟨Knum, hKnumpos, hfiber⟩ := q44_window_fiber_le Kmink hKmink hmink
  have hbnds := q44_window_bounds Kmink hKmink hmink
  obtain ⟨Karith, hKarithpos, harith⟩ := q44_arith_sum Kmink hKmink
  obtain ⟨Klog, hKlogpos, hlog⟩ := q44_log_bound Kmink hKmink
  refine ⟨Knum * Karith * Klog, by positivity, ?_⟩
  intro T Δ hΔ hT
  set N : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hNdef
  set box : Finset (Fin 3 → ℕ) :=
    Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)) with hboxdef
  set w : Submodule ℤ (Fin 5 → ℤ) → ℝ :=
    fun L => Work.HP.lam L 1 ^ 18 * Work.HP.lam L 2 ^ 18 * Work.HP.lam L 3 ^ 20 with hwdef
  set win : (Fin 3 → ℕ) → ℝ := fun k => (2 : ℝ) ^ (25 * k 0 + 23 * k 1 + 23 * k 2) with hwindef
  set cond : (Fin 3 → ℕ) → Prop := fun k => Monotone k ∧ (∑ j : Fin 3, k j) ≤ N with hconddef
  have hfib : (∑ k ∈ box, ∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k), w L)
      = ∑ L ∈ T, w L := by
    refine Finset.sum_fiberwise_of_maps_to ?_ w
    intro L hL
    rw [hboxdef, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hbnds Δ hΔ L (hT L hL).2.1 (hT L hL).2.2).2.2 j)
  have hk_bound : ∀ k ∈ box,
      (∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k), w L)
        ≤ Knum * (if cond k then win k else 0) := by
    intro k hk
    by_cases hc : cond k
    · rw [if_pos hc]
      exact hfiber k T (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1⟩)
    · rw [if_neg hc]
      have hzero : (∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k), w L) = 0 := by
        apply Finset.sum_eq_zero
        intro L hL
        exfalso
        rw [Finset.mem_filter] at hL
        obtain ⟨hLT, hLk⟩ := hL
        apply hc
        constructor
        · rw [← hLk]
          exact (hbnds Δ hΔ L (hT L hLT).2.1 (hT L hLT).2.2).1
        · rw [← hLk]
          exact (hbnds Δ hΔ L (hT L hLT).2.1 (hT L hLT).2.2).2.1
      rw [hzero]
      simp
  have hsum1 : (∑ k ∈ box, ∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k), w L)
      ≤ ∑ k ∈ box, Knum * (if cond k then win k else 0) := Finset.sum_le_sum hk_bound
  have hsum2 : (∑ k ∈ box, Knum * (if cond k then win k else 0))
      = Knum * ∑ k ∈ box, (if cond k then win k else 0) := (Finset.mul_sum _ _ _).symm
  have harith' : (∑ k ∈ box, (if cond k then win k else 0))
      ≤ Karith * ((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3) := harith Δ hΔ
  have hlog' : ((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3) ≤ Klog * Δ ^ 24 :=
    hlog Δ hΔ
  calc (∑ L ∈ T, w L)
      = ∑ k ∈ box, ∑ L ∈ T.filter (fun L => Work.HP.kwin 3 L = k), w L := hfib.symm
    _ ≤ ∑ k ∈ box, Knum * (if cond k then win k else 0) := hsum1
    _ = Knum * ∑ k ∈ box, (if cond k then win k else 0) := hsum2
    _ ≤ Knum * (Karith * ((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left harith' hKnumpos.le
    _ ≤ Knum * (Karith * (Klog * Δ ^ 24)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnumpos.le
        have hre : Karith * ((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3)
            = Karith * (((N : ℝ) + 1) ^ 3 * (2 : ℝ) ^ (71 * (N : ℝ) / 3)) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hlog' hKarithpos.le
    _ = (Knum * Karith * Klog) * Δ ^ 24 := by ring

end Work.HP.MDEstimates
