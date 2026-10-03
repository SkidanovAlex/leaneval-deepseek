import Mathlib
import Submission.Work.Analysis.EndVar.Sums

set_option autoImplicit false

namespace Work.KMTAreas.A7

open Filter

/-- **Tail bound for the reciprocals of `⌊a n⌋`.**  For a `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with
`a n ≥ 1`, the sum of `1/⌊a n⌋` over the indices with `⌊a n⌋ ≥ M` is bounded by `C / M` with `C`
depending only on `Λ` (and not on `M` nor on `a`).

Indeed, if `N` is the least index with `a N ≥ M`, then for `n ≥ N` the lacunarity gives
`a n ≥ Λ^{n-N} M`, while on the support `⌊a n⌋ ≥ M ≥ 2 ≥ a n / 2`; hence
`1/⌊a n⌋ ≤ 2/(a n) ≤ (2/M) · Λ^{-(n-N)}`, and summing the geometric series gives
`2/(1 - Λ⁻¹) · 1/M = 2Λ/((Λ-1)M)`. -/
theorem invFloor_tail_le (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℝ), 2 ≤ M → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Summable (fun n : ℕ => if M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
          then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0) ∧
      (∑' n : ℕ, (if M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
          then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)) ≤ C / M := by
  refine ⟨2 * (Λ : ℝ) / ((Λ : ℝ) - 1), ?_, ?_⟩
  · have hL : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have h1 : (0 : ℝ) < (Λ : ℝ) - 1 := by linarith
    exact div_nonneg (by linarith) h1.le
  · intro M hM a ha ha1
    have hL : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
    have hL0 : (0 : ℝ) < (Λ : ℝ) := lt_trans zero_lt_one hL
    have hM0 : (0 : ℝ) < M := by linarith
    have hposn : ∀ n, (0 : ℝ) < (a n : ℝ) := by
      intro n
      have h := ha1 n
      exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
    -- the lacunarity step in `ℝ`
    have hstepR : ∀ m, (Λ : ℝ) * (a m : ℝ) < (a (m + 1) : ℝ) := by
      intro m
      have hm : (Λ : NNReal) < a (m + 1) / a m := ha m
      have hm' : ((Λ : NNReal) : ℝ) < ((a (m + 1) / a m : NNReal) : ℝ) :=
        NNReal.coe_lt_coe.mpr hm
      have hdiv : (Λ : ℝ) < (a (m + 1) : ℝ) / (a m : ℝ) := by
        rwa [NNReal.coe_div] at hm'
      exact (lt_div_iff₀ (hposn m)).mp hdiv
    -- growth `Λ^n ≤ a n`
    have hpow : ∀ n, (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
      intro n
      induction n with
      | zero => simpa using (NNReal.coe_le_coe.mpr (ha1 0))
      | succ n ih =>
          calc (Λ : ℝ) ^ (n + 1) = (Λ : ℝ) * (Λ : ℝ) ^ n := by rw [pow_succ, mul_comm]
            _ ≤ (Λ : ℝ) * (a n : ℝ) := mul_le_mul_of_nonneg_left ih hL0.le
            _ ≤ (a (n + 1) : ℝ) := (hstepR n).le
    -- `a` eventually exceeds `M`
    have hev : ∀ᶠ n in atTop, M ≤ (a n : ℝ) :=
      ((tendsto_pow_atTop_atTop_of_one_lt hL).eventually (eventually_ge_atTop M)).mono
        (fun n hn => le_trans hn (hpow n))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
    have hnex : ∃ n, M ≤ (a n : ℝ) := ⟨N₀, hN₀ N₀ le_rfl⟩
    -- the least such index
    let N : ℕ := Nat.find hnex
    have hNle : M ≤ (a N : ℝ) := Nat.find_spec hnex
    have hNlt : ∀ m < N, (a m : ℝ) < M := fun m hm => lt_of_not_ge (Nat.find_min hnex hm)
    -- growth from the threshold index
    have hgrowth : ∀ k, M * (Λ : ℝ) ^ k ≤ (a (k + N) : ℝ) := by
      intro k
      induction k with
      | zero => simpa using hNle
      | succ k ih =>
          have hstep : (Λ : ℝ) * (a (k + N) : ℝ) ≤ (a ((k + 1) + N) : ℝ) := by
            have h := (hstepR (k + N)).le
            have hidx : k + N + 1 = (k + 1) + N := by omega
            rwa [hidx] at h
          calc M * (Λ : ℝ) ^ (k + 1) = (Λ : ℝ) * (M * (Λ : ℝ) ^ k) := by rw [pow_succ]; ring
            _ ≤ (Λ : ℝ) * (a (k + N) : ℝ) := mul_le_mul_of_nonneg_left ih hL0.le
            _ ≤ (a ((k + 1) + N) : ℝ) := hstep
    -- the summand
    set f : ℕ → ℝ := fun n => (if M ≤ ((Nat.floor (a n) : ℕ) : ℝ)
        then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0) with hfdef
    have hfnonneg : ∀ n, 0 ≤ f n := by
      intro n
      simp only [hfdef]
      split_ifs with h
      · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · exact le_refl 0
    -- below the threshold the summand vanishes
    have hfzero : ∀ n < N, f n = 0 := by
      intro n hn
      have hφ : ((Nat.floor (a n) : ℕ) : ℝ) ≤ (a n : ℝ) := by
        have h : ((Nat.floor (a n) : ℕ) : NNReal) ≤ a n :=
          Nat.floor_le (show (0 : NNReal) ≤ a n by positivity)
        exact_mod_cast h
      have hlt : ((Nat.floor (a n) : ℕ) : ℝ) < M := lt_of_le_of_lt hφ (hNlt n hn)
      rw [hfdef]
      simp only [if_neg (not_le.mpr hlt)]
    -- the pointwise geometric bound
    have hpt : ∀ k, f (k + N) ≤ (2 / M) * ((Λ : ℝ)⁻¹) ^ k := by
      intro k
      by_cases hcond : M ≤ ((Nat.floor (a (k + N)) : ℕ) : ℝ)
      · have hφge : (2 : ℝ) ≤ ((Nat.floor (a (k + N)) : ℕ) : ℝ) := le_trans hM hcond
        have hφpos : (0 : ℝ) < ((Nat.floor (a (k + N)) : ℕ) : ℝ) := by linarith
        have hlt1 : (a (k + N) : ℝ) < ((Nat.floor (a (k + N)) : ℕ) : ℝ) + 1 := by
          have h : a (k + N) < ((Nat.floor (a (k + N)) : ℕ) : NNReal) + 1 :=
            Nat.lt_floor_add_one _
          have hc := NNReal.coe_lt_coe.mpr h
          push_cast at hc
          exact hc
        have hanle : (a (k + N) : ℝ) ≤ 2 * ((Nat.floor (a (k + N)) : ℕ) : ℝ) := by linarith
        have hinv : (((Nat.floor (a (k + N)) : ℕ) : ℝ))⁻¹ ≤ 2 / (a (k + N) : ℝ) := by
          have hpos2 : (0 : ℝ) < (a (k + N) : ℝ) / 2 := by
            have hp := hposn (k + N)
            linarith
          have hhalf : (a (k + N) : ℝ) / 2 ≤ ((Nat.floor (a (k + N)) : ℕ) : ℝ) := by
            linarith
          have h1 : (1 : ℝ) / ((Nat.floor (a (k + N)) : ℕ) : ℝ)
              ≤ 1 / ((a (k + N) : ℝ) / 2) :=
            one_div_le_one_div_of_le hpos2 hhalf
          have h2 : (1 : ℝ) / ((a (k + N) : ℝ) / 2) = 2 / (a (k + N) : ℝ) := by ring
          rw [inv_eq_one_div, ← h2]
          exact h1
        have hgeo : 2 / (a (k + N) : ℝ) ≤ (2 / M) * ((Λ : ℝ)⁻¹) ^ k := by
          have hg := hgrowth k
          have hgpos : (0 : ℝ) < M * (Λ : ℝ) ^ k := by positivity
          calc 2 / (a (k + N) : ℝ) ≤ 2 / (M * (Λ : ℝ) ^ k) :=
                div_le_div_of_nonneg_left (by norm_num) hgpos hg
            _ = (2 / M) * ((Λ : ℝ)⁻¹) ^ k := by
                rw [inv_pow]
                field_simp
        simp only [hfdef]
        rw [if_pos hcond]
        exact le_trans hinv hgeo
      · simp only [hfdef]
        rw [if_neg hcond]
        positivity
    -- the dominating geometric series
    have hrinv1 : ((Λ : ℝ)⁻¹) < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hL
    have hsumg : Summable (fun k : ℕ => (2 / M) * ((Λ : ℝ)⁻¹) ^ k) := by
      have hr : ‖(Λ : ℝ)⁻¹‖ < 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact hrinv1
      exact (summable_geometric_of_norm_lt_one hr).mul_left (2 / M)
    have hsum_shift : Summable (fun k : ℕ => f (k + N)) :=
      Summable.of_nonneg_of_le (fun k => hfnonneg (k + N)) (fun k => hpt k) hsumg
    have hsumf : Summable f := (summable_nat_add_iff N).mp hsum_shift
    -- the shifted sum equals the original one
    have hshift : (∑' k : ℕ, f (k + N)) = ∑' n : ℕ, f n := by
      have h := hsumf.sum_add_tsum_nat_add N
      have hz : ∑ i ∈ Finset.range N, f i = 0 :=
        Finset.sum_eq_zero (fun i hi => hfzero i (Finset.mem_range.mp hi))
      linarith
    have hbound : (∑' n : ℕ, f n) ≤ 2 * (Λ : ℝ) / ((Λ : ℝ) - 1) / M := by
      rw [← hshift]
      calc (∑' k : ℕ, f (k + N)) ≤ ∑' k : ℕ, (2 / M) * ((Λ : ℝ)⁻¹) ^ k :=
            Summable.tsum_le_tsum hpt hsum_shift hsumg
        _ = (2 / M) * (1 - (Λ : ℝ)⁻¹)⁻¹ := by
            rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hrinv1]
        _ = 2 * (Λ : ℝ) / ((Λ : ℝ) - 1) / M := by
            field_simp
    exact ⟨hsumf, hbound⟩

end Work.KMTAreas.A7
