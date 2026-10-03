import Mathlib
import Submission.Work.KMTAreas.A7.Split

/-!
# A uniform bound for the lacunary geometric sum `∑ ⌊a n⌋^{2d} δ² 1_{⌊a n⌋^d δ < 2^d}`

This module proves `Work.KMTPlan.A6.lacunaryGeometricSumLeENNReal`: for a `Λ`-lacunary sequence
`a : ℕ → ℝ≥0` (`Λ > 1`) with `a n ≥ 1`, and every `δ ≥ 0`,

`∑'_n (⌊a n⌋^d δ)² · 1_{⌊a n⌋^d δ < 2^d} ≤ C(Λ, d) < ∞`.

The point is that although the summands *grow* with `n`, the summation is restricted to the
indices with `⌊a n⌋^d δ < 2^d`, and there the terms decay geometrically in the index (with a
ratio `ρ < 1` depending only on `Λ`), because the floors of a lacunary sequence grow at least
as fast as `θ^n` for some `θ > 1`.  Consequently the (finite) sum is dominated by a geometric
series with sum `≤ C(Λ,d)`, uniformly in `a` and `δ`.

## Structure

* `lacunaryFloorMono` : `⌊a ·⌋` is monotone;
* `lacunaryFloorRatio` : there are `θ > 1`, `N₀` with `θ^{m-n} ⌊a n⌋ ≤ ⌊a m⌋` for `N₀ ≤ n ≤ m`;
* `lacunaryFloorDecay` : the pointwise geometric decay of the summands;
* `geomRangeReflectLe` : `∑_{n ≤ c} ρ^{c-n} ≤ (1-ρ)⁻¹` for `0 ≤ ρ < 1`;
* `rangeSumENNReal_le` / `tsumENNReal_le_of_decay` : the `Finset`/`ENNReal` bookkeeping turning
  the pointwise decay into the `tsum` bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal BigOperators

/-! ### Monotonicity of the floors -/

/-- The floors `⌊a n⌋` of a `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` are nondecreasing. -/
theorem lacunaryFloorMono {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone fun n => Nat.floor (a n) := by
  have hmono : Monotone a := monotone_nat_of_le_succ fun n => by
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have hlt : Λ * a n < a (n + 1) := (lt_div_iff₀ hpos).mp (ha n)
    calc a n = 1 * a n := (one_mul _).symm
      _ ≤ Λ * a n := mul_le_mul_of_nonneg_right hΛ.le hpos.le
      _ ≤ a (n + 1) := le_of_lt hlt
  intro i j hij
  exact Nat.floor_mono (hmono hij)

/-! ### The uniform ratio bound for the floors -/

/-- **Uniform ratio bound.**  For a `Λ`-lacunary sequence with `Λ > 1` there are `θ ∈ (1, Λ)` and
`N₀` such that `θ ^ (m - n) * ⌊a n⌋ ≤ ⌊a m⌋` for all `n ≥ N₀` and `m ≥ n`. -/
theorem lacunaryFloorRatio (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ θ : ℝ, 1 < θ ∧ θ < (Λ : ℝ) ∧ ∃ N₀ : ℕ,
      ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
        (n m : ℕ), N₀ ≤ n → n ≤ m →
        θ ^ (m - n) * (Nat.floor (a n) : ℝ) ≤ (Nat.floor (a m) : ℝ) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hLamp : (0 : ℝ) < (Λ : ℝ) := by linarith
  have hΛm1 : (0 : ℝ) < (Λ : ℝ) - 1 := by linarith
  set θ : ℝ := (1 + (Λ : ℝ)) / 2 with hθdef
  have hθ1 : 1 < θ := by rw [hθdef]; linarith
  have hθΛ : θ < (Λ : ℝ) := by rw [hθdef]; linarith
  have hθpos : (0 : ℝ) < θ := lt_trans zero_lt_one hθ1
  have hθdiff : (Λ : ℝ) - θ = ((Λ : ℝ) - 1) / 2 := by rw [hθdef]; ring
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, 2 / ((Λ : ℝ) - 1) + 1 ≤ (Λ : ℝ) ^ n := by
    have ht : Filter.Tendsto (fun n : ℕ => (Λ : ℝ) ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hΛR
    exact Filter.eventually_atTop.mp
      (ht.eventually (Filter.eventually_ge_atTop (2 / ((Λ : ℝ) - 1) + 1)))
  refine ⟨θ, hθ1, hθΛ, N₀, ?_⟩
  intro a ha ha1 n m hn hm
  have hgrow : ∀ j, Λ * a j ≤ a (j + 1) := by
    intro j
    have hpos : (0 : NNReal) < a j := lt_of_lt_of_le zero_lt_one (ha1 j)
    exact le_of_lt ((lt_div_iff₀ hpos).mp (ha j))
  have hpow : ∀ j : ℕ, (Λ : ℝ) ^ j ≤ (a j : ℝ) := by
    intro j
    induction j with
    | zero =>
        have h1 : (1 : ℝ) ≤ (a 0 : ℝ) := by
          have h := ha1 0
          exact_mod_cast h
        simpa using h1
    | succ i ih =>
        have hstep : (Λ : ℝ) * (a i : ℝ) ≤ (a (i + 1) : ℝ) := by
          have h := hgrow i
          have h' : ((Λ * a i : NNReal) : ℝ) ≤ ((a (i + 1) : NNReal) : ℝ) :=
            NNReal.coe_le_coe.mpr h
          simpa using h'
        calc (Λ : ℝ) ^ (i + 1) = (Λ : ℝ) * (Λ : ℝ) ^ i := pow_succ' _ i
          _ ≤ (Λ : ℝ) * (a i : ℝ) := mul_le_mul_of_nonneg_left ih hLamp.le
          _ ≤ (a (i + 1) : ℝ) := hstep
  have hbig : ∀ j, N₀ ≤ j → 2 / ((Λ : ℝ) - 1) ≤ (Nat.floor (a j) : ℝ) := by
    intro j hj
    have h1 : 2 / ((Λ : ℝ) - 1) + 1 ≤ (a j : ℝ) := le_trans (hN₀ j hj) (hpow j)
    have h2 : (a j : ℝ) < (Nat.floor (a j) : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (a j)
      have h3 : ((a j : NNReal) : ℝ) < ((Nat.floor (a j) : NNReal) : ℝ) + 1 :=
        NNReal.coe_lt_coe.mpr h
      simpa using h3
    linarith
  have hstep : ∀ j, N₀ ≤ j → θ * (Nat.floor (a j) : ℝ) ≤ (Nat.floor (a (j + 1)) : ℝ) := by
    intro j hj
    have hfl : (Nat.floor (a j) : ℝ) ≤ (a j : ℝ) := by
      have h := Nat.floor_le (show (0 : NNReal) ≤ a j by positivity)
      have h' : ((Nat.floor (a j) : NNReal) : ℝ) ≤ ((a j : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr h
      simpa using h'
    have hA : 2 / ((Λ : ℝ) - 1) ≤ (Nat.floor (a j) : ℝ) := hbig j hj
    have h1 : (Λ : ℝ) * (a j : ℝ) - 1 < (Nat.floor (a (j + 1)) : ℝ) := by
      have h2 : (Λ : ℝ) * (a j : ℝ) - 1 < ((Nat.floor (Λ * a j) : ℕ) : ℝ) := by
        have h := Nat.lt_floor_add_one (Λ * a j)
        have h3 : ((Λ * a j : NNReal) : ℝ) < ((Nat.floor (Λ * a j) : NNReal) : ℝ) + 1 :=
          NNReal.coe_lt_coe.mpr h
        have h4 : ((Λ : NNReal) : ℝ) * ((a j : NNReal) : ℝ)
            < ((Nat.floor (Λ * a j) : ℕ) : ℝ) + 1 := by simpa using h3
        linarith
      have h5 : ((Nat.floor (Λ * a j) : ℕ) : ℝ) ≤ (Nat.floor (a (j + 1)) : ℝ) := by
        have h := Nat.floor_mono (hgrow j)
        exact_mod_cast h
      linarith
    have h6 : θ * (Nat.floor (a j) : ℝ) ≤ (Λ : ℝ) * (Nat.floor (a j) : ℝ) - 1 := by
      have h7 : (1 : ℝ) ≤ ((Λ : ℝ) - θ) * (Nat.floor (a j) : ℝ) := by
        rw [hθdiff]
        calc (1 : ℝ) = ((Λ : ℝ) - 1) / 2 * (2 / ((Λ : ℝ) - 1)) := by
              rw [div_mul_div_comm, mul_comm 2 ((Λ : ℝ) - 1),
                div_self (mul_ne_zero (ne_of_gt hΛm1) (by norm_num))]
          _ ≤ ((Λ : ℝ) - 1) / 2 * (Nat.floor (a j) : ℝ) :=
              mul_le_mul_of_nonneg_left hA (by positivity)
      linarith
    have h8 : (Λ : ℝ) * (Nat.floor (a j) : ℝ) ≤ (Λ : ℝ) * (a j : ℝ) :=
      mul_le_mul_of_nonneg_left hfl hLamp.le
    linarith
  have hiter : ∀ k : ℕ, θ ^ k * (Nat.floor (a n) : ℝ) ≤ (Nat.floor (a (n + k)) : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ i ih =>
        have hs := hstep (n + i) (le_trans hn (Nat.le_add_right n i))
        calc θ ^ (i + 1) * (Nat.floor (a n) : ℝ)
            = θ * (θ ^ i * (Nat.floor (a n) : ℝ)) := by rw [pow_succ']; ring
          _ ≤ θ * (Nat.floor (a (n + i)) : ℝ) := mul_le_mul_of_nonneg_left ih hθpos.le
          _ ≤ (Nat.floor (a (n + i + 1)) : ℝ) := hs
          _ = (Nat.floor (a (n + (i + 1))) : ℝ) := by rw [Nat.add_assoc]
  have hfin := hiter (m - n)
  rwa [Nat.add_sub_of_le hm] at hfin

/-! ### Pointwise geometric decay -/

/-- **Pointwise decay of the lacunary summands.**  There are `ρ ∈ [0, 1)` and `N₀` such that for a
`Λ`-lacunary sequence `a ≥ 1`, `δ ≥ 0` and `n ≤ k` with `⌊a k⌋^d δ < 2^d`, the `n`-th summand is
bounded by `2^{2d} ρ^{k-n}` (and by `2^{2d}` for `n < N₀`). -/
theorem lacunaryFloorDecay (Λ : NNReal) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ N₀ : ℕ,
      ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
        (δ : ℝ), 0 ≤ δ → ∀ k n : ℕ, n ≤ k →
        (((Nat.floor (a k) : ℝ)) ^ d * δ < (2 : ℝ) ^ d) →
        (((Nat.floor (a n) : ℝ)) ^ d * δ) ^ 2 *
            (if ((Nat.floor (a n) : ℝ)) ^ d * δ < (2 : ℝ) ^ d then 1 else 0)
          ≤ (2 : ℝ) ^ (2 * d) * (if n < N₀ then 1 else ρ ^ (k - n)) := by
  obtain ⟨θ, hθ1, hθΛ, N₁, hratio⟩ := lacunaryFloorRatio Λ hΛ
  have hθpos : (0 : ℝ) < θ := lt_trans zero_lt_one hθ1
  have hθinv0 : (0 : ℝ) ≤ θ⁻¹ := le_of_lt (inv_pos.mpr hθpos)
  have hθinv1 : θ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hθ1
  have hρlt : (θ⁻¹) ^ 2 < 1 := pow_lt_one₀ hθinv0 hθinv1 two_ne_zero
  refine ⟨(θ⁻¹) ^ 2, by positivity, hρlt, N₁, ?_⟩
  intro a ha ha1 δ hδ k n hnk hkcond
  rcases lt_or_ge n N₁ with hlt | hge
  · rw [if_pos hlt]
    rcases lt_or_ge (((Nat.floor (a n) : ℝ)) ^ d * δ) ((2 : ℝ) ^ d) with hc | hc
    · rw [if_pos hc]
      have h1 : ((Nat.floor (a n) : ℝ)) ^ d * δ ≤ (2 : ℝ) ^ d := le_of_lt hc
      have h2 : (0 : ℝ) ≤ ((Nat.floor (a n) : ℝ)) ^ d * δ := by positivity
      have h3 : (((Nat.floor (a n) : ℝ)) ^ d * δ) ^ 2 ≤ ((2 : ℝ) ^ d) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      have h4 : ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ (2 * d) := by
        rw [← pow_mul, Nat.mul_comm d 2]
      simpa [h4] using h3
    · rw [if_neg (not_lt.mpr hc), mul_zero]
      exact mul_nonneg (by positivity) zero_le_one
  · rw [if_neg (not_lt.mpr hge)]
    have hAmono : Monotone fun j => Nat.floor (a j) := lacunaryFloorMono hΛ ha ha1
    have hcondn : ((Nat.floor (a n) : ℝ)) ^ d * δ < (2 : ℝ) ^ d := by
      have h1 : ((Nat.floor (a n) : ℝ)) ≤ (Nat.floor (a k) : ℝ) := by
        exact_mod_cast hAmono hnk
      have h2 : ((Nat.floor (a n) : ℝ)) ^ d ≤ ((Nat.floor (a k) : ℝ)) ^ d :=
        pow_le_pow_left₀ (by positivity) h1 d
      have h3 : ((Nat.floor (a n) : ℝ)) ^ d * δ ≤ ((Nat.floor (a k) : ℝ)) ^ d * δ :=
        mul_le_mul_of_nonneg_right h2 hδ
      linarith
    rw [if_pos hcondn, mul_one]
    have hAn : ((Nat.floor (a n) : ℝ)) ≤ ((Nat.floor (a k) : ℝ)) * (θ⁻¹) ^ (k - n) := by
      have h1 := hratio a ha ha1 n k hge hnk
      have h2 : (0 : ℝ) < θ ^ (k - n) := pow_pos hθpos _
      have h3 : ((Nat.floor (a n) : ℝ)) ≤ ((Nat.floor (a k) : ℝ)) / θ ^ (k - n) := by
        rw [le_div_iff₀ h2]
        calc ((Nat.floor (a n) : ℝ)) * θ ^ (k - n)
            = θ ^ (k - n) * ((Nat.floor (a n) : ℝ)) := mul_comm _ _
          _ ≤ ((Nat.floor (a k) : ℝ)) := h1
      rwa [div_eq_mul_inv, ← inv_pow] at h3
    have hAnu : ((Nat.floor (a n) : ℝ)) ^ d
        ≤ ((Nat.floor (a k) : ℝ)) ^ d * (θ⁻¹) ^ (k - n) := by
      have h4 : ((Nat.floor (a n) : ℝ)) ^ d
          ≤ (((Nat.floor (a k) : ℝ)) * (θ⁻¹) ^ (k - n)) ^ d :=
        pow_le_pow_left₀ (by positivity) hAn d
      have h5 : (((Nat.floor (a k) : ℝ)) * (θ⁻¹) ^ (k - n)) ^ d
          = ((Nat.floor (a k) : ℝ)) ^ d * ((θ⁻¹) ^ (k - n)) ^ d := mul_pow _ _ _
      have h6 : ((θ⁻¹) ^ (k - n)) ^ d = (θ⁻¹) ^ (d * (k - n)) := by
        rw [← pow_mul, Nat.mul_comm (k - n) d]
      have h7 : (θ⁻¹) ^ (d * (k - n)) ≤ (θ⁻¹) ^ (k - n) := by
        refine pow_le_pow_of_le_one hθinv0 (le_of_lt hθinv1) ?_
        calc k - n = (k - n) * 1 := (mul_one _).symm
          _ ≤ (k - n) * d := mul_le_mul_right hd (k - n)
          _ = d * (k - n) := Nat.mul_comm _ _
      calc ((Nat.floor (a n) : ℝ)) ^ d
            ≤ ((Nat.floor (a k) : ℝ)) ^ d * ((θ⁻¹) ^ (k - n)) ^ d := by rw [← h5]; exact h4
        _ = ((Nat.floor (a k) : ℝ)) ^ d * (θ⁻¹) ^ (d * (k - n)) := by rw [h6]
        _ ≤ ((Nat.floor (a k) : ℝ)) ^ d * (θ⁻¹) ^ (k - n) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
    have hAnuδ : ((Nat.floor (a n) : ℝ)) ^ d * δ ≤ (2 : ℝ) ^ d * (θ⁻¹) ^ (k - n) :=
      calc ((Nat.floor (a n) : ℝ)) ^ d * δ
            ≤ (((Nat.floor (a k) : ℝ)) ^ d * (θ⁻¹) ^ (k - n)) * δ :=
              mul_le_mul_of_nonneg_right hAnu hδ
        _ = (((Nat.floor (a k) : ℝ)) ^ d * δ) * (θ⁻¹) ^ (k - n) := by ring
        _ ≤ (2 : ℝ) ^ d * (θ⁻¹) ^ (k - n) :=
              mul_le_mul_of_nonneg_right (le_of_lt hkcond) (by positivity)
    calc (((Nat.floor (a n) : ℝ)) ^ d * δ) ^ 2
          ≤ ((2 : ℝ) ^ d * (θ⁻¹) ^ (k - n)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hAnuδ 2
      _ = (2 : ℝ) ^ (2 * d) * ((θ⁻¹) ^ 2) ^ (k - n) := by
            have e1 : ((2 : ℝ) ^ d) ^ 2 = (2 : ℝ) ^ (2 * d) := by
              rw [← pow_mul, Nat.mul_comm d 2]
            have e2 : ((θ⁻¹) ^ (k - n)) ^ 2 = ((θ⁻¹) ^ 2) ^ (k - n) := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm (k - n) 2]
            rw [mul_pow, e1, e2]

/-! ### The reflected geometric sum -/

/-- The reflected partial geometric sum is bounded by the full series. -/
theorem geomRangeReflectLe (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (c : ℕ) :
    ∑ n ∈ Finset.range (c + 1), ρ ^ (c - n) ≤ (1 - ρ)⁻¹ := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hrefl : (∑ n ∈ Finset.range (c + 1), ρ ^ (c - n))
      = ∑ n ∈ Finset.range (c + 1), ρ ^ n := by
    rw [← Finset.sum_range_reflect (fun j => ρ ^ j) (c + 1)]
    rfl
  rw [hrefl, inv_eq_one_div, le_div_iff₀ h1ρ]
  have htel : (∑ i ∈ Finset.range (c + 1), ρ ^ i) * (1 - ρ) = 1 - ρ ^ (c + 1) :=
    geom_sum_mul_neg ρ (c + 1)
  rw [htel]
  have hp := pow_nonneg hρ0 (c + 1)
  linarith

/-! ### From the pointwise decay to the `tsum` bound -/

/-- **Finite-range form of the bound.**  If `f ≥ 0` decays as in `lacunaryFloorDecay`, then every
partial sum of the `ENNReal.ofReal (f n)` is bounded by `ofReal (c * (N₀ + (1-ρ)⁻¹))`. -/
lemma rangeSumENNReal_le (f : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (N₀ : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (h0 : ∀ n, 0 ≤ f n)
    (hpoint : ∀ k n : ℕ, n ≤ k → f k ≠ 0 →
      f n ≤ c * (if n < N₀ then (1 : ℝ) else ρ ^ (k - n)))
    (hgeom : ∀ k : ℕ, ∑ n ∈ Finset.range (k + 1), ρ ^ (k - n) ≤ (1 - ρ)⁻¹) (K : ℕ) :
    ∑ n ∈ Finset.range K, ENNReal.ofReal (f n)
      ≤ ENNReal.ofReal (c * ((N₀ : ℝ) + (1 - ρ)⁻¹)) := by
  classical
  set s : Finset ℕ := (Finset.range K).filter (fun n => f n ≠ 0) with hsdef
  by_cases hs : s = ∅
  · have hz : ∀ n ∈ Finset.range K, f n = 0 := by
      intro n hn
      by_contra hne
      have hmem : n ∈ s := by rw [hsdef]; exact Finset.mem_filter.mpr ⟨hn, hne⟩
      rw [hs] at hmem
      simp at hmem
    rw [Finset.sum_eq_zero (fun n hn => by rw [hz n hn, ENNReal.ofReal_zero])]
    exact bot_le
  · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    set k : ℕ := s.max' hne with hkdef
    have hks : k ∈ s := by rw [hkdef]; exact Finset.max'_mem s hne
    have hks' : k ∈ (Finset.range K).filter (fun n => f n ≠ 0) := by rwa [hsdef] at hks
    have hkne : f k ≠ 0 := (Finset.mem_filter.mp hks').2
    have hkK : k ∈ Finset.range K := (Finset.mem_filter.mp hks').1
    have hkmax : ∀ n ∈ s, n ≤ k := by
      intro n hn
      rw [hkdef]
      exact Finset.le_max' s n hn
    have hsub : Finset.range (k + 1) ⊆ Finset.range K := by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [Finset.mem_range]
      have hklt : k < K := Finset.mem_range.mp hkK
      omega
    have hzE : ∀ n ∈ Finset.range K, n ∉ Finset.range (k + 1) →
        ENNReal.ofReal (f n) = 0 := by
      intro n hnK hnk
      have hz : f n = 0 := by
        by_contra hne'
        have hmem : n ∈ s := by rw [hsdef]; exact Finset.mem_filter.mpr ⟨hnK, hne'⟩
        have hle := hkmax n hmem
        rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hnk
        omega
      rw [hz, ENNReal.ofReal_zero]
    rw [← Finset.sum_subset hsub hzE]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => h0 n)]
    apply ENNReal.ofReal_le_ofReal
    calc ∑ n ∈ Finset.range (k + 1), f n
        ≤ ∑ n ∈ Finset.range (k + 1), c * (if n < N₀ then (1 : ℝ) else ρ ^ (k - n)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hpoint k n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) hkne
      _ = c * ∑ n ∈ Finset.range (k + 1), (if n < N₀ then (1 : ℝ) else ρ ^ (k - n)) := by
          rw [Finset.mul_sum]
      _ ≤ c * ((N₀ : ℝ) + (1 - ρ)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ hc
          have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (k + 1))
            (fun n => n < N₀) (fun n => if n < N₀ then (1 : ℝ) else ρ ^ (k - n))
          rw [← hsplit]
          have h1 : ∑ n ∈ (Finset.range (k + 1)).filter (fun n => n < N₀),
              (if n < N₀ then (1 : ℝ) else ρ ^ (k - n)) ≤ (N₀ : ℝ) := by
            rw [Finset.sum_congr rfl (fun n hn => if_pos (Finset.mem_filter.mp hn).2)]
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            have hcard : ((Finset.range (k + 1)).filter (fun n => n < N₀)).card ≤ N₀ := by
              have hsub2 : ((Finset.range (k + 1)).filter (fun n => n < N₀)) ⊆ Finset.range N₀ := by
                intro n hn
                rw [Finset.mem_filter, Finset.mem_range] at hn
                exact Finset.mem_range.mpr hn.2
              simpa using Finset.card_le_card hsub2
            exact_mod_cast hcard
          have h2 : ∑ n ∈ (Finset.range (k + 1)).filter (fun n => ¬ n < N₀),
              (if n < N₀ then (1 : ℝ) else ρ ^ (k - n)) ≤ (1 - ρ)⁻¹ := by
            rw [Finset.sum_congr rfl (fun n hn => if_neg (Finset.mem_filter.mp hn).2)]
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
              (fun n hn => (Finset.mem_filter.mp hn).1)
              (fun i hi his => pow_nonneg hρ0 _)) (hgeom k)
          linarith

/-- **The `tsum` bound in `ENNReal`.** -/
lemma tsumENNReal_le_of_decay (d : ℕ) (A : ℕ → ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (N₀ : ℕ)
    (hdecay : ∀ k n : ℕ, n ≤ k → (A k : ℝ) ^ d * δ < (2 : ℝ) ^ d →
      ((A n : ℝ) ^ d * δ) ^ 2 * (if (A n : ℝ) ^ d * δ < (2 : ℝ) ^ d then 1 else 0)
        ≤ (2 : ℝ) ^ (2 * d) * (if n < N₀ then 1 else ρ ^ (k - n)))
    (hgeom : ∀ k : ℕ, ∑ n ∈ Finset.range (k + 1), ρ ^ (k - n) ≤ (1 - ρ)⁻¹) :
    (∑' n : ℕ, ENNReal.ofReal (((A n : ℝ) ^ d * δ) ^ 2 *
        (if (A n : ℝ) ^ d * δ < (2 : ℝ) ^ d then 1 else 0)))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d) * ((N₀ : ℝ) + (1 - ρ)⁻¹)) := by
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * d) := by positivity
  have hf0 : ∀ n, 0 ≤ ((A n : ℝ) ^ d * δ) ^ 2 *
      (if (A n : ℝ) ^ d * δ < (2 : ℝ) ^ d then (1 : ℝ) else 0) := by
    intro n
    rcases lt_or_ge ((A n : ℝ) ^ d * δ) ((2 : ℝ) ^ d) with h | h
    · rw [if_pos h]
      exact mul_nonneg (sq_nonneg _) zero_le_one
    · rw [if_neg (not_lt.mpr h), mul_zero]
  have hcondne : ∀ k : ℕ, ((A k : ℝ) ^ d * δ) ^ 2 *
      (if (A k : ℝ) ^ d * δ < (2 : ℝ) ^ d then (1 : ℝ) else 0) ≠ 0 →
      (A k : ℝ) ^ d * δ < (2 : ℝ) ^ d := by
    intro k hk
    by_contra h
    rw [if_neg h, mul_zero] at hk
    exact hk rfl
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le (fun K => ?_)
  exact rangeSumENNReal_le (fun n => ((A n : ℝ) ^ d * δ) ^ 2 *
      (if (A n : ℝ) ^ d * δ < (2 : ℝ) ^ d then (1 : ℝ) else 0)) ((2 : ℝ) ^ (2 * d)) hc N₀ ρ
    hρ0 hf0 (fun k n hnk hkne => hdecay k n hnk (hcondne k hkne)) hgeom K

/-! ### The main theorem -/

theorem lacunaryGeometricSumLeENNReal (Λ : NNReal) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n : ℕ, 1 ≤ a n) (δ : ℝ), 0 ≤ δ →
      (∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℝ)) ^ d * δ) ^ 2 *
        (if ((Nat.floor (a n) : ℝ)) ^ d * δ < (2 : ℝ) ^ d then 1 else 0))) ≤ C := by
  obtain ⟨ρ, hρ0, hρ1, N₀, hdecay⟩ := lacunaryFloorDecay Λ hΛ d hd
  refine ⟨ENNReal.ofReal ((2 : ℝ) ^ (2 * d) * ((N₀ : ℝ) + (1 - ρ)⁻¹)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro a ha ha1 δ hδ
  exact tsumENNReal_le_of_decay d (fun n => Nat.floor (a n)) δ hδ ρ hρ0 N₀
    (fun k n hnk hk => hdecay a ha ha1 δ hδ k n hnk hk)
    (fun k => geomRangeReflectLe ρ hρ0 hρ1 k)

end Work.KMTPlan.A6
