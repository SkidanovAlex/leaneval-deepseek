import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-!
# `tent_sum`

A dyadic (`tent`-shaped) sum bound used in the deviation step of Wilkie's conjecture.

With `K = ⌈log₂ (x₂ / x₁)⌉` and `q = 2 ^ (-η)`, each summand
`δ (min (x₁·2^k / a) (b / (x₁·2^k)))` is bounded by `β · N^{-η} (q^k + q^{K-1-k})`:
the two arguments of the `min` are bounded below by `N·2^k` and `N·2^{K-1-k}`
respectively, so the minimum is bounded below by the minimum of these, whose
`(-η)`-th power is at most the sum. Summing the two geometric series (the second
being the reverse of the first) gives the claimed bound.
-/

theorem tent_sum {N : ℕ} (hN : 1 ≤ N) {δ : ℝ → ℝ} {β η : ℝ}
    (hδ0 : ∀ M : ℝ, 0 < M → 0 ≤ δ M)
    (hanti : ∀ M M' : ℝ, 0 < M → M ≤ M' → δ M' ≤ δ M)
    (hη : 0 < η) (hβ : 0 < β)
    (hδ : ∀ M : ℝ, (N : ℝ) ≤ M → δ M ≤ β * M ^ (-(η : ℝ)))
    {x₁ x₂ a b : ℝ} (hx₁ : 0 < x₁) (hx₂ : x₁ ≤ x₂) (ha : 0 < a) (hb : 0 < b)
    (hda : (N : ℝ) * a < x₁) (hdb : (N : ℝ) * x₂ < b) :
    ∑ k ∈ Finset.range (Nat.ceil (Real.logb 2 (x₂ / x₁))),
        δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
      ≤ 2 * β * (N : ℝ) ^ (-(η : ℝ)) / (1 - (2 : ℝ) ^ (-(η : ℝ))) := by
  set K := Nat.ceil (Real.logb 2 (x₂ / x₁)) with hK
  set q : ℝ := (2 : ℝ) ^ (-(η : ℝ)) with hq
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hqpos : 0 < q := by rw [hq]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hqlt : q < 1 := by
    rw [hq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hNpowpos : (0 : ℝ) < (N : ℝ) ^ (-(η : ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hx2pos : 0 < x₂ := lt_of_lt_of_le hx₁ hx₂
  have hx2div : 0 < x₂ / x₁ := div_pos hx2pos hx₁
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- empty sum
    rw [hK0]
    simp only [Finset.range_zero, Finset.sum_empty]
    apply div_nonneg
    · exact (mul_pos (mul_pos (by norm_num) hβ) hNpowpos).le
    · exact (sub_pos.mpr hqlt).le
  · have hK1 : 1 ≤ K := hKpos
    -- `((2 ^ k)) ^ (-η) = q ^ k`
    have hpowid : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-(η : ℝ)) = q ^ k := by
      intro k
      rw [hq, ← Real.rpow_natCast 2 k,
        ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num) (k : ℝ) (-(η : ℝ)),
        show ((k : ℝ) * (-(η : ℝ))) = (-(η : ℝ)) * (k : ℝ) by ring,
        Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num) (-(η : ℝ)) (k : ℝ),
        Real.rpow_natCast]
    -- `2 ^ (K - 1) < x₂ / x₁`
    have hpowK : (2 : ℝ) ^ (K - 1) < x₂ / x₁ := by
      have h1 : (1 : ℝ) ≤ x₂ / x₁ := (one_le_div hx₁).mpr hx₂
      have hL0 : (0 : ℝ) ≤ Real.logb 2 (x₂ / x₁) := Real.logb_nonneg (by norm_num) h1
      have hceil : (K : ℝ) < Real.logb 2 (x₂ / x₁) + 1 := by
        rw [hK]; exact Nat.ceil_lt_add_one hL0
      have hKcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
        rw [Nat.cast_sub hK1]; norm_num
      have hlt : ((K - 1 : ℕ) : ℝ) < Real.logb 2 (x₂ / x₁) := by rw [hKcast]; linarith
      have hres := (Real.lt_logb_iff_rpow_lt (b := 2) (x := ((K - 1 : ℕ) : ℝ))
        (y := x₂ / x₁) (by norm_num) hx2div).mp hlt
      simpa [Real.rpow_natCast] using hres
    have hx12 : x₁ * (2 : ℝ) ^ (K - 1) < x₂ := by
      have h1 : x₁ * (2 : ℝ) ^ (K - 1) < x₁ * (x₂ / x₁) :=
        mul_lt_mul_of_pos_left hpowK hx₁
      rwa [mul_div_cancel₀ _ hx₁.ne'] at h1
    -- termwise bound
    have key : ∀ k ∈ Finset.range K,
        δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
          ≤ β * (N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk1 : k ≤ K - 1 := Nat.le_pred_of_lt hk
      have hC : (N : ℝ) * (2 : ℝ) ^ k ≤ x₁ * (2 : ℝ) ^ k / a := by
        rw [le_div_iff₀ ha]
        calc (N : ℝ) * (2 : ℝ) ^ k * a = ((N : ℝ) * a) * (2 : ℝ) ^ k := by ring
          _ ≤ x₁ * (2 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right hda.le (pow_nonneg (by norm_num) k)
      have hpow2 : (2 : ℝ) ^ (K - 1 - k) * (2 : ℝ) ^ k = (2 : ℝ) ^ (K - 1) := by
        rw [← pow_add, Nat.sub_add_cancel hk1]
      have hB : (N : ℝ) * (2 : ℝ) ^ (K - 1 - k) ≤ b / (x₁ * (2 : ℝ) ^ k) := by
        rw [le_div_iff₀ (mul_pos hx₁ (pow_pos (by norm_num) k))]
        have heq : (N : ℝ) * (2 : ℝ) ^ (K - 1 - k) * (x₁ * (2 : ℝ) ^ k)
            = (N : ℝ) * (x₁ * (2 : ℝ) ^ (K - 1)) := by
          rw [← hpow2]; ring
        rw [heq]
        exact (mul_lt_mul_of_pos_left hx12 hNpos).le.trans hdb.le
      have hmle : min ((N : ℝ) * (2 : ℝ) ^ k) ((N : ℝ) * (2 : ℝ) ^ (K - 1 - k))
            ≤ min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)) :=
        min_le_min hC hB
      have hmpos : 0 < min ((N : ℝ) * (2 : ℝ) ^ k) ((N : ℝ) * (2 : ℝ) ^ (K - 1 - k)) :=
        lt_min (mul_pos hNpos (pow_pos (by norm_num : (0 : ℝ) < 2) k))
          (mul_pos hNpos (pow_pos (by norm_num : (0 : ℝ) < 2) (K - 1 - k)))
      have hNs : (N : ℝ) ≤ min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)) := by
        have h1 : (N : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ k := by
          have := mul_le_mul_of_nonneg_left
            (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)) hNpos.le
          simpa using this
        have h2 : (N : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ (K - 1 - k) := by
          have := mul_le_mul_of_nonneg_left
            (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := K - 1 - k)) hNpos.le
          simpa using this
        exact (le_min h1 h2).trans hmle
      have hδs : δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
            ≤ β * (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k))) ^ (-(η : ℝ)) :=
        hδ _ hNs
      have hpowle : (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k))) ^ (-(η : ℝ))
            ≤ (min ((N : ℝ) * (2 : ℝ) ^ k) ((N : ℝ) * (2 : ℝ) ^ (K - 1 - k))) ^ (-(η : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hmpos hmle (by linarith)
      have hmq : (min ((N : ℝ) * (2 : ℝ) ^ k) ((N : ℝ) * (2 : ℝ) ^ (K - 1 - k))) ^ (-(η : ℝ))
            ≤ (N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k)) := by
        rcases le_total ((N : ℝ) * (2 : ℝ) ^ k) ((N : ℝ) * (2 : ℝ) ^ (K - 1 - k)) with hle | hle
        · rw [min_eq_left hle, Real.mul_rpow hNpos.le (pow_nonneg (by norm_num) k), hpowid k]
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right (pow_nonneg hqpos.le _)) hNpowpos.le
        · rw [min_eq_right hle,
            Real.mul_rpow hNpos.le (pow_nonneg (by norm_num) (K - 1 - k)), hpowid (K - 1 - k)]
          exact mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_left (pow_nonneg hqpos.le _)) hNpowpos.le
      calc δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
          ≤ β * (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k))) ^ (-(η : ℝ)) := hδs
        _ ≤ β * ((N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k))) :=
              mul_le_mul_of_nonneg_left (hpowle.trans hmq) hβ.le
        _ = β * (N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k)) := by ring
    have hsum : ∑ k ∈ Finset.range K,
        δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
      ≤ ∑ k ∈ Finset.range K, β * (N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k)) :=
      Finset.sum_le_sum key
    have hgeo : ∑ k ∈ Finset.range K, q ^ k ≤ (1 - q)⁻¹ := by
      have h1 : ∑ k ∈ Finset.range K, q ^ k = (1 - q ^ K) / (1 - q) := by
        have h3 : (0 : ℝ) < 1 - q := sub_pos.mpr hqlt
        rw [eq_div_iff h3.ne', geom_sum_mul_neg]
      rw [h1]
      have h2 : 1 - q ^ K ≤ 1 := by
        have := pow_nonneg hqpos.le K; linarith
      have h3 : 0 < 1 - q := sub_pos.mpr hqlt
      calc (1 - q ^ K) / (1 - q) ≤ 1 / (1 - q) := div_le_div_of_nonneg_right h2 h3.le
        _ = (1 - q)⁻¹ := by rw [one_div]
    have hreflect : ∑ k ∈ Finset.range K, q ^ (K - 1 - k) = ∑ k ∈ Finset.range K, q ^ k :=
      Finset.sum_range_reflect (fun k => q ^ k) K
    calc ∑ k ∈ Finset.range K, δ (min (x₁ * (2 : ℝ) ^ k / a) (b / (x₁ * (2 : ℝ) ^ k)))
        ≤ ∑ k ∈ Finset.range K, β * (N : ℝ) ^ (-(η : ℝ)) * (q ^ k + q ^ (K - 1 - k)) := hsum
      _ = β * (N : ℝ) ^ (-(η : ℝ)) * ∑ k ∈ Finset.range K, (q ^ k + q ^ (K - 1 - k)) :=
            (Finset.mul_sum _ _ _).symm
      _ = β * (N : ℝ) ^ (-(η : ℝ)) *
            ((∑ k ∈ Finset.range K, q ^ k) + (∑ k ∈ Finset.range K, q ^ (K - 1 - k))) := by
            rw [Finset.sum_add_distrib]
      _ = β * (N : ℝ) ^ (-(η : ℝ)) * (2 * (∑ k ∈ Finset.range K, q ^ k)) := by
            rw [hreflect]; ring
      _ ≤ β * (N : ℝ) ^ (-(η : ℝ)) * (2 * (1 - q)⁻¹) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hgeo (by norm_num)
            · exact mul_nonneg hβ.le hNpowpos.le
      _ = 2 * β * (N : ℝ) ^ (-(η : ℝ)) / (1 - q) := by ring

end Work.WilC4
