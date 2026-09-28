import Mathlib

/-!
# Dyadic layer cake for inverse powers

Let `s : Finset α`, `D : α → ℝ` with `L₀ ≤ D a ≤ Λ` for `a ∈ s`, `L₀ ≥ 1`, and suppose the
counting function is bounded by `#{a ∈ s : D a ≤ Δ} ≤ c Δ^k (log (2Δ))²` for all `Δ ≥ 1`.
Then, for `k ≤ R`,

`∑ a ∈ s, (D a)^{-R} ≤ 16 c 2^R L₀^{k-R} (log (2Λ) + 1)³` (the levels below `log₂ L₀` are
empty, which is what makes the bound sharp when `L₀` is large).

This is the standard dyadic decomposition: assign to `a` the level `⌈log₂ (D a)⌉`, so that
`2^{⌈log₂ D a⌉ - 1} ≤ D a ≤ 2^{⌈log₂ D a⌉}`, and sum the counting bound over the dyadic levels.
Since `k ≤ R` the geometric factor `2^{j(k-R)}` is at most `1`, so the sum over levels costs only
a single `(log)³` factor.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

open Finset

theorem finset_sum_rpow_neg_le {α : Type*} (s : Finset α) (D : α → ℝ) (L₀ Λ : ℝ) (c : ℝ)
    (k R : ℕ) (hk : k ≤ R) (hL₀ : 1 ≤ L₀) (hΛ : 1 ≤ Λ)
    (hD₀ : ∀ a ∈ s, L₀ ≤ D a) (hDΛ : ∀ a ∈ s, D a ≤ Λ) (hc : 0 ≤ c)
    (hcount : ∀ Δ : ℝ, 1 ≤ Δ →
      ((s.filter (fun a => D a ≤ Δ)).card : ℝ) ≤ c * Δ ^ k * Real.log (2 * Δ) ^ 2) :
    (∑ a ∈ s, (D a) ^ (-(R : ℝ)))
      ≤ 16 * c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * (Real.log (2 * Λ) + 1) ^ 3 := by
  classical
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set la : α → ℕ := fun a => ⌈Real.logb 2 (D a)⌉₊ with hladef
  have hDpos : ∀ a ∈ s, 0 < D a :=
    fun a ha => lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hL₀) (hD₀ a ha)
  have hD1 : ∀ a ∈ s, 1 ≤ D a := fun a ha => le_trans hL₀ (hD₀ a ha)
  -- (A) `D a ≤ 2 ^ la a`
  have hA : ∀ a ∈ s, D a ≤ (2 : ℝ) ^ (la a) := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow (b := 2) (by norm_num) (hDpos a ha)]
    exact Nat.le_ceil _
  -- (B) `2 ^ (la a - 1) ≤ D a`
  have hB : ∀ a ∈ s, (2 : ℝ) ^ (la a - 1) ≤ D a := by
    intro a ha
    have hx : 0 < D a := hDpos a ha
    rcases Nat.eq_zero_or_pos (la a) with h0 | hpos
    · rw [h0]
      have hz : (2 : ℝ) ^ ((0 : ℕ) - 1) = 1 := by norm_num
      rw [hz]
      exact hD1 a ha
    · have hlt : ((la a - 1 : ℕ) : ℝ) < Real.logb 2 (D a) := by
        by_contra hcon
        push Not at hcon
        have h2 : la a ≤ la a - 1 := (Nat.ceil_le).mpr hcon
        omega
      rw [← Real.rpow_natCast, ← Real.le_logb_iff_rpow_le (b := 2) (by norm_num) hx]
      exact le_of_lt hlt
  -- per-term bound
  have hterm : ∀ a ∈ s, (D a) ^ (-(R : ℝ)) ≤ 2 ^ R * ((2 : ℝ) ^ (la a * R))⁻¹ := by
    intro a ha
    have hx : 0 < D a := hDpos a ha
    rcases Nat.eq_zero_or_pos (la a) with h0 | hpos
    · have hDeq : D a = 1 := le_antisymm (by simpa [h0] using hA a ha) (hD1 a ha)
      rw [hDeq, Real.one_rpow, h0, Nat.zero_mul, pow_zero, inv_one, mul_one]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    · have h1 : ((2 : ℝ) ^ (la a - 1)) ^ R ≤ (D a) ^ R :=
        pow_le_pow_left₀ (by positivity) (hB a ha) R
      have h2 : ((D a) ^ R)⁻¹ ≤ (((2 : ℝ) ^ (la a - 1)) ^ R)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by positivity)).mpr h1
      have h3 : (((2 : ℝ) ^ (la a - 1)) ^ R)⁻¹ = 2 ^ R * ((2 : ℝ) ^ (la a * R))⁻¹ := by
        have hla : la a * R = (la a - 1) * R + R := by
          have h1 : la a = (la a - 1) + 1 := by omega
          nth_rewrite 1 [h1]
          ring
        rw [← pow_mul, hla, pow_add, mul_inv_rev, ← mul_assoc,
          mul_inv_cancel₀ (by positivity), one_mul]
      rw [Real.rpow_neg (le_of_lt hx), Real.rpow_natCast]
      exact le_trans h2 (le_of_eq h3)
  have hsum1 : (∑ a ∈ s, (D a) ^ (-(R : ℝ))) ≤ 2 ^ R * ∑ a ∈ s, ((2 : ℝ) ^ (la a * R))⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hterm a ha
  set K : ℕ := ⌈Real.logb 2 Λ⌉₊ with hKdef
  set jmin : ℕ := ⌈Real.logb 2 L₀⌉₊ with hjmin
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le zero_lt_one hL₀
  have hlap : ∀ i ∈ s, la i ∈ Finset.range (K + 1) := by
    intro a ha
    rw [Finset.mem_range]
    have h1 : Real.logb 2 (D a) ≤ Real.logb 2 Λ :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (hDpos a ha) (hDΛ a ha)
    have h2 : la a ≤ ⌈Real.logb 2 Λ⌉₊ := Nat.ceil_le.mpr (le_trans h1 (Nat.le_ceil _))
    have h3 : la a ≤ K := h2
    omega
  -- fibre identity
  have hfib : (∑ a ∈ s, ((2 : ℝ) ^ (la a * R))⁻¹)
      = ∑ j ∈ Finset.range (K + 1),
          ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to hlap (fun a => ((2 : ℝ) ^ (la a * R))⁻¹)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_congr rfl (fun a ha => by
          rw [show la a = j from (Finset.mem_filter.mp ha).2]),
        Finset.sum_const, nsmul_eq_mul]
  -- the fibre cardinality bound
  have hfiber_card : ∀ j, ((s.filter (fun a => la a = j)).card : ℝ)
      ≤ c * (2 : ℝ) ^ (j * k) * ((j : ℝ) + 1) ^ 2 := by
    intro j
    have hsub : s.filter (fun a => la a = j) ⊆ s.filter (fun a => D a ≤ (2 : ℝ) ^ j) := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      rw [Finset.mem_filter]
      exact ⟨ha'.1, by rw [← ha'.2]; exact hA a ha'.1⟩
    have hcard : (s.filter (fun a => la a = j)).card
        ≤ (s.filter (fun a => D a ≤ (2 : ℝ) ^ j)).card := Finset.card_le_card hsub
    have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hc1 := hcount ((2 : ℝ) ^ j) h2j
    have hlog : Real.log (2 * (2 : ℝ) ^ j) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by
      have h2j' : (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
      rw [h2j', Real.log_pow]
      push_cast
      have hlog2le : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hlog2nn : (0 : ℝ) ≤ Real.log 2 := le_of_lt hlog2pos
      have hsq : (Real.log 2) ^ 2 ≤ 1 := by nlinarith
      calc (((j : ℝ) + 1) * Real.log 2) ^ 2
          = ((j : ℝ) + 1) ^ 2 * (Real.log 2) ^ 2 := by ring
        _ ≤ ((j : ℝ) + 1) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = ((j : ℝ) + 1) ^ 2 := by ring
    calc ((s.filter (fun a => la a = j)).card : ℝ)
        ≤ ((s.filter (fun a => D a ≤ (2 : ℝ) ^ j)).card : ℝ) := by exact_mod_cast hcard
      _ ≤ c * ((2 : ℝ) ^ j) ^ k * Real.log (2 * (2 : ℝ) ^ j) ^ 2 := hc1
      _ = c * (2 : ℝ) ^ (j * k) * Real.log (2 * (2 : ℝ) ^ j) ^ 2 := by rw [← pow_mul]
      _ ≤ c * (2 : ℝ) ^ (j * k) * ((j : ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  -- levels below `jmin` carry no point
  have hzero : ∀ j < jmin, (s.filter (fun a => la a = j)).card = 0 := by
    intro j hj
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha hla
    have h1 : L₀ ≤ (2 : ℝ) ^ j := by
      rw [← hla]
      exact le_trans (hD₀ a ha) (hA a ha)
    have h1' : L₀ ≤ (2 : ℝ) ^ ((j : ℕ) : ℝ) := by rwa [← Real.rpow_natCast] at h1
    have h2 : Real.logb 2 L₀ ≤ (j : ℝ) :=
      (Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hL₀pos).mpr h1'
    have h3 : jmin ≤ j := Nat.ceil_le.mpr h2
    omega
  have hL0_le : L₀ ≤ (2 : ℝ) ^ jmin := by
    have h := (Real.logb_le_iff_le_rpow (b := 2) (by norm_num) hL₀pos).mp
      (Nat.le_ceil (Real.logb 2 L₀))
    rwa [Real.rpow_natCast] at h
  -- the sum over the dyadic levels
  have hstep2 : (∑ a ∈ s, ((2 : ℝ) ^ (la a * R))⁻¹)
      ≤ c * ((L₀ ^ (R - k))⁻¹) * ((K : ℝ) + 1) ^ 3 := by
    rw [hfib]
    have hsplit : (∑ j ∈ Finset.range (K + 1),
          ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹)
        = ∑ j ∈ (Finset.range (K + 1)).filter (fun j => jmin ≤ j),
            ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹ := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (K + 1)) (fun j => jmin ≤ j)]
      have hz : (∑ j ∈ (Finset.range (K + 1)).filter (fun j => ¬ (jmin ≤ j)),
            ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_filter] at hj
        push Not at hj
        rw [hzero j hj.2, Nat.cast_zero, zero_mul]
      rw [hz, add_zero]
    rw [hsplit]
    have h1 : ∀ j ∈ (Finset.range (K + 1)).filter (fun j => jmin ≤ j),
        ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹
          ≤ c * ((L₀ ^ (R - k))⁻¹) * ((j : ℝ) + 1) ^ 2 := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjK, hjj⟩ := hj
      have hjk : (2 : ℝ) ^ (j * k) * ((2 : ℝ) ^ (j * R))⁻¹ = ((2 : ℝ) ^ (j * (R - k)))⁻¹ := by
        have hpow : (2 : ℝ) ^ (j * R) = (2 : ℝ) ^ (j * k) * (2 : ℝ) ^ (j * (R - k)) := by
          have hsum : j * R = j * k + j * (R - k) := by
            have h : R - k + k = R := Nat.sub_add_cancel hk
            calc j * R = j * (R - k + k) := by rw [h]
              _ = j * (R - k) + j * k := by rw [Nat.mul_add]
              _ = j * k + j * (R - k) := by ring
          rw [hsum, pow_add]
        rw [hpow]
        field_simp
      have hinv : ((2 : ℝ) ^ (j * (R - k)))⁻¹ ≤ ((L₀ ^ (R - k))⁻¹) := by
        have h1 : L₀ ^ (R - k) ≤ (2 : ℝ) ^ (j * (R - k)) := by
          calc L₀ ^ (R - k) ≤ ((2 : ℝ) ^ jmin) ^ (R - k) :=
                pow_le_pow_left₀ hL₀pos.le hL0_le _
            _ ≤ ((2 : ℝ) ^ j) ^ (R - k) := by
                apply pow_le_pow_left₀ (by positivity)
                rw [← Real.rpow_natCast, ← Real.rpow_natCast]
                exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
                  (by exact_mod_cast hjj)
            _ = (2 : ℝ) ^ (j * (R - k)) := by rw [pow_mul]
        exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr h1
      calc ((s.filter (fun a => la a = j)).card : ℝ) * ((2 : ℝ) ^ (j * R))⁻¹
          ≤ c * (2 : ℝ) ^ (j * k) * ((j : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (j * R))⁻¹ :=
            mul_le_mul_of_nonneg_right (hfiber_card j) (by positivity)
        _ = c * ((j : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (j * k) * ((2 : ℝ) ^ (j * R))⁻¹) := by ring
        _ = c * ((j : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ (j * (R - k)))⁻¹ := by rw [hjk]
        _ ≤ c * ((j : ℝ) + 1) ^ 2 * ((L₀ ^ (R - k))⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = c * ((L₀ ^ (R - k))⁻¹) * ((j : ℝ) + 1) ^ 2 := by ring
    have h3 : (∑ j ∈ (Finset.range (K + 1)).filter (fun j => jmin ≤ j),
          c * ((L₀ ^ (R - k))⁻¹) * ((j : ℝ) + 1) ^ 2)
        ≤ c * ((L₀ ^ (R - k))⁻¹) * ((K : ℝ) + 1) ^ 3 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (∑ j ∈ (Finset.range (K + 1)).filter (fun j => jmin ≤ j), ((j : ℝ) + 1) ^ 2)
          ≤ ∑ j ∈ (Finset.range (K + 1)).filter (fun j => jmin ≤ j), ((K : ℝ) + 1) ^ 2 := by
            refine Finset.sum_le_sum fun j hj => ?_
            rw [Finset.mem_filter] at hj
            have hj' : j ≤ K := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj.1
            have : (j : ℝ) + 1 ≤ (K : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hj' 1
            exact pow_le_pow_left₀ (by positivity) this 2
        _ = ((K : ℝ) + 1) ^ 2 * (((Finset.range (K + 1)).filter (fun j => jmin ≤ j)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
        _ ≤ ((K : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : (((Finset.range (K + 1)).filter (fun j => jmin ≤ j)).card : ℝ)
                ≤ ((Finset.range (K + 1)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
            simpa [Finset.card_range] using this
        _ = ((K : ℝ) + 1) ^ 3 := by ring
    exact le_trans (le_trans (Finset.sum_le_sum h1) (Finset.sum_le_sum (fun j hj => le_refl _))) h3
  -- comparison of `K` with `log (2Λ)`
  have hKbound : ((K : ℝ) + 1) ^ 3 ≤ 8 * (Real.log (2 * Λ) + 1) ^ 3 := by
    have hK1 : ((K : ℝ) + 1) ≤ 2 * (Real.log (2 * Λ) + 1) := by
      have h1 : (K : ℝ) ≤ Real.logb 2 Λ + 1 := by
        have h0 : (0 : ℝ) ≤ Real.logb 2 Λ := Real.logb_nonneg (b := 2) (by norm_num) hΛ
        have hc1 := Nat.ceil_lt_add_one h0
        rw [hKdef]
        linarith
      have h2 : Real.logb 2 Λ ≤ 2 * Real.log (2 * Λ) := by
        have hlogL : (0 : ℝ) ≤ Real.log Λ := Real.log_nonneg hΛ
        have hlog2L : (0 : ℝ) ≤ Real.log (2 * Λ) := Real.log_nonneg (by linarith)
        have hle : Real.log Λ ≤ Real.log (2 * Λ) :=
          Real.log_le_log (by linarith) (by linarith)
        have hinv : 1 / Real.log 2 ≤ 2 := by
          rw [div_le_iff₀ hlog2pos]
          linarith
        have hinvnn : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
        rw [Real.logb]
        calc Real.log Λ / Real.log 2 = Real.log Λ * (1 / Real.log 2) := by ring
          _ ≤ Real.log (2 * Λ) * 2 := mul_le_mul hle hinv hinvnn hlog2L
          _ = 2 * Real.log (2 * Λ) := by ring
      linarith
    calc ((K : ℝ) + 1) ^ 3 ≤ (2 * (Real.log (2 * Λ) + 1)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hK1 3
      _ = 8 * (Real.log (2 * Λ) + 1) ^ 3 := by ring
  calc (∑ a ∈ s, (D a) ^ (-(R : ℝ)))
      ≤ 2 ^ R * ∑ a ∈ s, ((2 : ℝ) ^ (la a * R))⁻¹ := hsum1
    _ ≤ 2 ^ R * (c * ((L₀ ^ (R - k))⁻¹) * ((K : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * ((K : ℝ) + 1) ^ 3 := by ring
    _ ≤ c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * (8 * (Real.log (2 * Λ) + 1) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hKbound
        positivity
    _ = 8 * c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * (Real.log (2 * Λ) + 1) ^ 3 := by ring
    _ ≤ 16 * c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * (Real.log (2 * Λ) + 1) ^ 3 := by
        have h1 : (0:ℝ) ≤ L₀ ^ (R - k) := pow_nonneg (by linarith) _
        have h2 : (0:ℝ) ≤ (L₀ ^ (R - k))⁻¹ := inv_nonneg.mpr h1
        have h3 : (0:ℝ) ≤ Real.log (2 * Λ) + 1 := by
          have := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 * Λ)
          linarith
        have h4 : (0:ℝ) ≤ (Real.log (2 * Λ) + 1) ^ 3 := pow_nonneg h3 3
        have h5 : (0:ℝ) ≤ 2 ^ R := by positivity
        have hnon : (0:ℝ) ≤ c * 2 ^ R * ((L₀ ^ (R - k))⁻¹) * (Real.log (2 * Λ) + 1) ^ 3 :=
          mul_nonneg (mul_nonneg (mul_nonneg hc h5) h2) h4
        nlinarith [hnon]

end Work.HP.Sig2
