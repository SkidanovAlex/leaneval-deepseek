import Mathlib

/-!
# The dyadic sum bound

Fix `n ≥ 2`.  For every `Δ ≥ 1` and every finite set `A` of pairs `k = (k₁,k₂) ∈ ℕ × ℕ`
satisfying `2 ^ (k₁ + k₂) ≤ 8 (Δ + 1)` one has

`∑_{k ∈ A} 2 ^ (n (k₁ + k₂)) ≤ C Δ^n log (2 Δ)`

for a constant `C` depending only on `n`.

The key point is that although `A` may contain as many as `~(log Δ)²` points, the sum is
dominated by the largest dyadic level: on the level `k₁ + k₂ = s` the terms equal `(2^n)^s`,
and a bounded triangle `{(a,b) : a + b ≤ L}` of `ℕ × ℕ` has geometric-sum-type total
`≤ 2 (L + 1) (2^n)^L`.  Since `2 ^ L ≤ 8 (Δ + 1) ≤ 16 Δ` forces `L + 1 ≤ 5 log₂ (2 Δ)`,
the claim follows.
-/

set_option autoImplicit false

namespace Work.HP.FM3

open Finset

/-- The triangular region `{(a,b) ∈ ℕ × ℕ : a + b ≤ L}`. -/
def triRegion (L : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (L + 1)).sigma (fun a => Finset.range (L - a + 1))).map
    (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding

/-- Geometric-type bound: `∑_{b=0}^{m} q ^ b ≤ 2 q ^ m` whenever `2 ≤ q`. -/
lemma geo_sum_le (q : ℝ) (hq : 2 ≤ q) (m : ℕ) :
    ∑ b ∈ Finset.range (m + 1), q ^ b ≤ 2 * q ^ m := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    calc (∑ b ∈ Finset.range (m + 1), q ^ b) + q ^ (m + 1)
        ≤ 2 * q ^ m + q ^ (m + 1) := by linarith [ih]
      _ = q ^ m * (2 + q) := by ring
      _ ≤ q ^ m * (2 * q) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 m)
            linarith
      _ = 2 * q ^ (m + 1) := by rw [pow_succ]; ring

/-- Sum over the triangle `{a + b ≤ L}` is bounded by `2 (L+1) q^L`. -/
lemma triRegion_sum_le (q : ℝ) (hq : 2 ≤ q) (L : ℕ) :
    (∑ p ∈ triRegion L, q ^ (p.1 + p.2)) ≤ 2 * (L + 1) * q ^ L := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  rw [triRegion, Finset.sum_map, Finset.sum_sigma]
  simp only [Equiv.toEmbedding_apply, Equiv.sigmaEquivProd_apply]
  calc ∑ a ∈ Finset.range (L + 1), ∑ b ∈ Finset.range (L - a + 1), q ^ (a + b)
      ≤ ∑ a ∈ Finset.range (L + 1), 2 * q ^ L := by
        apply Finset.sum_le_sum
        intro a ha
        have haL : a ≤ L := by simpa using ha
        have h1 : ∑ b ∈ Finset.range (L - a + 1), q ^ (a + b)
            = q ^ a * ∑ b ∈ Finset.range (L - a + 1), q ^ b := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => by rw [pow_add])
        rw [h1]
        calc q ^ a * ∑ b ∈ Finset.range (L - a + 1), q ^ b
            ≤ q ^ a * (2 * q ^ (L - a)) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 a)
              exact geo_sum_le q hq (L - a)
          _ = 2 * q ^ L := by
              have hL : a + (L - a) = L := by omega
              have hpq : q ^ a * q ^ (L - a) = q ^ L := by rw [← pow_add, hL]
              calc q ^ a * (2 * q ^ (L - a)) = 2 * (q ^ a * q ^ (L - a)) := by ring
                _ = 2 * q ^ L := by rw [hpq]
    _ = 2 * (L + 1) * q ^ L := by
        rw [Finset.sum_const, Finset.card_range]
        simp only [nsmul_eq_mul]; push_cast; ring

/-- Main combinatorial step: the dyadic sum over a finite set of pairs is bounded by
`2 (L+1) 2^{nL}` whenever all sums `k₁ + k₂` are `≤ L`. -/
lemma dyadic_split (n L : ℕ) (hn : 1 ≤ n) (A : Finset (ℕ × ℕ))
    (hA : ∀ k ∈ A, k.1 + k.2 ≤ L) :
    (∑ k ∈ A, (2 : ℝ) ^ (n * (k.1 + k.2))) ≤ 2 * (L + 1) * (2 : ℝ) ^ (n * L) := by
  have hq2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hn
  have hsubset : A ⊆ triRegion L := by
    intro k hk
    rw [triRegion, Finset.mem_map]
    refine ⟨⟨k.1, k.2⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor <;> · simp only [Finset.mem_range]; have := hA k hk; omega
    · simp
  have hstep1 : (∑ k ∈ A, (2 : ℝ) ^ (n * (k.1 + k.2)))
      ≤ ∑ p ∈ triRegion L, (2 : ℝ) ^ (n * (p.1 + p.2)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => by positivity)
  have hstep2 : (∑ p ∈ triRegion L, (2 : ℝ) ^ (n * (p.1 + p.2)))
      ≤ 2 * (L + 1) * (2 : ℝ) ^ (n * L) := by
    have hcongr : (∑ p ∈ triRegion L, (2 : ℝ) ^ (n * (p.1 + p.2)))
        = ∑ p ∈ triRegion L, ((2 : ℝ) ^ n) ^ (p.1 + p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [pow_mul]
    rw [hcongr]
    calc ∑ p ∈ triRegion L, ((2 : ℝ) ^ n) ^ (p.1 + p.2)
        ≤ 2 * (L + 1) * ((2 : ℝ) ^ n) ^ L := triRegion_sum_le ((2 : ℝ) ^ n) hq2 L
      _ = 2 * (L + 1) * (2 : ℝ) ^ (n * L) := by rw [pow_mul]
  linarith [hstep1, hstep2]

/-- If `2 ^ L ≤ 8 (Δ + 1)` with `Δ ≥ 1` then `L + 1 ≤ 5 log₂ (2 Δ)`. -/
lemma dyadic_log_bound (Δ : ℝ) (hΔ : 1 ≤ Δ) (L : ℕ)
    (hL : (2 : ℝ) ^ L ≤ 8 * (Δ + 1)) :
    (L : ℝ) + 1 ≤ (5 / Real.log 2) * Real.log (2 * Δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL16 : (2 : ℝ) ^ L ≤ 16 * Δ := by nlinarith [hL, hΔ]
  have hlogL : (L : ℝ) * Real.log 2 ≤ Real.log (16 * Δ) := by
    have h1 : Real.log ((2 : ℝ) ^ L) ≤ Real.log (16 * Δ) :=
      Real.log_le_log (by positivity) hL16
    rwa [Real.log_pow] at h1
  have hlog16 : Real.log (16 * Δ) ≤ 4 * Real.log (2 * Δ) := by
    have hsplit : Real.log (16 * Δ) = Real.log (2 * Δ) + Real.log 8 := by
      rw [show (16 : ℝ) * Δ = (2 * Δ) * 8 by ring,
          Real.log_mul (by positivity : (2 : ℝ) * Δ ≠ 0) (by norm_num)]
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have hge : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
    rw [hsplit, h8]; linarith
  have hLlog : (L : ℝ) * Real.log 2 ≤ 4 * Real.log (2 * Δ) := le_trans hlogL hlog16
  have hDge : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
  have hLdiv : (L : ℝ) ≤ 4 * Real.log (2 * Δ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith [hLlog]
  have hratio : (1 : ℝ) ≤ Real.log (2 * Δ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith [hDge]
  calc (L : ℝ) + 1 ≤ 4 * Real.log (2 * Δ) / Real.log 2 + 1 := by linarith [hLdiv]
    _ ≤ 5 * (Real.log (2 * Δ) / Real.log 2) := by
        have hrw : (4 : ℝ) * Real.log (2 * Δ) / Real.log 2
            = 4 * (Real.log (2 * Δ) / Real.log 2) := by ring
        rw [hrw]; linarith [hratio]
    _ = (5 / Real.log 2) * Real.log (2 * Δ) := by ring

theorem dyadic_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Δ : ℝ) (A : Finset (ℕ × ℕ)), 1 ≤ Δ →
      (∀ k ∈ A, (2 : ℝ) ^ (k.1 + k.2) ≤ 8 * (Δ + 1)) →
      (∑ k ∈ A, (2 : ℝ) ^ (n * (k.1 + k.2))) ≤ C * Δ ^ n * Real.log (2 * Δ) := by
  refine ⟨10 * 16 ^ n / Real.log 2, ?_, ?_⟩
  · apply div_pos
    · positivity
    · exact Real.log_pos (by norm_num)
  · intro Δ A hΔ hA
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set M : ℝ := 8 * (Δ + 1) with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    set L : ℕ := Nat.floor (Real.logb 2 M) with hL
    have hlogb_nonneg : 0 ≤ Real.logb 2 M :=
      Real.logb_nonneg (by norm_num) (by rw [hM]; linarith)
    have hLle : (L : ℝ) ≤ Real.logb 2 M := by rw [hL]; exact Nat.floor_le hlogb_nonneg
    have hLlt : Real.logb 2 M < (L : ℝ) + 1 := by
      rw [hL]; exact Nat.lt_floor_add_one _
    have h2L : (2 : ℝ) ^ L ≤ M := by
      have hrw : (2 : ℝ) ^ ((L : ℝ)) ≤ (2 : ℝ) ^ (Real.logb 2 M) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hLle
      rwa [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) hMpos] at hrw
    have h2Lt : M < (2 : ℝ) ^ (L + 1) := by
      have hrw : (2 : ℝ) ^ (Real.logb 2 M) < (2 : ℝ) ^ ((L : ℝ) + 1) :=
        (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hLlt
      rw [Real.rpow_logb (by norm_num) (by norm_num) hMpos] at hrw
      have hEq : (2 : ℝ) ^ ((L : ℝ) + 1) = (2 : ℝ) ^ (L + 1) := by
        rw [show ((L : ℝ) + 1) = ((L + 1 : ℕ) : ℝ) from by push_cast; ring, Real.rpow_natCast]
      rwa [hEq] at hrw
    have hmem : ∀ k ∈ A, k.1 + k.2 ≤ L := by
      intro k hk
      have hk2 : (2 : ℝ) ^ (k.1 + k.2) ≤ M := by rw [hM]; exact hA k hk
      have hlt : (2 : ℝ) ^ (k.1 + k.2) < (2 : ℝ) ^ (L + 1) := lt_of_le_of_lt hk2 h2Lt
      have hltnat : (2 : ℕ) ^ (k.1 + k.2) < (2 : ℕ) ^ (L + 1) := by exact_mod_cast hlt
      have hlt' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hltnat
      omega
    have hmain := dyadic_split n L (by omega) A hmem
    have hpow : (2 : ℝ) ^ (n * L) ≤ M ^ n := by
      rw [Nat.mul_comm n L, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h2L n
    have hM16 : M ^ n ≤ (16 * Δ) ^ n := by
      apply pow_le_pow_left₀ (le_of_lt hMpos)
      rw [hM]; nlinarith [hΔ]
    have hlogb : (L : ℝ) + 1 ≤ (5 / Real.log 2) * Real.log (2 * Δ) :=
      dyadic_log_bound Δ hΔ L (by rw [hM] at h2L; exact h2L)
    have hKnonneg : (0 : ℝ) ≤ (5 / Real.log 2) * Real.log (2 * Δ) := by
      apply mul_nonneg
      · exact div_nonneg (by norm_num) (le_of_lt hlog2)
      · exact Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Δ)
    calc (∑ k ∈ A, (2 : ℝ) ^ (n * (k.1 + k.2)))
        ≤ 2 * (L + 1) * (2 : ℝ) ^ (n * L) := hmain
      _ ≤ 2 * (L + 1) * M ^ n := by
            apply mul_le_mul_of_nonneg_left hpow; positivity
      _ ≤ 2 * ((5 / Real.log 2) * Real.log (2 * Δ)) * (16 * Δ) ^ n := by
            have hprod : (L + 1) * M ^ n
                ≤ ((5 / Real.log 2) * Real.log (2 * Δ)) * (16 * Δ) ^ n :=
              mul_le_mul hlogb hM16 (by positivity) hKnonneg
            have h2 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
            rw [show (2 : ℝ) * (L + 1) * M ^ n = 2 * ((L + 1) * M ^ n) by ring,
                show (2 : ℝ) * ((5 / Real.log 2) * Real.log (2 * Δ)) * (16 * Δ) ^ n
                  = 2 * (((5 / Real.log 2) * Real.log (2 * Δ)) * (16 * Δ) ^ n) by ring]
            exact h2
      _ = (10 * 16 ^ n / Real.log 2) * Δ ^ n * Real.log (2 * Δ) := by
            rw [mul_pow]; ring

end Work.HP.FM3
