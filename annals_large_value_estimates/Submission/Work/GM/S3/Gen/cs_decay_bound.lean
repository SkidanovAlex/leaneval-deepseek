import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.hhat_decay
import Submission.Work.GM.S3.Iterm_majorant
import Submission.Work.GM.S2.hhat_sum_tail
import Submission.Work.GM.S3.Gen.csLHS_le_majorant

namespace Work.GM.S3.Gen

open scoped BigOperators

noncomputable section


/-- `|t - s| ≤ T` for `t,s ∈ [0,T]`. -/
lemma abs_sub_le_of_mem_Icc {T t s : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (hs : s ∈ Set.Icc (0:ℝ) T) :
    |t - s| ≤ T := by
  rw [abs_sub_le_iff]
  exact ⟨by linarith [ht.2, hs.1], by linarith [hs.2, ht.1]⟩

/-- The per-frequency bound on `ĥ`: with `t,s ∈ [0,T]` and `m ≠ 0`,
`‖ĥ_{t-s}(mN)‖ ≤ min C₀ (C₄ ((1+T)/N)⁴/|m|⁴)`. -/
lemma norm_hhat_le_min {N : ℕ} (hN : 1 ≤ N) {C₀ C₄ : ℝ} (hC₀ : 0 ≤ C₀) (hC₄ : 0 ≤ C₄)
    (h0 : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ C₀)
    (h4 : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ C₄ * (1 + |t|)^4 / |ξ|^4)
    {W : Finset ℝ} (hW : ∀ t ∈ W, t ∈ Set.Icc (0:ℝ) (Submission.LargeValues.M N))
    {t s : ℝ} (ht : t ∈ W) (hs : s ∈ W) {m : ℤ} (hm : m ≠ 0) :
    ‖Submission.GM.hhat (t - s) ((m:ℝ) * N)‖ ≤
      min C₀ (C₄ * ((1 + Submission.LargeValues.M N)/(N:ℝ))^4 / |((m:ℝ))|^4) := by
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hm0 : ((m:ℝ)) ≠ 0 := by exact_mod_cast hm
  have hξ : ((m:ℝ) * (N:ℝ)) ≠ 0 := mul_ne_zero hm0 (ne_of_gt hN0)
  refine le_min (h0 _ _ hξ) ?_
  have hdec := h4 (t - s) ((m:ℝ) * (N:ℝ)) hξ
  have hts := abs_sub_le_of_mem_Icc (hW t ht) (hW s hs)
  have hT0 : (0:ℝ) ≤ Submission.LargeValues.M N := le_of_lt (Submission.LargeValues.M_pos hN)
  have habsξ : |((m:ℝ) * (N:ℝ))| = |(m:ℝ)| * (N:ℝ) := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hN0)]
  have hpow : (1 + |t - s|)^4 ≤ (1 + Submission.LargeValues.M N)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hle : C₄ * (1 + |t - s|)^4 ≤ C₄ * (1 + Submission.LargeValues.M N)^4 :=
    mul_le_mul_of_nonneg_left hpow hC₄
  calc ‖Submission.GM.hhat (t - s) ((m:ℝ) * (N:ℝ))‖
      ≤ C₄ * (1 + |t - s|)^4 / |((m:ℝ) * (N:ℝ))|^4 := hdec
    _ = C₄ * (1 + |t - s|)^4 / (|(m:ℝ)|^4 * (N:ℝ)^4) := by rw [habsξ, mul_pow]
    _ ≤ C₄ * (1 + Submission.LargeValues.M N)^4 / (|(m:ℝ)|^4 * (N:ℝ)^4) :=
        div_le_div_of_nonneg_right hle (by positivity)
    _ = C₄ * ((1 + Submission.LargeValues.M N)/(N:ℝ))^4 / |(m:ℝ)|^4 := by
        rw [div_pow]
        field_simp

/-- **The key one-dimensional sum.**  For `A,B ≥ 0` and `ρ ≥ 1`,
`Σ_{m ∈ ℤ, |m| ≤ K} min (A) (B ρ⁴/|m|⁴) ≤ C (A+B) ρ`, uniformly in `K`.

This is the point where the two halves of the decay estimate of `ĥ` are combined: the terms
`|m| ≤ ρ` (where the trivial bound `‖ĥ‖ ≤ C₀` applies, there being `≲ ρ` of them) and the terms
`|m| > ρ` (where the `|ξ|^{-4}` decay applies and the ℤ p-series tail
`Work.GM.S2.tsum_int_guard_inv_pow_le` is `≲ ρ^{-3}`). -/
theorem cs_key_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B ρ : ℝ) (K : ℤ), 0 ≤ A → 0 ≤ B → 1 ≤ ρ →
      (∑ m ∈ Finset.Icc (-K) K, min A (B * ρ ^ 4 / |((m : ℝ))| ^ 4)) ≤ C * (A + B) * ρ := by
  obtain ⟨Cp, hCppos, hCp⟩ := Work.GM.S2.tsum_int_guard_inv_pow_le
  refine ⟨5 + Cp, by positivity, ?_⟩
  intro A B ρ K hA hB hρ1
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
  have hρnn : 0 ≤ ρ := le_of_lt hρ0
  set c : ℤ := (Nat.ceil ρ : ℤ) with hcdef
  have hc0 : (0:ℤ) ≤ c := by
    rw [hcdef]; positivity
  have hρc : ρ ≤ (c : ℝ) := by
    rw [hcdef]; push_cast; exact Nat.le_ceil ρ
  -- the guard sum over ℤ
  have hsumm_guard : Summable (fun m : ℤ =>
      (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0)) :=
    Work.GM.S2.summable_int_guard_abs_pow_inv (j := 4) (by norm_num) (fun m : ℤ => ρ < |((m:ℝ))|)
  -- Part 1: |m| ≤ ρ
  have hsub : (Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ) ⊆ Finset.Icc (-c) c := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_Icc]
    have h2 : |((m:ℝ))| ≤ (c:ℝ) := le_trans hm.2 hρc
    rw [abs_le] at h2
    exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
  have hcard : ((Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ)).card
      ≤ 2 * Nat.ceil ρ + 1 := by
    refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
    rw [Int.card_Icc]
    have hz : c + 1 - (-c) = ((2 * Nat.ceil ρ + 1 : ℕ) : ℤ) := by
      rw [hcdef]; push_cast; ring
    rw [hz]
    have hpos : (0:ℤ) ≤ ((2 * Nat.ceil ρ + 1 : ℕ) : ℤ) := by positivity
    have := Int.toNat_of_nonneg hpos
    exact_mod_cast this
  have h5 : ((2 * Nat.ceil ρ + 1 : ℕ) : ℝ) ≤ 5 * ρ := by
    have hcl : ((Nat.ceil ρ : ℕ) : ℝ) < ρ + 1 := Nat.ceil_lt_add_one hρnn
    push_cast
    linarith
  have hP1 : (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ),
        min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4)) ≤ 5 * A * ρ := by
    calc (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ),
          min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4))
        ≤ ∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ), A :=
          Finset.sum_le_sum (fun m _ => min_le_left _ _)
      _ = (((Finset.Icc (-K) K).filter (fun m : ℤ => |((m:ℝ))| ≤ ρ)).card : ℝ) * A := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * Nat.ceil ρ + 1 : ℕ) : ℝ) * A :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hA
      _ ≤ (5 * ρ) * A := mul_le_mul_of_nonneg_right h5 hA
      _ = 5 * A * ρ := by ring
  -- Part 2: |m| > ρ
  have hP2 : (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
        min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4)) ≤ (Cp * B) * ρ := by
    have hpt : (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
          min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4))
        ≤ B * ρ ^ 4 * ∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
            (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun m _ => ?_)
      calc min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4) ≤ B * ρ ^ 4 / |((m:ℝ))| ^ 4 := min_le_right _ _
        _ = B * ρ ^ 4 * (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ := by rw [div_eq_mul_inv]
    have hguard : (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
            (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹)
        = ∑ m ∈ Finset.Icc (-K) K, (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases h : ρ < |((m:ℝ))|
      · rw [if_pos (not_le.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (not_le.mp hh)), if_neg h]
    have htsum : (∑ m ∈ Finset.Icc (-K) K,
            (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0))
        ≤ ∑' m : ℤ, (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0) :=
      hsumm_guard.sum_le_tsum (Finset.Icc (-K) K) (fun m _ => by
        by_cases h : ρ < |((m:ℝ))|
        · rw [if_pos h]; positivity
        · rw [if_neg h])
    have hrpow : ρ ^ 4 * ρ ^ ((1:ℝ) - 4) = ρ := by
      have h3 : ρ ^ ((1:ℝ) - 4) = (ρ ^ 3)⁻¹ := by
        rw [show (1:ℝ) - 4 = -(3:ℝ) by norm_num, Real.rpow_neg hρnn]
        congr 1
        exact Real.rpow_natCast ρ 3
      rw [h3]
      calc ρ ^ 4 * (ρ ^ 3)⁻¹ = (ρ * ρ ^ 3) * (ρ ^ 3)⁻¹ := by rw [show ρ ^ 4 = ρ * ρ ^ 3 by ring]
        _ = ρ * (ρ ^ 3 * (ρ ^ 3)⁻¹) := by ring
        _ = ρ * 1 := by rw [mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hρ0))]
        _ = ρ := by ring
    calc (∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
          min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4))
        ≤ B * ρ ^ 4 * ∑ m ∈ (Finset.Icc (-K) K).filter (fun m : ℤ => ¬ (|((m:ℝ))| ≤ ρ)),
            (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ := hpt
      _ = B * ρ ^ 4 * ∑ m ∈ Finset.Icc (-K) K,
            (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0) := by rw [hguard]
      _ ≤ B * ρ ^ 4 * ∑' m : ℤ,
            (if ρ < |((m:ℝ))| then (((|((m:ℝ))| : ℝ)) ^ 4)⁻¹ else 0) :=
          mul_le_mul_of_nonneg_left htsum (by positivity)
      _ ≤ B * ρ ^ 4 * (Cp * ρ ^ ((1:ℝ) - 4)) :=
          mul_le_mul_of_nonneg_left (hCp 4 ρ (by norm_num) hρ0) (by positivity)
      _ = (Cp * B) * ρ := by rw [show B * ρ ^ 4 * (Cp * ρ ^ ((1:ℝ) - 4))
            = B * Cp * (ρ ^ 4 * ρ ^ ((1:ℝ) - 4)) by ring, hrpow]; ring
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.Icc (-K) K)
        (p := fun m : ℤ => |((m:ℝ))| ≤ ρ) (f := fun m => min A (B * ρ ^ 4 / |((m:ℝ))| ^ 4))]
  exact (add_le_add hP1 hP2).trans (by
    have h1 : 0 ≤ A * ρ := mul_nonneg hA hρnn
    have h2 : 0 ≤ B * ρ := mul_nonneg hB hρnn
    nlinarith [h1, h2, hCppos])

/-- **Decay bound.** There is an absolute constant `C` with
`csLHS N δ W ≤ C |W|³ (M N)³ (1+log N)³ (1+δ)³` for every `N ≥ 1`, `δ > 0` and every
`W ⊆ [0, M N]` (no separation hypothesis is needed). -/
theorem cs_decay_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → 1 ≤ N →
      ∀ (W : Finset ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Work.GM.S3.Gen.csLHS N δ W ≤
        C * (W.card : ℝ) ^ 3 * (Submission.LargeValues.M N) ^ 3 *
          (1 + Real.log (N : ℝ)) ^ 3 * (1 + δ) ^ 3 := by
  obtain ⟨C₀, hC₀pos, h₀⟩ := Work.GM.S3.hhat_decay 0
  obtain ⟨C₄, hC₄pos, h₄⟩ := Work.GM.S3.hhat_decay 4
  obtain ⟨Cs, hCspos, hCs⟩ := cs_key_sum
  have h₀' : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ C₀ := by
    intro t ξ hξ
    simpa using h₀ t ξ hξ
  refine ⟨8 * Cs^3 * (C₀ + C₄)^3, by positivity, ?_⟩
  intro N δ hδ hN W hW
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hT1 : 1 ≤ Submission.LargeValues.M N := Submission.LargeValues.M_ge_one hN
  have hT0 : 0 < Submission.LargeValues.M N := Submission.LargeValues.M_pos hN
  -- N ≤ T
  have hNT : (N:ℝ) ≤ Submission.LargeValues.M N := by
    rw [Submission.LargeValues.M]
    calc (N:ℝ) = (N:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (N:ℝ)^(6/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  -- abbreviations
  set ρ : ℝ := (1 + Submission.LargeValues.M N) / (N:ℝ) with hρ
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hN0]
    linarith
  have hρnn : 0 ≤ ρ := le_trans (by norm_num) hρ1
  have hρ2 : ρ ≤ 2 * (N:ℝ)^(1/5:ℝ) := by
    have hTN : Submission.LargeValues.M N / (N:ℝ) = (N:ℝ)^(1/5:ℝ) := by
      have h := Real.rpow_sub hN0 (6/5:ℝ) 1
      rw [Real.rpow_one] at h
      rw [Submission.LargeValues.M, ← h]
      norm_num
    rw [hρ]
    calc (1 + Submission.LargeValues.M N) / (N:ℝ)
        ≤ (Submission.LargeValues.M N + Submission.LargeValues.M N) / (N:ℝ) :=
          div_le_div_of_nonneg_right (by linarith) (le_of_lt hN0)
      _ = 2 * (Submission.LargeValues.M N / (N:ℝ)) := by ring
      _ = 2 * (N:ℝ)^(1/5:ℝ) := by rw [hTN]
  set bnd : ℤ → ℝ := fun m => min C₀ (C₄ * ρ ^ 4 / |((m : ℝ))| ^ 4) with hbnd
  have hbndnn : ∀ m : ℤ, 0 ≤ bnd m := by
    intro m
    rw [hbnd]
    exact le_min (le_of_lt hC₀pos) (by positivity)
  -- the per-frequency bound
  have hhat_le : ∀ (t s : ℝ) (m : ℤ), t ∈ W → s ∈ W → m ≠ 0 →
      ‖Submission.GM.hhat (t - s) ((m:ℝ) * N)‖ ≤ bnd m := by
    intro t s m ht hs hm
    rw [hbnd, hρ]
    exact norm_hhat_le_min hN (le_of_lt hC₀pos) (le_of_lt hC₄pos) h₀' h₄ hW ht hs hm
  have hIterm : ∀ (m : ℤ × ℤ × ℤ), m.1 ≠ 0 → m.2.1 ≠ 0 → m.2.2 ≠ 0 →
      ‖Submission.GM.Iterm N W m‖ ≤
        (N:ℝ)^3 * (W.card:ℝ)^3 * (bnd m.1 * bnd m.2.1 * bnd m.2.2) := by
    intro m h1 h2 h3
    refine Work.GM.S3.Iterm_majorant N W m (bnd m.1) (bnd m.2.1) (bnd m.2.2) ?_ ?_ ?_
    · intro t s ht hs
      exact hhat_le t s m.1 ht hs h1
    · intro t s ht hs
      exact hhat_le t s m.2.1 ht hs h2
    · intro t s ht hs
      exact hhat_le t s m.2.2 ht hs h3
  have hB := csLHS_le_majorant N δ W bnd hbndnn hIterm
  have hSsum : (∑ m ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋, bnd m) ≤ Cs * (C₀ + C₄) * ρ := by
    rw [hbnd, hρ]
    exact hCs C₀ C₄ ((1 + Submission.LargeValues.M N) / (N:ℝ)) ⌊Klev N δ⌋
      (le_of_lt hC₀pos) (le_of_lt hC₄pos) hρ1
  have hSnn : 0 ≤ (∑ m ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋, bnd m) :=
    Finset.sum_nonneg (fun m _ => hbndnn m)
  -- arithmetic helpers
  have h15 : ((N:ℝ)^(1/5:ℝ))^3 = (N:ℝ)^(3/5:ℝ) := by
    rw [← Real.rpow_natCast ((N:ℝ)^(1/5:ℝ)) 3, ← Real.rpow_mul (le_of_lt hN0)]
    norm_num
  have hT3 : (Submission.LargeValues.M N)^3 = (N:ℝ)^(18/5:ℝ) := by
    rw [Submission.LargeValues.M, ← Real.rpow_natCast ((N:ℝ)^(6/5:ℝ)) 3,
      ← Real.rpow_mul (le_of_lt hN0)]
    norm_num
  have h18 : (N:ℝ)^3 * (N:ℝ)^(3/5:ℝ) = (N:ℝ)^(18/5:ℝ) := by
    rw [← Real.rpow_natCast (N:ℝ) 3, ← Real.rpow_add hN0]
    norm_num
  have hstep1 : (Cs * (C₀+C₄) * (2 * (N:ℝ)^(1/5:ℝ)))^3
      = Cs^3 * (C₀+C₄)^3 * (8 * (N:ℝ)^(3/5:ℝ)) := by
    rw [mul_pow, mul_pow, mul_pow, h15]
    norm_num
  have harith : (N:ℝ)^3 * (Cs * (C₀+C₄) * (2 * (N:ℝ)^(1/5:ℝ)))^3
      = 8 * Cs^3 * (C₀+C₄)^3 * (Submission.LargeValues.M N)^3 := by
    rw [hstep1]
    calc (N:ℝ)^3 * (Cs^3 * (C₀+C₄)^3 * (8 * (N:ℝ)^(3/5:ℝ)))
        = 8 * Cs^3 * (C₀+C₄)^3 * ((N:ℝ)^3 * (N:ℝ)^(3/5:ℝ)) := by ring
      _ = 8 * Cs^3 * (C₀+C₄)^3 * (N:ℝ)^(18/5:ℝ) := by rw [h18]
      _ = 8 * Cs^3 * (C₀+C₄)^3 * (Submission.LargeValues.M N)^3 := by rw [hT3]
  calc csLHS N δ W
      ≤ (N:ℝ)^3 * (W.card:ℝ)^3 * (∑ m ∈ Finset.Icc (-⌊Klev N δ⌋) ⌊Klev N δ⌋, bnd m)^3 := hB
    _ ≤ (N:ℝ)^3 * (W.card:ℝ)^3 * (Cs * (C₀ + C₄) * ρ)^3 := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSnn hSsum 3) ?_
        positivity
    _ ≤ (N:ℝ)^3 * (W.card:ℝ)^3 * (Cs * (C₀ + C₄) * (2 * (N:ℝ)^(1/5:ℝ)))^3 := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 3) ?_
        · exact mul_le_mul_of_nonneg_left hρ2 (by positivity)
        · positivity
    _ = (W.card:ℝ)^3 * ((N:ℝ)^3 * (Cs * (C₀ + C₄) * (2 * (N:ℝ)^(1/5:ℝ)))^3) := by ring
    _ = (W.card:ℝ)^3 * (8 * Cs^3 * (C₀+C₄)^3 * (Submission.LargeValues.M N)^3) := by
        rw [harith]
    _ = 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 := by ring
    _ ≤ 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 *
          (1 + Real.log (N:ℝ))^3 * (1 + δ)^3 := by
        have hbase : 0 ≤ 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 := by
          positivity
        have hlog : 1 ≤ (1 + Real.log (N:ℝ))^3 := one_le_pow₀ (by linarith [Real.log_nonneg hN1])
        have hd : 1 ≤ (1 + δ)^3 := one_le_pow₀ (by linarith)
        calc 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3
            ≤ 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 *
                (1 + Real.log (N:ℝ))^3 := le_mul_of_one_le_right hbase hlog
          _ ≤ 8 * Cs^3 * (C₀+C₄)^3 * (W.card:ℝ)^3 * (Submission.LargeValues.M N)^3 *
                (1 + Real.log (N:ℝ))^3 * (1 + δ)^3 :=
              le_mul_of_one_le_right (by positivity) hd

end

end Work.GM.S3.Gen
