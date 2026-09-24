import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.hhat_sum_tail

/-!
# The `ℕ`-indexed tail of `‖ĥ_t(m N)‖`

The decay hypothesis `hdec` (GM Lemma 4.3(2)) says `‖ĥ_t(ξ)‖ ≤ C_j (1+|t|)^j / |ξ|^j` for
every `j`.  Hence, for `N ≥ 1`, the series `Σ_k ‖ĥ_t((k+1)N)‖` converges, and its tail
beyond `⌊Y⌋`, namely `Σ_k ‖ĥ_t((k + ⌊Y⌋ + 1)N)‖`, is `≪ (1+|t|)^j / (N^j Y^{j-1})`.

The tail is compared with the `ℤ`-indexed tail `Σ_{|m| > Y} ‖ĥ_t(mN)‖` already estimated in
`hhat_sum_tail`; the comparison only needs the injectivity of `k ↦ k + ⌊Y⌋ + 1` together with
non-negativity (`tsum_comp_le_tsum_of_inj`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.GM.S2

/-- The shifted `p`-series `Σ_k (k+1)^{-j}` converges for `1 < j`. -/
lemma summable_nat_succ_pow_inv {j : ℕ} (hj : 1 < j) :
    Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ j)⁻¹) :=
  (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr hj)

theorem tail_nat_hhat
    (hdec : Work.GM.S2.DecHyp) (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ t : ℝ,
        Summable (fun k : ℕ => ‖Submission.GM.hhat t (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖)) ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
        (∑' k : ℕ, ‖Submission.GM.hhat t (((k + Nat.floor Y + 1 : ℕ) : ℝ) * (N : ℝ))‖)
          ≤ C * (1 + |t|) ^ j / ((N : ℝ) ^ j * Y ^ (j - 1))) := by
  obtain ⟨Cj, hCjpos, hCj⟩ := hdec j
  obtain ⟨C, hCpos, hCtail⟩ := hhat_sum_tail hdec j hj
  have h1j : 1 < j := by omega
  refine ⟨C, hCpos, ?_, ?_⟩
  · -- summability for every `t`
    intro N hN t
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ j := one_le_pow₀ hN1
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_nat_succ_pow_inv h1j).mul_left (Cj * (1 + |t|) ^ j))
    have hpows : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) ^ j := by positivity
    have hξ : (((k + 1 : ℕ) : ℝ) * (N : ℝ)) ≠ 0 := by positivity
    have hb := hCj t (((k + 1 : ℕ) : ℝ) * (N : ℝ)) hξ
    have habs : |(((k + 1 : ℕ) : ℝ) * (N : ℝ))| ^ j
        = (((k + 1 : ℕ) : ℝ) ^ j) * ((N : ℝ) ^ j) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)), mul_pow]
    rw [habs] at hb
    calc ‖Submission.GM.hhat t (((k + 1 : ℕ) : ℝ) * (N : ℝ))‖
        ≤ Cj * (1 + |t|) ^ j / ((((k + 1 : ℕ) : ℝ) ^ j) * ((N : ℝ) ^ j)) := hb
      _ ≤ Cj * (1 + |t|) ^ j / (((k + 1 : ℕ) : ℝ) ^ j) :=
          div_le_div_of_nonneg_left (by positivity) hpows (by nlinarith [hNpow, hpows])
      _ = Cj * (1 + |t|) ^ j * ((((k + 1 : ℕ) : ℝ) ^ j))⁻¹ := by rw [div_eq_mul_inv]
  · -- the tail bound
    intro N hN t Y ht hY
    have hYpos : (0 : ℝ) < Y := by linarith
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    set K : ℤ := (Nat.floor Y : ℤ) + 1 with hKdef
    -- the `ℤ`-indexed (truncated) tail, as a function of `m`
    have hGsum : Summable (fun m : ℤ =>
        (if Y < |(m : ℝ)| then ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ else 0)) := by
      have hbase : Summable (fun m : ℤ => (((|(m : ℝ)| : ℝ)) ^ j)⁻¹) := summable_int_abs_pow_inv hj
      have hD : (0 : ℝ) ≤ Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹ := by positivity
      refine Summable.of_nonneg_of_le ?_ ?_
        (hbase.mul_left (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹))
      · intro m
        by_cases h : Y < |(m : ℝ)| <;> simp [h]
      · intro m
        by_cases h : Y < |(m : ℝ)|
        · rw [if_pos h]
          have hm0 : (m : ℝ) ≠ 0 := by
            have hpos : (0 : ℝ) < |(m : ℝ)| := lt_of_lt_of_le hYpos (le_of_lt h)
            exact abs_pos.mp hpos
          have hξ : (m : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hm0 (by positivity)
          have hb := hCj t ((m : ℝ) * (N : ℝ)) hξ
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)), mul_pow,
            div_eq_mul_inv, mul_inv] at hb
          calc ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
              ≤ Cj * (1 + |t|) ^ j * ((((|(m : ℝ)| : ℝ)) ^ j)⁻¹ * ((N : ℝ) ^ j)⁻¹) := hb
            _ = (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * (((|(m : ℝ)| : ℝ)) ^ j)⁻¹ := by ring
        · rw [if_neg h]
          positivity
    have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + K) := by
      intro a b hab
      have h : (a : ℤ) = (b : ℤ) := add_right_cancel hab
      exact_mod_cast h
    have hle : (∑' k : ℕ, (fun m : ℤ =>
          (if Y < |(m : ℝ)| then ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ else 0)) ((k : ℤ) + K))
        ≤ ∑' m : ℤ, (fun m : ℤ =>
          (if Y < |(m : ℝ)| then ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ else 0)) m :=
      tsum_comp_le_tsum_of_inj hGsum (fun m => by by_cases h : Y < |(m : ℝ)| <;> simp [h]) hinj
    have hleft : (∑' k : ℕ, (fun m : ℤ =>
          (if Y < |(m : ℝ)| then ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ else 0)) ((k : ℤ) + K))
        = ∑' k : ℕ, ‖Submission.GM.hhat t (((k + Nat.floor Y + 1 : ℕ) : ℝ) * (N : ℝ))‖ := by
      refine tsum_congr (fun k => ?_)
      have hcast : ((((k : ℤ) + K : ℤ) : ℝ)) = ((k + Nat.floor Y + 1 : ℕ) : ℝ) := by
        rw [hKdef]; push_cast; ring
      have hxpos : (0 : ℝ) < ((k + Nat.floor Y + 1 : ℕ) : ℝ) := by positivity
      have hlt : Y < |((k + Nat.floor Y + 1 : ℕ) : ℝ)| := by
        rw [abs_of_pos hxpos]
        have h2 : Y < ((Nat.floor Y : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one Y
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hc : ((k + Nat.floor Y + 1 : ℕ) : ℝ) = (k : ℝ) + ((Nat.floor Y : ℕ) : ℝ) + 1 := by
          push_cast; ring
        rw [hc]; linarith
      beta_reduce
      rw [hcast, if_pos hlt]
    have hright : (∑' m : ℤ, (fun m : ℤ =>
          (if Y < |(m : ℝ)| then ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖ else 0)) m)
        = (∑' (m : {m : ℤ // Y < |(m : ℝ)|}), ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖) := by
      refine ((tsum_subtype (s := {m : ℤ | Y < |(m : ℝ)|})
        (f := fun m : ℤ => ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖)).trans ?_).symm
      refine tsum_congr (fun m => ?_)
      by_cases h : Y < |(m : ℝ)| <;> simp [h]
    rw [hleft, hright] at hle
    exact le_trans hle (hCtail N hN t Y hYpos)

end Work.GM.S2
