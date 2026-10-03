import Mathlib
import Submission.Work.KMTAreas.A7.Split

namespace Work.KMTPlan.A6

/-- **Lacunary floors have bounded index gaps.** If `a` is `Λ`-lacunary with `Λ > 1`, then two
indices whose floors are comparable up to a constant `c > 1` (in the sense that the smaller floor
sits above `x ≥ 1` and the larger floor is at most `c · x`) must be within `L = L(Λ, c)` of one
another.

The proof is the elementary observation that `a` grows at least like `Λ ^ k` (`k = n' - n`), while
the hypothesis forces `a n' < (c + 1/2) · a n`: indeed `⌊a n⌋ ≥ 2` (because `x ≥ 1` and
`x < ⌊a n⌋`), so `a n ≥ 2` and `a n' < ⌊a n'⌋ + 1 ≤ c x + 1 < c a n + 1 ≤ (c + 1/2) a n`.
Hence `Λ ^ (n' - n) < c + 1/2`, which bounds `n' - n` since `Λ > 1`. -/
theorem lacunaryFloorGap (Λ : NNReal) (hΛ : 1 < Λ) (c : ℝ) (hc : 1 < c) :
    ∃ L : ℕ, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (n n' : ℕ) (x : ℝ),
      n < n' → 1 ≤ x → x < (Nat.floor (a n) : ℝ) → (Nat.floor (a n') : ℝ) ≤ c * x →
      n' - n ≤ L := by
  have hΛR : (1:ℝ) < (Λ:ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0:ℝ) < (Λ:ℝ) := lt_trans zero_lt_one hΛR
  have hcpos : (0:ℝ) < c := lt_trans zero_lt_one hc
  -- choose `L` with `Λ ^ L ≥ c + 1/2`
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (c + 1/2 : ℝ) ≤ (Λ:ℝ)^L := by
    have h : Filter.Tendsto (fun n : ℕ => (Λ:ℝ)^n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hΛR
    have hev := h.eventually (Filter.eventually_ge_atTop (c + 1/2))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    exact ⟨N, hN N le_rfl⟩
  refine ⟨L, ?_⟩
  intro a ha n n' x hn hx1 hxfl hbound
  have hfloor_le : ∀ m, (Nat.floor (a m) : ℝ) ≤ (a m : ℝ) := by
    intro m
    have hh : (Nat.floor (a m) : NNReal) ≤ a m :=
      Nat.floor_le (show (0:NNReal) ≤ a m from bot_le)
    exact_mod_cast hh
  -- the lacunarity gives `Λ * a m < a (m+1)`
  have hmul : ∀ m, (Λ:ℝ) * (a m : ℝ) < (a (m+1) : ℝ) := by
    intro m
    have h := ha m
    have hane : a m ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      exact absurd h (not_lt.mpr (bot_le : (0:NNReal) ≤ Λ))
    have hh := (lt_div_iff₀ (pos_iff_ne_zero.mpr hane)).mp h
    exact_mod_cast hh
  -- hence `Λ ^ k * a m ≤ a (m + k)`
  have hpow : ∀ m k, (Λ:ℝ)^k * (a m : ℝ) ≤ (a (m+k) : ℝ) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have hrec := hmul (m+k)
      have hgoal : (a (m + Nat.succ k) : ℝ) = (a (m+k+1) : ℝ) := by
        congr 1
      rw [hgoal]
      calc (Λ:ℝ)^(Nat.succ k) * (a m : ℝ)
          = (Λ:ℝ) * ((Λ:ℝ)^k * (a m:ℝ)) := by rw [pow_succ]; ring
        _ ≤ (Λ:ℝ) * (a (m+k) : ℝ) := mul_le_mul_of_nonneg_left ih (le_of_lt hΛpos)
        _ ≤ (a (m+k+1) : ℝ) := le_of_lt hrec
  -- `⌊a n⌋ ≥ 2`, hence `a n ≥ 2`
  have han2 : 2 ≤ (a n : ℝ) := by
    have h1 : (1:ℝ) < (Nat.floor (a n) : ℝ) := lt_of_le_of_lt hx1 hxfl
    have h2 : (1:ℕ) < Nat.floor (a n) := by exact_mod_cast h1
    have h3 : 2 ≤ Nat.floor (a n) := by omega
    have h5 : (2:ℝ) ≤ (Nat.floor (a n) : ℝ) := by exact_mod_cast h3
    linarith [h5, hfloor_le n]
  have hkey : (Λ:ℝ)^(n'-n) * (a n : ℝ) < c * (a n : ℝ) + 1 := by
    have h1 : (Λ:ℝ)^(n'-n) * (a n : ℝ) ≤ (a (n + (n'-n)) : ℝ) := hpow n (n'-n)
    have h2 : n + (n'-n) = n' := Nat.add_sub_cancel' (le_of_lt hn)
    rw [h2] at h1
    have h3 : (a n' : ℝ) < (Nat.floor (a n') : ℝ) + 1 := Nat.lt_floor_add_one _
    have hxlt : x < (a n : ℝ) := lt_of_lt_of_le hxfl (hfloor_le n)
    have h5 : c * x < c * (a n : ℝ) := mul_lt_mul_of_pos_left hxlt hcpos
    linarith
  have hfin : (Λ:ℝ)^(n'-n) < c + 1/2 := by
    have hnonneg : (0:ℝ) ≤ (Λ:ℝ)^(n'-n) := pow_nonneg (le_of_lt hΛpos) _
    nlinarith [hkey, han2, hnonneg]
  by_contra hcon
  rw [not_le] at hcon
  have hle : L + 1 ≤ n' - n := by omega
  have hstep : (Λ:ℝ)^(L+1) ≤ (Λ:ℝ)^(n'-n) := pow_le_pow_right₀ (le_of_lt hΛR) hle
  have hLL : (c + 1/2 : ℝ) ≤ (Λ:ℝ)^(L+1) :=
    le_trans hL (pow_le_pow_right₀ (le_of_lt hΛR) (Nat.le_succ L))
  linarith

end Work.KMTPlan.A6
