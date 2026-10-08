import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- Design pass 5 (`Submission/Work/_design_gw/Core5.lean`): the closing arithmetic of §3,
`Work.CORE3.Case1bArithProp`, pure.

From `6k + Σ (n−3) bₙ = 0`, `bₙ = 0` for `n ≥ 5`, `k = 3`, `b₄ = 12`, `b₂ = 18`, `b₃ = 0` and
`8 ∣ b₁`: the sum gives `12 = 3b₀ + 2b₁`, so `b₁ ≤ 6`, and `8 ∣ b₁` forces `b₁ = 0` and
`b₀ = 4`; then `1 + Σ bₙ = 1 + 4 + 0 + 18 + 0 + 12 = 35`. -/
theorem Case1bArith : Case1bArithProp := by
  intro b k N hN hb5 hk hb4 hb2 hb3 h8 hrel
  -- The sum only sees the indices `0,1,2,3,4`: all terms with `n ≥ 5` vanish.
  have hsubset : Finset.range 5 ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range 5 →
      ((x : ℤ) - 3) * (b x : ℤ) = 0 := by
    intro x _ hxn
    simp only [Finset.mem_range, not_lt] at hxn
    rw [hb5 x (by omega)]
    ring
  have hsumeq : ∑ n ∈ Finset.range (N + 1), ((n : ℤ) - 3) * (b n : ℤ)
      = ∑ n ∈ Finset.range 5, ((n : ℤ) - 3) * (b n : ℤ) :=
    (Finset.sum_subset hsubset hzero).symm
  have h5val : ∑ n ∈ Finset.range 5, ((n : ℤ) - 3) * (b n : ℤ)
      = -3 * (b 0 : ℤ) - 2 * (b 1 : ℤ) - (b 2 : ℤ) + (b 4 : ℤ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    ring
  -- hence the linear relation `3 b₀ + 2 b₁ = 12` over `ℤ`.
  have hkey : 3 * (b 0 : ℤ) + 2 * (b 1 : ℤ) = 12 := by
    have h := hrel
    rw [hsumeq, h5val, hk, hb2, hb4] at h
    linarith
  have hb1zero : b 1 = 0 := by
    have hle : b 1 ≤ 6 := by
      have hb0 : (0 : ℤ) ≤ (b 0 : ℤ) := Nat.cast_nonneg _
      have : ((b 1 : ℤ)) ≤ 6 := by linarith
      exact_mod_cast this
    exact Nat.eq_zero_of_dvd_of_lt h8 (by omega)
  have hb0val : b 0 = 4 := by
    have h : (b 0 : ℤ) = 4 := by
      rw [hb1zero] at hkey
      linarith
    exact_mod_cast h
  -- and the sum of the `b n`.
  have hzeroB : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range 5 → b x = 0 := by
    intro x _ hxn
    simp only [Finset.mem_range, not_lt] at hxn
    exact hb5 x (by omega)
  have hsumeqB : ∑ n ∈ Finset.range (N + 1), b n = ∑ n ∈ Finset.range 5, b n :=
    (Finset.sum_subset hsubset hzeroB).symm
  have h5valB : ∑ n ∈ Finset.range 5, b n = b 0 + b 1 + b 2 + b 3 + b 4 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  refine ⟨hb1zero, hb0val, ?_⟩
  rw [hsumeqB, h5valB, hb0val, hb1zero, hb2, hb3, hb4]

end Work.CORE3

open Work.GW2

/-- The same lemma at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Work.CORE3.Case1bArith` (the skeleton's namespace layout) and as
`Work.CORE3.Case1bArith`. -/
theorem Case1bArith : Case1bArithProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bArith

end Work.CORE3
