import Submission.Work.NumberTheory.Chen.BTermCount.Basic

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The `B`-term: the sieve interface

The whole `B`-term bound rests on one analytic input: the sharp upper-bound (Rosser /
Jurkat–Richert) sieve for the ternary sequence `n ↦ n - 2`, `n ∈ B̄`, sieved by the odd primes
`< Y`.  This module isolates that input as a named hypothesis (`BTermSieveInput`) and proves
the *elementary* reduction which turns it into a bound for `bTermCount`.

The content of `BTermSieveInput C` is the statement

`#(survivorSet x M Y) ≤ C · x / (log x)^2` eventually,

where `survivorSet` is the set of `n ∈ B̄` with `n - 2` coprime to every odd prime `< Y`.
The sharp value of `C` for the linear sieve at sieve limit `Y ≈ x^{1/3}` and level `√x` is

`C = c̄ · (V(Y)·log Y) · F(3/2) ≈ 0.666 · 0.7413 · 2.375 ≈ 1.17` times `log x/log x`-factors,
i.e. roughly `3.5` once the factor `log x / log Y = 3` is taken into account (see
`notes/BTERM_COUNT_ANALYSIS.md`); the truth is around `1.9`.
-/

/-- **The `B`-term sieve input**: the survivors of the ternary sequence, sieved by `P(Y)`, are
at most `C · x / (log x)^2`. -/
def BTermSieveInput (C : ℝ) : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop,
    (survivorCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
      ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ 2

/-- **The sharp `B`-term sieve main term.**  The survivors of the ternary sequence, sieved by the
odd primes `< Y`, number at most `C · #B̄ · V(Y) · F(3/2)`, where `V(Y)` is the odd Mertens product
and `F(3/2) = 2e^γ/(3/2)` is the linear-sieve upper-bound constant at level `√x` and sieve limit
`Y`.  This is the *sharp* form of the missing analytic input (the Rosser/Jurkat–Richert
upper-bound sieve for `n ↦ n - 2` over `B̄`); its error term is a bilinear sum, so it needs the
Bombieri–Vinogradov mean value theorem for bilinear forms at level `√x` — see `MVTInput.lean` /
`BTernaryLevelOfDistribution` for the formulation actually used in this chapter, and
`notes/BTERM_COUNT_ANALYSIS.md` for the constants (sharp value `3.52 x/log²x` at
`M = chenSiftLimit x`). -/
def BTermSieveSharp (C : ℝ) : Prop :=
  ∀ᶠ x : ℕ in Filter.atTop,
    (survivorCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
      ≤ C * (bTripleCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        * VsieveOdd (Submission.chenWindowTop x)
        * (2 * Real.exp Real.eulerMascheroniConstant / (3/2))

theorem chenWindowTop_le (x : ℕ) (hx : (24:ℕ)^6 ≤ x) :
    (Submission.chenWindowTop x : ℝ) ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  have hx1 : (1:ℝ) < (x:ℝ) := by
    have h : (1:ℕ) < x := by
      have : (1:ℕ) < 24^6 := by norm_num
      omega
    exact_mod_cast h
  have hx0 : (0:ℝ) < (x:ℝ) := by linarith
  have hlogpos : 0 < Real.log (x:ℝ) := Real.log_pos hx1
  have hlog_le : Real.log (x:ℝ) ≤ 6 * (x:ℝ) ^ ((1:ℝ)/6) := by
    have h := Real.log_le_rpow_div (x := (x:ℝ)) (le_of_lt hx0) (by norm_num : (0:ℝ) < 1/6)
    calc Real.log (x:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/6) / (1/6) := h
      _ = 6 * (x:ℝ) ^ ((1:ℝ)/6) := by ring
  have hx16 : (24:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/6) := by
    have h24 : ((24:ℝ))^6 ≤ (x:ℝ) := by
      have h : (((24:ℕ)^6 : ℕ) : ℝ) ≤ ((x:ℕ) : ℝ) := by exact_mod_cast hx
      push_cast at h
      linarith
    calc (24:ℝ) = ((24:ℝ)^6) ^ ((1:ℝ)/6) := by
          rw [← Real.rpow_natCast (24:ℝ) 6, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 24)]
          norm_num
      _ ≤ (x:ℝ) ^ ((1:ℝ)/6) := Real.rpow_le_rpow (by positivity) h24 (by norm_num)
  have hp16 : (x:ℝ) ^ ((1:ℝ)/6) * (x:ℝ) ^ ((1:ℝ)/6) = (x:ℝ) ^ ((1:ℝ)/3) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h13pos : 0 < (x:ℝ) ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos hx0 _
  have h16pos : 0 < (x:ℝ) ^ ((1:ℝ)/6) := Real.rpow_pos_of_pos hx0 _
  have hlog_small : Real.log (x:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) / 2 := by
    nlinarith [hlog_le, hx16, h16pos, hp16]
  have hlog2 : (Real.log (x:ℝ))^2 ≤ ((x:ℝ) ^ ((1:ℝ)/3))^2 / 4 := by
    nlinarith [hlog_small, le_of_lt hlogpos]
  have hY : (Submission.chenWindowTop x : ℝ) ≤ 2 * (x:ℝ) ^ ((1:ℝ)/3) := by
    have hcw : (Submission.chenWindowTop x : ℝ)
        = (⌊Real.rpow (x:ℝ) ((1:ℝ)/3)⌋₊ : ℝ) + 2 := by
      rw [Submission.chenWindowTop, Nat.cast_add, Nat.cast_ofNat]
    rw [hcw]
    rw [show Real.rpow (x:ℝ) ((1:ℝ)/3) = (x:ℝ) ^ ((1:ℝ)/3) from rfl]
    have hfloor : ((⌊(x:ℝ) ^ ((1:ℝ)/3)⌋₊ : ℕ) : ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) :=
      Nat.floor_le (Real.rpow_nonneg (le_of_lt hx0) _)
    have hone : (2:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/3) := by
      have h2 : (2:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/6) := by linarith
      nlinarith [h2, hp16, h13pos, h16pos]
    linarith
  have hpow3 : ((x:ℝ) ^ ((1:ℝ)/3))^3 = (x:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hx0)]
    norm_num
  have hmain : 2 * (x:ℝ) ^ ((1:ℝ)/3) ≤ (x:ℝ) / (Real.log (x:ℝ))^2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hlog2, h13pos, hpow3]
  linarith

/-- **The `B`-term count from the sieve input.**  If the survivors of the ternary sequence
number at most `C x/(log x)^2` eventually, with `C ≤ 2`, then the `B`-term count is at most
`3x/(log x)^2` eventually: the elementary reduction costs `+Y ≤ x/(log x)^2`. -/
theorem chen_bterm_count_upper_of_sieveInput (C : ℝ) (hC : C ≤ 2) (h : BTermSieveInput C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Submission.bTermCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        ≤ 3 * (x : ℝ) / (Real.log (x : ℝ)) ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 h
  filter_upwards [eventually_ge_atTop (max x₀ ((24:ℕ)^6)), eventually_ge_atTop 3] with x hx hx3
  have hxh : max x₀ ((24:ℕ)^6) ≤ x := hx
  have hx₀' : x₀ ≤ x := le_trans (le_max_left _ _) hxh
  have hx72 : (24:ℕ)^6 ≤ x := le_trans (le_max_right _ _) hxh
  have hxpos : (0:ℝ) < (x:ℝ) := by positivity
  have hlogpos : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hsurv := hx₀ x hx₀'
  have hred : (Submission.bTermCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
      ≤ (survivorCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        + (Submission.chenWindowTop x : ℝ) := by
    exact_mod_cast bTermCount_le_survivorCount_add x (Submission.chenSiftLimit x)
      (Submission.chenWindowTop x)
  have hY := chenWindowTop_le x hx72
  have hCx : C * (x:ℝ) / (Real.log (x:ℝ))^2 ≤ 2 * (x:ℝ) / (Real.log (x:ℝ))^2 := by
    have h1 : C * (x:ℝ) ≤ 2 * (x:ℝ) := by nlinarith
    exact div_le_div_of_nonneg_right h1 (by positivity)
  calc (Submission.bTermCount x (Submission.chenSiftLimit x)
        (Submission.chenWindowTop x) : ℝ)
      ≤ (survivorCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        + (Submission.chenWindowTop x : ℝ) := hred
    _ ≤ C * (x:ℝ) / (Real.log (x:ℝ))^2 + (x:ℝ) / (Real.log (x:ℝ))^2 := add_le_add hsurv hY
    _ ≤ 2 * (x:ℝ) / (Real.log (x:ℝ))^2 + (x:ℝ) / (Real.log (x:ℝ))^2 := add_le_add hCx le_rfl
    _ = 3 * (x:ℝ) / (Real.log (x:ℝ))^2 := by ring

end Work.NumberTheory.Chen.BTermCount
