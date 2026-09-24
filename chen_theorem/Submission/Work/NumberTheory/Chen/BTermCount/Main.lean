import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.NumberTheory.Chen.BTermCount.Bounds
import Submission.Work.NumberTheory.Chen.BTermCount.bTripleCount_le_barC
import Submission.Work.NumberTheory.Chen.BTermCount.bTripleCount_le_barC_sharp

open Finset Filter
open scoped BigOperators Topology

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The `B`-term count: main statements

This module records the unconditional consequences of the triple count
(`bTripleCount_le_barC`) for the `B`-term count `Submission.bTermCount`:

* `bTermCount_le_barC` — for a general sift limit `M ≥ x^{1/14}` and window top
  `x^{1/3} ≤ Y ≤ 2 x^{1/3}`: `bTermCount x M Y ≤ (0.85 + ε) x / log x`;
* `chen_bterm_count_le` — the same at Chen's parameters
  `M = chenSiftLimit x ≈ x^{0.0749}`, `Y = chenWindowTop x = ⌊x^{1/3}⌋ + 2`.

The bound is the *first* step of the `B`-term estimate (the count of triples `q q₂ q₃`); the
second step, the upper-bound sieve isolating the `q₃` for which `q q₂ q₃ - 2` is *prime*, is
isolated in `SieveInterface.lean` as the hypothesis `BTermSieveInput` and is not available in
this workspace (see `notes/BTERM_COUNT_ANALYSIS.md` for the constants: the sharp linear sieve
would give `3.52 · x/log²x`, the truth is near `1.9 · x/log²x`, and the requested constant `3`
needs a sieve stronger than the linear sieve).
-/

/-- **The `B`-term count is `≪ x/log x`** (first step only: the number of triples).  For a sift
limit `M ≥ x^{1/14}` and a window top `x^{1/3} ≤ Y ≤ 2 x^{1/3}`,

`bTermCount x M Y ≤ (0.85 + ε) x / log x`  for all large `x`. -/
theorem bTermCount_le_barC (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop, ∀ M Y : ℕ,
      (x : ℝ) ^ ((1:ℝ)/14) ≤ (M : ℝ) →
      (x : ℝ) ^ ((1:ℝ)/3) ≤ (Y : ℝ) →
      (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1:ℝ)/3) →
      (Submission.bTermCount x M Y : ℝ) ≤ (0.85 + ε) * (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (bTripleCount_le_barC ε hε)
  filter_upwards [eventually_ge_atTop x₀] with x hx
  intro M Y hM hY1 hY2
  have h := hx₀ x hx M Y hM hY1 hY2
  have h2 : (Submission.bTermCount x M Y : ℝ) ≤ (bTripleCount x M Y : ℝ) := by
    exact_mod_cast bTermCount_le_bTripleCount x M Y
  linarith

/-- **The `B`-term count at Chen's parameters.**  With `M = chenSiftLimit x` and
`Y = chenWindowTop x = ⌊x^{1/3}⌋ + 2`,

`bTermCount x M Y ≤ (0.85 + ε) x / log x`  for all large `x`. -/
theorem chen_bterm_count_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Submission.bTermCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        ≤ (0.85 + ε) * (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (bTermCount_le_barC ε hε)
  filter_upwards [eventually_ge_atTop (max x₀ 8)] with x hx
  have hx' : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  exact hx₀ x hx' _ _ (chenSiftLimit_ge_rpow x) (chenWindowTop_ge_rpow x)
    (chenWindowTop_le_two_rpow x hx8)

/-- The `θ`-mass of the `B`-term is at most `log (x+2)` times the count. -/
theorem bTermMass_le_count' (x M Y : ℕ) :
    Submission.bTermMass x M Y
      ≤ (Submission.bTermCount x M Y : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := by
  have hset : ((Submission.s0Set x M).filter (fun p => ∃ q q₂ q₃ : ℕ, q.Prime ∧ q₂.Prime ∧
      q₃.Prime ∧ M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ p + 2 = q * q₂ * q₃))
      = bTermSet x M Y := rfl
  rw [Submission.bTermMass, hset, bTermCount_eq_card_bTermSet]
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
  have hps : p ∈ Submission.s0Set x M := (Finset.mem_filter.mp hp).1
  have hpx : p < x + 1 := (mem_s0Set'.mp hps).1
  have hp2 : 2 ≤ p := (mem_s0Set'.mp hps).2.1.two_le
  have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have h2 : (p:ℝ) ≤ (((x + 2 : ℕ)) : ℝ) := by
    have : p ≤ x + 2 := by omega
    exact_mod_cast this
  exact Real.log_le_log h1 h2

/-- **The `B`-term `θ`-mass at Chen's parameters.**  This is the form consumed by the switch
(`bTermMass` is the sum of `log p` over the counted primes).  The constant is `2 · 0.85`, using
the crude `log (x+2) ≤ 2 log x` for `x ≥ 3`. -/
theorem chen_bTermMass_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop,
      Submission.bTermMass x (Submission.chenSiftLimit x) (Submission.chenWindowTop x)
        ≤ (1.75 + ε) * (x : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (chen_bterm_count_le (ε/2) (by linarith))
  filter_upwards [eventually_ge_atTop (max x₀ 3)] with x hx
  have hx₀' : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hxpos : (0:ℝ) < (x:ℝ) := by positivity
  have hlogpos : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hcount := hx₀ x hx₀'
  have hmass := bTermMass_le_count' x (Submission.chenSiftLimit x) (Submission.chenWindowTop x)
  have hlog2 : Real.log (((x + 2 : ℕ)) : ℝ) ≤ 2 * Real.log (x:ℝ) := by
    have hx2 : (1:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 1 < x)
    have hle : (((x + 2 : ℕ)) : ℝ) ≤ (x:ℝ)^2 := by
      have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx3
      have hfac : 0 ≤ ((x:ℝ) - 2) * ((x:ℝ) + 1) :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      nlinarith [hfac]
    calc Real.log (((x + 2 : ℕ)) : ℝ) ≤ Real.log ((x:ℝ)^2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (x:ℝ) := by rw [Real.log_pow]; norm_num
  have hlog2nn : 0 ≤ Real.log (((x + 2 : ℕ)) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x + 2))
  have hstep : ((0.85 + ε/2) * (x:ℝ) / Real.log (x:ℝ)) * (2 * Real.log (x:ℝ))
      = (1.7 + ε) * (x:ℝ) := by
    field_simp [hlogpos.ne']
    ring
  calc Submission.bTermMass x (Submission.chenSiftLimit x) (Submission.chenWindowTop x)
      ≤ (Submission.bTermCount x (Submission.chenSiftLimit x)
          (Submission.chenWindowTop x) : ℝ) * Real.log (((x + 2 : ℕ)) : ℝ) := hmass
    _ ≤ ((0.85 + ε/2) * (x:ℝ) / Real.log (x:ℝ)) * (2 * Real.log (x:ℝ)) :=
        mul_le_mul hcount hlog2 hlog2nn (by
          apply div_nonneg _ (le_of_lt hlogpos)
          apply mul_nonneg _ (le_of_lt hxpos)
          linarith)
    _ = (1.7 + ε) * (x:ℝ) := hstep
    _ ≤ (1.75 + ε) * (x:ℝ) := by
        have : (1.7:ℝ) + ε ≤ 1.75 + ε := by linarith
        exact mul_le_mul_of_nonneg_right this (le_of_lt hxpos)

/-- **Sharper unconditional `B`-term count.**  Same as `chen_bterm_count_le` but with the constant
`0.78` (from the sharpened triple count `bTripleCount_le_barC_sharp`). -/
theorem chen_bterm_count_le_sharp (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Submission.bTermCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ)
        ≤ (0.78 + ε) * (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (bTripleCount_le_barC_sharp ε hε)
  filter_upwards [eventually_ge_atTop (max x₀ 8)] with x hx
  have hx' : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have h := hx₀ x hx' (Submission.chenSiftLimit x) (Submission.chenWindowTop x)
    (chenSiftLimit_ge_rpow x) (chenWindowTop_ge_rpow x) (chenWindowTop_le_two_rpow x hx8)
  have h2 : (Submission.bTermCount x (Submission.chenSiftLimit x)
      (Submission.chenWindowTop x) : ℝ)
      ≤ (bTripleCount x (Submission.chenSiftLimit x) (Submission.chenWindowTop x) : ℝ) := by
    exact_mod_cast bTermCount_le_bTripleCount x _ _
  linarith

end Work.NumberTheory.Chen.BTermCount
