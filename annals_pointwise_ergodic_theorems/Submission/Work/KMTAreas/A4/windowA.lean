/-
# The free support window `A N^d` (area A4)

## Why this module exists — read this before working on `peluseLipL1TailA`

The A4 interface proved in `A4/peluseLipL1Tail.lean` pins the support window of Proposition
`lip` (Krause--Mirek--Tao, §5.1) to `N₀ ≤ 2 N^d`.  That pin is *too tight* (see
`NOTES_A4_window_pin_GAP.md`): §5.1 needs a **P-dependent** window `N₀ ∈ [N^d/A, A N^d]`, and
the pinned predicate is provably vacuous for `P = 100 X²`.  The repair is purely interface: keep
`A ≥ 1` explicit, let the implied constants `C, K` depend on `A`, and put `A N^d` in the spatial
tail clause.

**The only real change in the §5.1 argument is the truncation radius `D`.**

* In the `N`-large branch ("case B", the smoothing construction) the dual function is
  `F = λ • smoothOp w G q`, where `G` is the sign of the progression average cut to the window
  `[-MW, MW]`, `MW = D - q N'`, and `D` is *both* the radius outside which the tail of `F` is
  estimated *and* an upper bound for `N₀ + q N'`.  The proof needs
  `N₀ ≤ D`, `q N' ≤ D`, `MW ≤ D`, and (for the tail conversion) `D ≤ A N^d`.
  Taking `D := winA A N d = ⌊A N^d⌋` gives all four: `N₀` and `q N'` are *natural* numbers with
  `N₀ ≤ A N^d` (hypothesis) and `q N' ≤ N^d ≤ A N^d`, so they are `≤ ⌊A N^d⌋` by
  `Nat.le_floor`; and `⌊A N^d⌋ ≤ A N^d` by `Nat.floor_le`.
  The mass of `G` is `2 MW + 1 ≤ 2 D + 1 ≤ (2A + 2) N^d ≤ K' δ^{-u} N^d`, so the constant
  `K'` (which in the `A = 2` file is `5 + 2 C₀`) has to be enlarged to dominate `2A + 2`.
* The `N`-small branch ("case A") truncates the transposed dual to the ball of radius `D`; the
  same `D` works, and the tail beyond `A N^d` vanishes *identically* because `D ≤ A N^d` while
  `F` is supported in `[-D, D]`.

This module collects the elementary `⌊·⌋` bookkeeping, plus copies of four one-line helpers that
live inside the (currently non-compiling) `A4/peluseLipL1Tail.lean` and that both branches need.
**Do not import `A4/peluseLipL1Tail.lean`: it does not compile** (its case-B proof has a long
list of unfinished proof obligations).  Its *statements* are still the best guide to the proof,
so copy from it (textually) rather than importing it.

## Route for the `N`-large branch (case `B`)

The `A = 2` case-`B` construction lives (unfinished, and currently **not compiling**) in
`A4/peluseLipL1Tail.lean`, theorem `lipL1Tail_caseB` (lines 126--1050); its *statements* are a
reliable guide.  The `A`-dependence is confined to four places:

1. `set D : ℕ := 2 * N ^ P.natDegree` becomes `set D : ℕ := winA A N P.natDegree`, and the
   equalities `(D : ℝ) = 2 * (N : ℝ) ^ P.natDegree` become the inequality
   `(D : ℝ) ≤ A * (N : ℝ) ^ P.natDegree` (`winA_le`).  The two facts `N₀ ≤ D` and `q N' ≤ D`
   (`N₀` and `q N'` are *naturals* with `N₀ ≤ A N^d` and `q N' ≤ N^d ≤ A N^d`) come from
   `le_winA`; `MW := D - q N'` and `(MW : ℤ) = (D : ℤ) - (q : ℤ) * N'` are unchanged.
2. The tail conversion `2 * N^d < |x| ↔ D < x.natAbs` becomes the one-way implication
   `A * N^d < |x| → D < x.natAbs` (`winA_lt_natAbs`), which is all the argument uses.
3. `hMdW : 2 * MW + 1 ≤ K' δ^{-u} N^d` needs `K' ≥ 2A + 2` instead of `K' ≥ 5`
   (as `MW ≤ D ≤ A N^d` and `N^d ≥ 1`).  Every other constant inequality is of the shape
   "`Cc` dominates an explicit expression in `c₁, c₂, K'`" and is insensitive to the value of
   `K'` as long as `c₁ = 1 + 4 C₀ calcConst ψ K'` and `c₂ = 4 C₀² calcConst ψ K'` grow with it.
4. The largeness hypotheses: `N > Cc δ^{-Kc}` is used only through `winA_master`
   (`α δ^{-A} ≤ N^j` when `α ≤ Cc^j`, `A ≤ Kc j`) and `winA_rpow_low`
   (`Cc / N ≤ δ^P` for `P ≤ Kc`), so choosing `Kc = 5 * u + 6` (and `Cc` dominating the finitely
   many expressions appearing) transports verbatim.

**Watch out**: the tail clause `∑_{|x| > A N^d} ‖F x‖ ≤ δ^K N^d / 2` *tightens* as `K` grows, so
`K` should be taken as small as the largeness requirements allow (in particular `K ≥` the Peluse
exponent plus `2u`), and a witness for a smaller exponent can always be *scaled down* by
`δ^{K' - K}` to one for a larger exponent `K' ≤ 1` (this is how `peluseLipL1TailA` merges the two
branches).

## Toolchain note (please read)

Elaborating the whole of `A4/peluseLipL1Tail.lean` in one go currently exceeds this sandbox's
memory budget (`12 GB`), partly because of its very long chains of `linarith`/`nlinarith` over
dozens of local hypotheses.  When writing the `A`-parameterised case `B`, prefer

* short explicit `calc` chains with `mul_le_mul_of_nonneg_left/right`, `le_trans`, `div_le_div...`
  and the packaged facts `winA_master`, `winA_rpow_low`, `winA_le`, `le_winA`, `winA_lt_natAbs`,
  `winA_card_Icc_diff_Icc_le` instead of one `linarith` over everything;
* splitting the construction into several top-level lemmas in *separate small modules* (each one
  is then compiled on its own and the memory stays bounded);
* developing proofs in the REPL (`lean_check`/`lean_tactic`) before pasting them in, since a full
  standalone compile only happens when a Lean slot frees up.

## Main results

* `Work.KMTAreas.A4.winA`, `winA_le`, `le_winA`, `winA_lt_natAbs`, `winA_nonneg`;
* `winA_real_lt_natAbs`, `winA_supportIn_natAbs_le`, `winA_card_Icc_diff_Icc_le`,
  `winA_card_Icc_int` (copies of helpers of `peluseLipL1Tail`);
* `winA_master` (the "largeness calculus" used repeatedly in case B: a large `N` absorbs
  `α δ^{-A}` as soon as `Α ≤ K j` and `α ≤ T^j`, where `N > T δ^{-K}`).
-/
import Mathlib
import Submission.Work.Analysis.InverseTheory.MajorArcs
import Submission.Work.Analysis.InverseTheory.AhalfZAPI

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Elementary helpers (copies of one-line facts of `A4/peluseLipL1Tail.lean`) -/

/-- `((B : ℕ) : ℝ) < |(x : ℝ)|` for integers, in terms of `x.natAbs`. -/
theorem winA_real_lt_natAbs {B : ℕ} {x : ℤ} : (B : ℝ) < |(x : ℝ)| ↔ B < x.natAbs := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

/-- The natural absolute value of an integer is its real absolute value. -/
theorem winA_natAbs_cast_real (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  norm_num

/-- A function supported in `[-M, M]` vanishes outside that interval. -/
theorem winA_supportIn_natAbs_le {f : ℤ → ℂ} {M : ℕ} (h : SupportIn f M) {x : ℤ}
    (hx : f x ≠ 0) : x.natAbs ≤ M := by
  by_contra hc
  exact hx (h x (not_le.mp hc))

/-- `card ([-M,M] \ [-W,W]) ≤ 2 (M - W)`. -/
theorem winA_card_Icc_diff_Icc_le (M W : ℕ) :
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))).card ≤ 2 * (M - W) := by
  have hsub : (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))
      ⊆ Finset.Icc ((W : ℤ) + 1) (M : ℤ) ∪ Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1)) := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hy
    rcases hy with ⟨⟨h1, h2⟩, h3⟩
    simp only [Finset.mem_union, Finset.mem_Icc]
    by_cases h5 : -(W : ℤ) ≤ y
    · left
      constructor <;> omega
    · right
      constructor <;> omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : (Finset.Icc ((W : ℤ) + 1) (M : ℤ)).card ≤ M - W := by
    rw [Int.card_Icc]
    omega
  have h2 : (Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1))).card ≤ M - W := by
    rw [Int.card_Icc]
    omega
  omega

/-- `card [-M, M] = 2 M + 1`. -/
theorem winA_card_Icc_int (M : ℕ) : ((Finset.Icc (-(M : ℤ)) (M : ℤ)).card) = 2 * M + 1 := by
  have h1 : (-(M : ℤ)) ≤ (M : ℤ) := by omega
  rw [Int.card_Icc]
  omega

/-! ## The truncation radius `⌊A N^d⌋` -/

/-- The truncation radius of the free-window Proposition `lip`: `⌊A N^d⌋`. -/
noncomputable def winA (A : ℝ) (N d : ℕ) : ℕ := Nat.floor (A * (N : ℝ) ^ d)

theorem winA_le (A : ℝ) (hA : 0 ≤ A) (N d : ℕ) :
    (winA A N d : ℝ) ≤ A * (N : ℝ) ^ d :=
  Nat.floor_le (mul_nonneg hA (pow_nonneg (by positivity) d))

theorem le_winA (A : ℝ) {N d M : ℕ} (h : (M : ℝ) ≤ A * (N : ℝ) ^ d) :
    M ≤ winA A N d :=
  Nat.le_floor h

theorem winA_nonneg (A : ℝ) (N d : ℕ) : 0 ≤ (winA A N d : ℝ) := Nat.cast_nonneg _

/-- The integers outside the ball of radius `A N^d` are outside the ball of radius `⌊A N^d⌋`. -/
theorem winA_lt_natAbs {A : ℝ} (hA : 0 ≤ A) {N d : ℕ} {x : ℤ}
    (h : A * (N : ℝ) ^ d < |(x : ℝ)|) : winA A N d < x.natAbs := by
  have h1 : (winA A N d : ℝ) ≤ A * (N : ℝ) ^ d := winA_le A hA N d
  rw [← winA_real_lt_natAbs]
  exact lt_of_le_of_lt h1 h

/-! ## The largeness calculus of case `B`

In case `B` the hypothesis is that `N` dominates a threshold `T δ^{-K}`.  Every estimate of the
form "`α δ^{-A}` is at most a power of `N`" is then an instance of the following lemma: write
`α δ^{-A} ≤ T^j (T δ^{-K})^j` and use `N > T δ^{-K}`. -/

/-- **The master inequality of case `B`.**  If `N > T δ^{-K}` with `T ≥ 1`, `0 < δ ≤ 1`, and
`α ≤ T^j`, `A ≤ K j`, `α ≥ 0`, `j ≥ 1`, then `α δ^{-A} ≤ N^j`. -/
theorem winA_master {T K N δ : ℝ} (hT1 : 1 ≤ T) (hNpos : 0 < N) (hδpos : 0 < δ)
    (hδle : δ ≤ 1) (hN : T * δ⁻¹ ^ K < N) {α A : ℝ} {j : ℕ} (hα0 : 0 ≤ α) (hj : 1 ≤ j)
    (hα : α ≤ T ^ j) (hA : A ≤ K * (j : ℝ)) : α * δ⁻¹ ^ A ≤ N ^ j := by
  have hδ0 : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hδ1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have h1 : δ⁻¹ ^ A ≤ δ⁻¹ ^ (K * (j : ℝ)) := Real.rpow_le_rpow_of_exponent_le hδ1 hA
  have h2 : δ⁻¹ ^ (K * (j : ℝ)) = ((δ⁻¹) ^ K) ^ j := by
    rw [Real.rpow_mul hδ0.le, Real.rpow_natCast]
  have h3 : δ⁻¹ ^ A ≤ ((δ⁻¹) ^ K) ^ j := by
    calc δ⁻¹ ^ A ≤ δ⁻¹ ^ (K * (j : ℝ)) := h1
      _ = ((δ⁻¹) ^ K) ^ j := h2
  calc α * δ⁻¹ ^ A ≤ T ^ j * δ⁻¹ ^ A :=
        mul_le_mul_of_nonneg_right hα (Real.rpow_nonneg hδ0.le A)
    _ ≤ T ^ j * ((δ⁻¹) ^ K) ^ j := mul_le_mul_of_nonneg_left h3 (pow_nonneg hT0 j)
    _ = (T * δ⁻¹ ^ K) ^ j := by rw [mul_pow]
    _ ≤ N ^ j := pow_le_pow_left₀ (mul_nonneg hT0 (Real.rpow_nonneg hδ0.le K)) hN.le j

/-- **Lower bounds for `δ^P` from the case-`B` largeness.**  If `C δ^{-K} < N` with `C > 0` and
`0 < δ ≤ 1`, then `C / N ≤ δ^P` for every `P ≤ K`.  (In case `B` this turns `q ≤ C δ^{-K}` and
`N ≥ C δ^{-K}` into lower bounds `q / N ≤ δ^P`.) -/
theorem winA_rpow_low {C K N δ P : ℝ} (hC : 0 < C) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hN : C * δ⁻¹ ^ K < N) (hPK : P ≤ K) : C / N ≤ δ ^ P := by
  have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hδK : 0 < δ ^ K := Real.rpow_pos_of_pos hδpos K
  have hNpos : 0 < N :=
    lt_of_lt_of_le (mul_pos hC (Real.rpow_pos_of_pos hδinv_pos K)) hN.le
  have h2 : (C * δ⁻¹ ^ K) * δ ^ K < N * δ ^ K := mul_lt_mul_of_pos_right hN hδK
  have h3 : (C * δ⁻¹ ^ K) * δ ^ K = C := by
    rw [mul_assoc, ← Real.mul_rpow hδinv_pos.le hδpos.le, inv_mul_cancel₀ hδpos.ne',
      Real.one_rpow, mul_one]
  have h4 : C < N * δ ^ K := by rw [h3] at h2; exact h2
  have h5 : δ ^ K ≤ δ ^ P := Real.rpow_le_rpow_of_exponent_ge hδpos hδle hPK
  rw [div_le_iff₀ hNpos]
  have h6 : N * δ ^ K ≤ δ ^ P * N := by
    rw [mul_comm (δ ^ P) N]
    exact mul_le_mul_of_nonneg_left h5 hNpos.le
  exact le_trans h4.le h6

end Work.KMTAreas.A4
