/-
# ZeroFreeTables/OffAxis/RectDefs

Bookkeeping for the **height-`L` `λ₀`-bound** (`OffAxis/RectLam0`).

The engines of HB §§8–9 are stated for the height-`L` numbering
`Work.ZeroFreeTables.IsMinWideAt L W` (`OffAxis/WideDefs.lean`), and
`isMinWideAt_of_isRectStrip` converts the off-axis rectangle bookkeeping
`IsRectStrip L χ₁ ρ₁` into it below the strip threshold `2`.

This module adds the two elementary tools that the assembly uses:

* `lamOf_nonneg_of_zeroMult` — `λ ≥ 0` at a zero of non-zero multiplicity;
* `le_log_of_ceil_exp_le` — the threshold `⌈e^T⌉ + 1` realises `T ≤ log q`;
* `exists_minZero_ne_pair` — the height-`L` "second zero of maximal real part" tool
  (`Work.LinnikAreas.boxMaxZeroH` with the HB §6 exclusion of the conjugate pair).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.LinnikAreas.boxMaxZeroH

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- `λ(ρ) = (1 - Re ρ) log q ≥ 0` at a zero of non-zero multiplicity. -/
theorem lamOf_nonneg_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : zeroMult χ ρ ≠ 0) : 0 ≤ lamOf q ρ := by
  have hre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ h
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [lamOf]
  exact mul_nonneg (by linarith) hlog

/-- The threshold `⌈e^T⌉ + 1` realises `T ≤ log q`. -/
theorem le_log_of_ceil_exp_le {T : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp T) + 1 ≤ q) :
    T ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp T ≤ (Nat.ceil (Real.exp T) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp T) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp T ≤ (q : ℝ) := by linarith
  calc T = Real.log (Real.exp T) := (Real.log_exp T).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos T) h3

/-- **The `λ`-minimal zero of `χ₁` at height `≤ L`, avoiding the pair `{ρ₁, conj ρ₁}`.**

Given a zero `ρ` of `χ₁` of height `≤ L` which is neither `ρ₁` nor `conj ρ₁`, there is a zero
`ρ₂` of `χ₁`, also of height `≤ L` and avoiding that pair, with `λ(ρ₂) ≤ λ(ρ)` and minimal among
all such zeros (HB §6: "choose such a zero `ρ⁰` with `Re(ρ⁰)` maximal"). -/
theorem exists_minZero_ne_pair {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ : ℂ}
    {L : ℝ} (hχ : χ₁ ≠ 1) (hL : 1 ≤ L) (hρ : zeroMult χ₁ ρ ≠ 0) (him : |ρ.im| ≤ L)
    (hne₁ : ρ ≠ ρ₁) (hne₂ : ρ ≠ starRingEnd ℂ ρ₁) :
    ∃ ρ₂, zeroMult χ₁ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ L ∧ ρ₂ ≠ ρ₁ ∧ ρ₂ ≠ starRingEnd ℂ ρ₁ ∧
      lamOf q ρ₂ ≤ lamOf q ρ ∧
      ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ L → u ≠ ρ₁ → u ≠ starRingEnd ℂ ρ₁ →
        lamOf q ρ₂ ≤ lamOf q u := by
  classical
  have hq2 : 2 ≤ q := by
    by_contra h
    have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hq1 : q = 1 := by omega
    exact hχ (DirichletCharacter.level_one' χ₁ hq1)
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hρre : ρ.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hρ
  have hfin := Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ₁ ρ.re L
  set S : Finset ℂ :=
    hfin.toFinset.filter (fun u => u ≠ ρ₁ ∧ u ≠ starRingEnd ℂ ρ₁) with hS
  have hmemS : ∀ u : ℂ, u ∈ S ↔
      (zeroMult χ₁ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ L) ∧
        u ≠ ρ₁ ∧ u ≠ starRingEnd ℂ ρ₁ := by
    intro u
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
      exact ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
      exact ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
  have hρS : ρ ∈ S := by
    rw [hmemS]
    exact ⟨⟨hρ, le_rfl, hρre.le, him⟩, hne₁, hne₂⟩
  obtain ⟨ρ₂, hρ₂mem, hmin⟩ := Finset.exists_min_image S (fun u => lamOf q u) ⟨ρ, hρS⟩
  obtain ⟨⟨hzm, -, -, him₂⟩, hne1₂, hne2₂⟩ := (hmemS ρ₂).mp hρ₂mem
  refine ⟨ρ₂, hzm, him₂, hne1₂, hne2₂, hmin ρ hρS, ?_⟩
  intro u hzu himu hune1 hune2
  rcases lt_or_ge (lamOf q ρ) (lamOf q u) with hlt | hle
  · exact le_trans (hmin ρ hρS) hlt.le
  · have hre_le : ρ.re ≤ u.re := by
      have h1 : (1 - u.re) * Real.log q ≤ (1 - ρ.re) * Real.log q := hle
      have h2 : 1 - u.re ≤ 1 - ρ.re := (mul_le_mul_iff_left₀ hlogpos).mp h1
      linarith
    have huS : u ∈ S := by
      rw [hmemS]
      exact ⟨⟨hzu, hre_le,
        le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hzu), himu⟩,
        hune1, hune2⟩
    exact hmin u huS

end Work.ZeroFreeTables
