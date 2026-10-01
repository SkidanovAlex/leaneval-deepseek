import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.ZeroFreeTables.HB94.L52supply

/-!
# `L52Hyp` at the level `1/6` for every non-principal character, with an arbitrary slack `ε`

Heath-Brown's Lemma 3.1 (with the Burgess exponent `φ = 1/3` of his Lemma 2.5) gives, for a
primitive non-principal character `χ` of level `N` and every `ε > 0` (with `δ = δ(ε) ∈ (0,1)`
and `N ≥ N₀(ε, δ)`),

`-Re (L'/L)(s,χ) + Σ_{|1 + i·Im s - ρ| ≤ δ} Re (1/(s-ρ)) ≤ (1/6 + ε) log N`

on the Lemma-5.2 range of `s`.  The window form `Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ`
records exactly the case in which the slack `ε` of Lemma 3.1 is used, and it is this form that the
Lemma 5.2 engine (`Ksum_le_self_of_L52_phi`, `Ksum_le_single_of_L52_phi`) consumes.

The Burgess input `Work.LinnikContract.LBound13` (HB Lemma 2.5 with `φ = 1/3`) is available
`sorry`-free as `Work.ZeroFreeTables.HB94.LBound13_clean`; feeding it to the `φ`-free Lemma 3.1
`Work.LinnikAreas.l31free.lemma3_1_free_gen` at slack `ε/4` produces the constant
`(1/3)/2 + ε/4 = 1/6 + ε/4` of `L52Hyp χ (1/6) ε δ`, so `δ` and `q₀` are produced from `ε`.
-/

open DirichletCharacter

noncomputable section

namespace Work.ZeroFreeTables

/-- **`L52Hyp` at the level `1/6`, with the window radius produced from `ε`.**  For every `ε > 0`
there are `δ ∈ (0,1)` and `q₀` such that every non-principal character `χ` modulo `q ≥ q₀` with
non-zero conductor satisfies Heath-Brown's Lemma 5.2 hypothesis `L52Hyp χ (1/6) ε δ`. -/
theorem L52Hyp_six_level (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ := by
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ)/3) (by norm_num)
      (ε := ε/4) (by linarith) Work.ZeroFreeTables.HB94.LBound13_clean
  refine ⟨δ, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ s hsre1 hsre2 hsim
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := by
    have h := Work.LinnikAreas.l31free.three_le_of_char_ne_one χ.primitiveCharacter hχ'
    exact_mod_cast h
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hNL : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have h1 := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (L := Real.log (q : ℝ))
    hL₀le hNL s hsre1 hsre2 hsim
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  refine le_trans h1 ?_
  have hc : (1 : ℝ)/3/2 + ε/4 = (1:ℝ)/6 + ε/4 := by norm_num
  rw [hc]

end Work.ZeroFreeTables
