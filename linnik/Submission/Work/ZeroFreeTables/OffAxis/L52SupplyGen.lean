import Mathlib
import Submission.Work.ZeroFreeTables.HB94.L52supply

namespace Work.ZeroFreeTables.OffAxis

open DirichletCharacter

/-- **The `L52Hyp` supply at `c = 1/6` with the slack `ε` left free.**

For every `ε > 0` there are `δ ∈ (0,1)` and `q₀` such that every non-principal Dirichlet character
of modulus `q ≥ q₀` satisfies `L52Hyp χ (1/6) ε δ`, i.e. the log-derivative-plus-window bound of
Heath-Brown's Lemma 5.2 with the constant `1/6 + ε/4`.

This is the general-`ε` version of `Work.ZeroFreeTables.HB94.L52supply16`; the proof is the same
run of HB's Lemma 3.1 (`Work.LinnikAreas.l31free.lemma3_1_free_gen` at `φ = 1/3`, which is free in
both `ε` and `φ`) on the `sorry`-free Burgess input `LBound13_clean`, with the outer slack of
Lemma 3.1 instantiated at `ε/4`. -/
theorem L52SupplyGen :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ := by
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ)/3) (by norm_num)
      (ε := ε / 4) hε4 Work.ZeroFreeTables.HB94.LBound13_clean
  refine ⟨δ, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ s hsre1 hsre2 hsim
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
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
  have hc : (1 : ℝ)/3/2 + ε/4 ≤ (1:ℝ)/6 + ε/4 := by norm_num
  exact mul_le_mul_of_nonneg_right hc hlogq

end Work.ZeroFreeTables.OffAxis
