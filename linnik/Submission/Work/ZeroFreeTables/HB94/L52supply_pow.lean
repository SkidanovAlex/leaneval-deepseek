import Mathlib
import Submission.Work.ZeroFreeTables.HB94.lemma3_1_free_pow
import Submission.Work.ZeroFreeTables.HB94.hbound_quarter_pow_h
import Submission.Work.LinnikAreas.area1
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter

noncomputable section

namespace Work.ZeroFreeTables.HB94

/-!
# The `c = 1/8` `L52Hyp` supply for characters with `χ ^ 60 = 1`

HB Lemma 2.5 gives `φ = 1/4` (instead of the general `1/3`) for every character of order dividing
`60` (an absolute constant), so HB Lemma 3.1 then gives the window bound with the constant
`φ/2 = 1/8`.  This is the input that the `(C3)` case of Lemma 9.4 needs, where the four characters
`χ₁, χ₂, χ₁χ₂, χ₁χ₂⁻¹` all have order dividing `lcm(3,4,5) = 60`.

The formal ingredients are `Work.ZeroFreeTables.HB94.lemma3_1_free_pow 60` (HB Lemma 3.1 with the
hypothesis `χ ^ 60 = 1`) and the `sorry`-free `Work.ZeroFreeTables.HB94.hbound_quarter_pow_h 60`
(HB Lemma 2.5 with `φ = 1/4` for `χ ^ 60 = 1`); the transport from the conductor `χ.conductor`
to the level `q` (with `L := log q`) is the one of `HB94/L52supply18.lean`.
-/

/-- **`L52Hyp` with `c = 1/8` for characters with `χ ^ 60 = 1`.** -/
theorem L52supply_pow :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ ^ 60 = 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ := by
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    lemma3_1_free_pow 60 (φ := (1 : ℝ)/4) (by norm_num)
      (ε := 1/4000000) (by norm_num) (hbound_quarter_pow_h 60 (by norm_num))
  refine ⟨δ, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ hχ60 s hsre1 hsre2 hsim
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
  have hcon : 3 ≤ χ.conductor := Work.LinnikAreas.conductor_ge_three χ hχ
  have hconle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hNL : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast hconle
  have hχ'60 : (χ.primitiveCharacter) ^ 60 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter]
    exact orderOf_dvd_iff_pow_eq_one.mpr hχ60
  have h1 := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hχ'60 (L := Real.log (q : ℝ))
    hL₀le hNL s hsre1 hsre2 hsim
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  refine le_trans h1 ?_
  have hc : (1 : ℝ)/4/2 + 1/4000000 ≤ (1:ℝ)/8 + (1/1000000)/4 := by norm_num
  exact mul_le_mul_of_nonneg_right hc hlogq

end Work.ZeroFreeTables.HB94
