import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.ZeroFreeTables.P9F.table9_top

/-!
# ZeroFreeTables/P9F/L52HypOfBurgess

`L52Hyp` with an *explicit* constant and window radius, **from the Burgess input `LBound13`
taken as a hypothesis** — the counterpart of `Work.LinnikAreas.DhCapped.L52HypExplicit`
(which proves the same thing from the *proof* `Work.LinnikAreas.LBound13_holds`, a module that
in turn pulls in `Work.LinnikBurgess.singleton_sum_all` and is not part of this area).

`Area3 = Area1 → ZeroFreeCert` and `Area1 = LBound13 ∧ LBoundSmall`, so this area is entitled
to `LBound13` as a hypothesis; threading it explicitly is what keeps this area's build closure
free of the other areas' WIP.
-/
open DirichletCharacter

noncomputable section

namespace Work.ZeroFreeTables.P9F

/-- The explicit constant of the Lemma 5.2 hypothesis produced by the Burgess exponent
`φ = 1/3`: `(1/3)/2 + 10⁻⁶`. -/
def l52C' : ℝ := 1 / 6 + 1 / 1000000

theorem l52C'_pos : 0 < l52C' := by rw [l52C']; norm_num

/-- **HB Lemma 5.2's hypothesis at the Burgess constant, from `LBound13`.** -/
theorem l52HypExplicit_of_LBound13 (hBurg : Work.LinnikContract.LBound13) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → ∀ ε : ℝ, 0 < ε →
        Commons.NumberTheory.Linnik.L52Hyp χ l52C' ε δ := by
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1 : ℝ)/3) (by norm_num)
      (ε := 1/1000000) (by norm_num) hBurg
  refine ⟨δ, hδpos, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ ε hε s hsre1 hsre2 hsim
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
  have hc : (1 : ℝ)/3/2 + 1/1000000 ≤ l52C' + ε/4 := by
    have h : (1 : ℝ)/3/2 = 1/6 := by norm_num
    rw [h, l52C']; linarith only [hε]
  exact mul_le_mul_of_nonneg_right hc hlogq

end Work.ZeroFreeTables.P9F
