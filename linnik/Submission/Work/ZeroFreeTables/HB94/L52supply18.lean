import Mathlib
import Submission.Work.ZeroFreeTables.l31_ord
import Submission.Work.LinnikAreas.area1
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter

noncomputable section

namespace Work.ZeroFreeTables.HB94

/-!
# The `c = 1/8` `L52Hyp` supply for characters of bounded order

HB's Lemma 2.5 gives `φ = 1/4` (instead of the general `1/3`) whenever `ord χ ≤ log N`, and HB's
Lemma 3.1 then gives the window bound with the constant `φ/2 = 1/8`.  This is the input that the
(case `C`) route of Lemma 9.4 needs, where the seven characters involved all have order `≤ 5`.

The formal ingredients are `Work.ZeroFreeTables.L31ord.lemma3_1_free_ord` (HB Lemma 3.1 with the
order hypothesis, `φ` free) and the `sorry`-free `Work.LinnikAreas.LBoundSmall_holds`; the transport
from the conductor `χ.conductor` to the level `q` (with `L := log q`) is the one of
`Work.ZeroFreeTables.P9F.L52HypOfBurgess.l52HypExplicit_of_LBound13`.
-/

/-- **`L52Hyp` with `c = 1/8` for bounded order and conductor dominating the order.** -/
theorem L52supply18 :
    ∃ N₀ : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ q : ℕ, N₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        (orderOf χ : ℝ) ≤ Real.log ((χ.conductor : ℕ) : ℝ) →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ := by
  obtain ⟨L₀, δ, hδpos, hδ1, hmain⟩ :=
    Work.ZeroFreeTables.L31ord.lemma3_1_free_ord (φ := (1 : ℝ)/4) (by norm_num)
      (ε := 1/4000000) (by norm_num) Work.LinnikAreas.LBoundSmall_holds
  refine ⟨⌈Real.exp L₀⌉₊ + 3, δ, hδpos, hδ1, ?_⟩
  intro q hq _inst χ _instc hχ hord s hsre1 hsre2 hsim
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
  have hordprim : (orderOf χ.primitiveCharacter : ℝ) ≤ Real.log ((χ.conductor : ℕ) : ℝ) := by
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter]
    exact hord
  have h1 := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hordprim (L := Real.log (q : ℝ))
    hL₀le hNL s hsre1 hsre2 hsim
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  refine le_trans h1 ?_
  have hc : (1 : ℝ)/4/2 + 1/4000000 ≤ (1:ℝ)/8 + (1/1000000)/4 := by norm_num
  exact mul_le_mul_of_nonneg_right hc hlogq

end Work.ZeroFreeTables.HB94
