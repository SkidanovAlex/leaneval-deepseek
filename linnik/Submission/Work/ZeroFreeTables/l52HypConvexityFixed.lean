/-
# `Submission.Work.ZeroFreeTables.L52HypConvexityFixed`

The **convexity** form of Heath-Brown's Lemma 3.1 / Lemma 5.2 supply, with the numerical
constant `1/4 + 10⁻⁶` and a *single* window radius `δ`, uniformly in `ε ∈ (0,1]` and in every
non-principal character mod `q ≥ q₀`.

This is the same statement as `Work.ZeroFreeTables.l52Hyp_general_fixed` of `HBSecondAux`, but
with the constant pinned (the proof already uses `1/4 + 10⁻⁶` internally), and on a **clean
import path**: it needs only `Work.LinnikAreas.l31free.lemma3_1_free_gen` (HB Lemma 3.1,
`φ`-free form) and the convexity bound `LFunction_bound_half_of_convexity` (HB Lemma 2.5 with
`φ = 1/2`), not the (still evolving) Burgess input `l31free.hbound_third_real` that `HBSecondAux`
also imports.

The constant `1/4 + 10⁻⁶` is all that is needed by the §6 repeated-zero counting: with the
triangle test function one gets `m₁ ≤ 2·0.564 + 2·(1/4) + O(ε) = 1.628 + O(ε) < 2`.
-/
import Mathlib
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.ZeroFreeTables

private lemma three_le_of_char_ne_one_aux {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

theorem l52HypConvexityFixed : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
    χ ≠ 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ (1/4 + 1/1000000) ε δ := by
  have hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1:ℝ)/2) (by norm_num)
      (ε := 1/1000000) (by norm_num) hbound
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ1 ε hε _hε1
  intro s hs1 hs2 hs3
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hL₀le : L₀ ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hexp_le
  have hlogNle : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
    · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hχstar : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ1
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := three_le_of_char_ne_one_aux χ.primitiveCharacter hχstar
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (L := Real.log (q : ℝ)) hL₀le hlogNle s hs1 hs2 hs3
  refine hmain'.trans ?_
  have hlogq : (0:ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hε]

end Work.ZeroFreeTables
