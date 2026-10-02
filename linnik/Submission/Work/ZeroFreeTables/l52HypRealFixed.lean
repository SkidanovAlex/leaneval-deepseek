import Mathlib
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Work.LinnikAreas.l31free.hbound_third_real
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi

namespace Work.ZeroFreeTables

open DirichletCharacter

/-- A non-principal character has level at least `3` (for `N ≤ 2` the unit group is trivial, so
every character is principal). -/
private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN2 : N ≤ 2 := by omega
  have hχne : ¬ (∀ a : (ZMod N)ˣ, χ ↑a = (1 : DirichletCharacter ℂ N) ↑a) := by
    intro hh
    exact hχ (MulChar.ext hh)
  push Not at hχne
  rcases hχne with ⟨a, hne⟩
  have hs : Subsingleton (ZMod N)ˣ := by
    interval_cases N <;> infer_instance
  have ha : a = 1 := Subsingleton.elim a 1
  subst a
  simp at hne

/-- For a real character the primitive character inducing it is again real. -/
private lemma primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
      (χ.primitiveCharacter ^ 2) = 1 := by
    rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h]
  exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
    (by rw [hmap, DirichletCharacter.changeLevel_one])

/-- **The `L52Hyp` hypothesis of Heath-Brown's Lemma 5.2 with the numerical constant
`1/6 + 10⁻⁶` and a single window radius `δ`, uniformly in `ε ∈ (0,1]` and in all real
non-principal characters.**

This is the hypothesis required by Lemma 5.2 of Heath-Brown (1992).  It is obtained from
HB Lemma 3.1 in its restricted real-character form
(`Work.LinnikAreas.l31free.lemma3_1_free_gen_real`, with `φ = 1/3`), whose input is the
near-`1` `L`-function bound `Work.LinnikAreas.l31free.hbound_third_real` (HB Lemma 2.5 for
real characters, from the cube-free-moduli Burgess character-sum bound).  The slack
`ε = 10⁻⁶` inside Lemma 3.1 is fixed, so a single `δ` serves every `ε ∈ (0,1]`: the
statement's own `ε` enters only additively in `(c + ε/4) log q`. -/
theorem l52HypRealFixed : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 2 = 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ (1/6 + 1/1000000) ε δ := by
  -- HB Lemma 2.5 with exponent `φ = 1/3` for real characters.
  have hBurg : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/3) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => Work.LinnikAreas.l31free.hbound_third_real hε' k hk
  -- HB Lemma 3.1 (threshold-uniform form) with the *fixed* slack `ε = 1/1000000`.
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen_real (φ := (1:ℝ)/3) (by norm_num)
      (ε := 1/1000000) (by norm_num) hBurg
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ1 hχ2 ε hε _hε1 s hs1 hs2 hs3
  -- thresholds coming from `q₀ = ⌈exp L₀⌉₊ + 3 ≤ q`
  have hexp_le : Real.exp L₀ ≤ (q : ℝ) := by
    have h1 : Real.exp L₀ ≤ (⌈Real.exp L₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp L₀⌉₊ : ℝ) ≤ ((⌈Real.exp L₀⌉₊ + 3 : ℕ) : ℝ) := by
      push_cast; linarith
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
  have hcon : 3 ≤ χ.conductor := three_le_of_char_ne_one χ.primitiveCharacter hχstar
  -- instantiate HB Lemma 3.1 at the primitive character inducing `χ`, with `L = log q`
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχstar
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) (primitiveCharacter_sq_one χ hχ2)
    (L := Real.log (q : ℝ)) hL₀le hlogNle s hs1 hs2 hs3
  refine hmain'.trans ?_
  have hlogq : (0:ℝ) ≤ Real.log (q : ℝ) := by
    refine Real.log_nonneg ?_
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast hq1
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith only [hε]

end Work.ZeroFreeTables
