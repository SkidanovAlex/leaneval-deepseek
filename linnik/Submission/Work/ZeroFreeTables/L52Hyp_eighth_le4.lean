/-
# `L52Hyp` at the constant `1/8` for characters of order dividing `4`

Heath-Brown's Lemma 3.1 gives, with `φ = 1/4` (HB Lemma 2.5 for characters of order `≤ log q`),

`-Re (L'/L)(s,χ*) + Σ_{|1+i Im s - u| ≤ δ} Re (1/(s-u)) ≤ (1/8 + ε/4) log q`,

i.e. `L52Hyp χ (1/8) ε δ`.  This file lands that statement uniformly over **all** non-principal
`χ` modulo `q` with `χ ^ 4 = 1` (so both the real characters and the genuine quartic ones) and
all `q ≥ q₀`.

For characters of order dividing `4` the exponent-`1/4` input of HB Lemma 2.5 holds for *every*
modulus (order `≤ 4` is an absolute constant, so the order factor `(orderOf χ)^{3/(2k)}` of HB §2
is bounded — see `hbound_quarter_pow_four`, which combines `LBoundSmall_holds` for large `N` with
the convexity bound for small `N`).  Hence the threshold-uniform form of HB Lemma 3.1 restricted
to `χ ^ 4 = 1` — `Work.LinnikAreas.l31free.lemma3_1_free_q4` — applies at the conductor `N` of
`χ` with the free level `L = log q`.

The window statement `L52Hyp χ (1/8) ε δ` is expressed through `χ.primitiveCharacter`; applying
`lemma3_1_free_q4` to `χ.primitiveCharacter` at level `χ.conductor` with `L = log q` reproduces
that expression verbatim, and `Real.log (χ.conductor) ≤ Real.log q` supplies the level.
-/
import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.l31_ord
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.area1
import Submission.Work.ZeroFreeTables.XY.L52HypEighthDelta
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_q4
import Submission.Work.ZeroFreeTables.hbound_quarter_pow_four

open DirichletCharacter

namespace Work.ZeroFreeTables

theorem L52Hyp_eighth_le4 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 4 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ := by
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_q4 (φ := (1:ℝ)/4) (by norm_num)
      (ε := ε/4) (by linarith) (hbound := hbound_quarter_pow_four)
  refine ⟨δ, hδ0, hδ1, ⌈Real.exp L₀⌉₊ + 3, ?_⟩
  intro q hq _inst χ _instc hχ hχ4
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hcon : 3 ≤ χ.conductor := Work.LinnikAreas.conductor_ge_three χ hχ
  have hχ'4 : (χ.primitiveCharacter) ^ 4 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter]
    exact orderOf_dvd_iff_pow_eq_one.mpr hχ4
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
    · exact_mod_cast Nat.le_of_dvd hqpos χ.conductor_dvd_level
  have hmain' := hmain (N := χ.conductor) hcon χ.primitiveCharacter hχ'
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hχ'4
    (L := Real.log (q : ℝ)) hL₀le hlogNle
  rw [show (1:ℝ)/4/2 = 1/8 by norm_num] at hmain'
  intro s hs1 hs2 hs3
  exact hmain' s hs1 hs2 hs3

end Work.ZeroFreeTables
