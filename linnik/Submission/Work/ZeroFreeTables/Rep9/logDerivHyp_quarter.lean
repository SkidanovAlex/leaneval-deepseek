/-
# `Work.ZeroFreeTables.Rep9.logDerivHyp_quarter`

The log-derivative input of the `P₃` engine of HB §9 (Heath-Brown 1992, Lemma 3.1) at the
constant `c = 1/4 + e`, i.e. with the exponent `φ = 1/2` of HB Lemma 2.5 and error `ε = e`:
`(-Re L'/L)(s) + Σ_{near} Re(1/(s-ρ)) ≤ (1/4 + e)·L` on the region
`1 + 1/(L log L) ≤ Re s ≤ 1 + log L/L`, `|Im s| ≤ L`, whenever `L ≥ log N`.

The point of the constant `1/4` is that `φ = 1/2` is the *convexity* (Phragmén–Lindelöf) exponent
for `L(σ+it,χ)`, so no Burgess input is needed: `Work.LinnikAreas.l31free.lemma3_1_free_gen`
(HB Lemma 3.1 with the exponent `φ` free and the scale `L ≥ log N` free) applied to the
`φ = 1/2` L-function bound `Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity`
produces the statement for *every* non-principal primitive character.  The remaining work is the
transport: `3 ≤ N` from `χ ≠ 1`, and `|Im s| ≤ L → |Im s| ≤ 10L`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen
import Submission.Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity

open DirichletCharacter

namespace Work.ZeroFreeTables.Rep9

/-- A non-principal Dirichlet character has level at least `3`. -/
private lemma three_le_of_char_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : 3 ≤ N := by
  by_contra h
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
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

theorem logDerivHyp_quarter {e : ℝ} (he : 0 < e) :
    ∃ L₀ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
      (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {L : ℝ}, L₀ ≤ L → Real.log (N:ℝ) ≤ L →
      Work.ZeroFreeTables.LogDerivHyp χ δ L (1/4 + e) := by
  -- HB Lemma 2.5 at `φ = 1/2`, from convexity: valid for every non-principal character.
  have hbound : ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
            ≤ Cb * (N:ℝ) ^ (((1:ℝ)/2) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|) :=
    fun k hk ε' hε' => Work.LinnikAreas.l31free.LFunction_bound_half_of_convexity hε' k hk
  -- HB Lemma 3.1 with `φ = 1/2`, error `e` and the free scale `L ≥ log N`.
  obtain ⟨L₀, δ, hδ0, hδ1, hmain⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := (1:ℝ)/2) (by norm_num) (ε := e) he hbound
  refine ⟨L₀, δ, hδ0, hδ1, ?_⟩
  intro N _inst χ hχ hprim L hL hlogN
  have hN3 : 3 ≤ N := three_le_of_char_ne_one χ hχ
  have hlogNnn : 0 ≤ Real.log (N:ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hLnn : 0 ≤ L := le_trans hlogNnn hlogN
  intro s hs1 hs2 hs3
  have key := hmain hN3 χ hχ hprim hL hlogN s hs1 hs2 (le_trans hs3 (by linarith))
  have hc : (1:ℝ)/2/2 + e = 1/4 + e := by norm_num
  rw [hc] at key
  exact key

end Work.ZeroFreeTables.Rep9
