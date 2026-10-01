/-
# `GlueL52` — Heath-Brown's Lemma 3.1 for real characters with `φ = 1/4`

`Work.ZeroFreeTables.GlueL52` asks for a *single* window radius `δ ≤ 1/2` and a threshold `q₀`
such that every real (`χ ^ 2 = 1`) non-principal character of conductor at least `q₀` satisfies the
`L52Hyp` bound with the sharp constant `1/8 + 10⁻⁶`, uniformly in `ε ∈ (0,1]`.

The analytic content is HB Lemma 3.1 with the exponent `φ = 1/4` (HB Lemma 2.5, Burgess), which
`Work.ZeroFreeTables.Table4.l52HypRealQuarter` already provides with a constant `c ≤ 1/8 + 10⁻⁶`
and a window radius `δ ∈ (0,1)`.  Two purely formal transfers finish the job:

* `Work.LinnikAreas.DhCapped.L52Hyp_mono` — the window sum is monotone in the radius, so the
  produced `δ ∈ (0,1)` may be *shrunk* to `min δ (1/2)`.  This is legitimate here because for a
  primitive character every zero of the completed `L`-function has real part `< 1`, so every
  window summand has non-negative sign;
* `l52Hyp_const_mono` — `L52Hyp` only weakens when the combination `c + ε/4` grows, so the source
  constant `c ≤ 1/8 + 10⁻⁶` may be replaced by `1/8 + 10⁻⁶`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono
import Submission.Work.ZeroFreeTables.Table4.HB82

namespace Work.ZeroFreeTables

open DirichletCharacter

/-- `L52Hyp` is monotone in the pair of constants `(c, ε)` along the combination `c + ε/4`: the
right-hand side `(c + ε/4) log q` only grows, and `log q ≥ 0`. -/
theorem l52Hyp_const_mono {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    {c c' ε ε' δ : ℝ} (h : c + ε / 4 ≤ c' + ε' / 4)
    (H : Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) :
    Commons.NumberTheory.Linnik.L52Hyp χ c' ε' δ := by
  intro s hs1 hs2 hs3
  refine (H s hs1 hs2 hs3).trans ?_
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  exact mul_le_mul_of_nonneg_right h hlogq

/-- **HB Lemma 3.1 with `φ = 1/4` for real characters**, in the shape required by HB Tables 2
and 3: a single window radius `δ ≤ 1/2` and threshold `q₀` serve every real non-principal
character mod `q ≥ q₀` and every slack `ε ∈ (0,1]`, with the sharp constant `1/8 + 10⁻⁶`. -/
theorem t23l52 : Work.ZeroFreeTables.GlueL52 := by
  -- HB Lemma 3.1 at a constant `c ≤ 1/8 + 10⁻⁶` with some window radius `δ < 1`.
  obtain ⟨c, _hcpos, hcle, δ₀, hδ₀pos, _hδ₀lt1, q₀, hq₀⟩ :=
    Table4.l52HypRealQuarter
  refine ⟨min δ₀ (1 / 2), lt_min hδ₀pos (by norm_num), min_le_right _ _, q₀, ?_⟩
  intro q hq _inst χ _instc hχ1 hχ2 ε hε hε1
  -- shrink the window radius `δ₀` to `min δ₀ (1/2) ≤ 1/2`
  have hδle : min δ₀ (1 / 2) ≤ δ₀ := min_le_left _ _
  have h0 : Commons.NumberTheory.Linnik.L52Hyp χ c ε (min δ₀ (1 / 2)) :=
    Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ1 hδle (hq₀ q hq χ hχ1 hχ2 ε hε hε1)
  -- replace the source constant `c ≤ 1/8 + 10⁻⁶` by the target value `1/8 + 10⁻⁶`
  exact l52Hyp_const_mono χ (by linarith) h0

end Work.ZeroFreeTables
