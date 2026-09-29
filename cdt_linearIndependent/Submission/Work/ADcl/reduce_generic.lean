import Mathlib
import Submission.Work.ADcl.asym_setup
import Submission.Work.CDcl.xrel_defs

namespace Work.ADcl

/-! Guidance (area ADcl of `cdt_linearIndependent`).  This file should be in `namespace Work.ADcl`.

In `LF = ℚ((x)) = Frac ℚ⟦x⟧` (`Work.CDcl.LF`) with derivation `dL` and the `y`-derivative
`Work.CDcl.Aop f = ρ · dL f` (`ρ = dx/dy = Work.CDcl.rhoL = toL rhoK`), let `f` satisfy the
order-two inhomogeneous ODE `f'' = α·f' + β·f + γ` with `α = aa, β = bb, γ = gg ∈ ℚ(x)`
(hypothesis `hf`).  `Work.ADcl.seqOf aa bb gg : ℕ → ℚ(x) × ℚ(x) × ℚ(x)` is defined by
`seqOf aa bb gg 0 = (1,0,0)` and, writing `(a_k, b_k, d_k) = seqOf aa bb gg k`,
`a_{k+1} = ρ·(a_k' + b_k·β)`, `b_{k+1} = ρ·(a_k + b_k' + b_k·α)`,
`d_{k+1} = ρ·(d_k' + b_k·γ)` (all derivatives `dRat`).

**Claim**: `Aop^k f = a_k·f + b_k·f' + d_k` for every `k` (all in `LF`, `toL a_k` etc. as
scalars, `f' = dL f`).

Route: induction on `k`.  Step: from the induction hypothesis,
`Aop (a_k f + b_k f' + d_k) = ρ·((a_k' + b_k β) f + (a_k + b_k' + b_k α) f' + (d_k' + b_k γ))`
using `Aop g = rhoL * dL g` (`Work.CDcl.Aop`), additivity of `Aop`, the Leibniz rule
`Work.CDcl.dL_toL_mul : dL (toL c * x) = toL (dRat c) * x + toL c * dL x` (and
`Work.CDcl.dL_toL`, `dL_mul`), and the ODE `hf` to replace `dL (dL f)`.  You will need
`rhoL = toL rhoK` (`rfl`) and `toL_mul`.  Nothing about the specific ODE of `H` is used, so this
statement is completely general. -/

noncomputable section

/-! ## Two elementary facts about `Aop = ρ·d/dx` -/

/-- `Aop` is additive (`Aop g = ρ · g'`). -/
theorem Aop_add' (x y : Work.CDcl.LF) :
    Work.CDcl.Aop (x + y) = Work.CDcl.Aop x + Work.CDcl.Aop y := by
  simp only [Work.CDcl.Aop, Work.CDcl.dL_add, mul_add]

/-- `Aop` of a `ℚ(x)`-multiple of an element: the Leibniz rule for the `x`-derivation. -/
theorem Aop_toL_mul' (c : RatFunc ℚ) (x : Work.CDcl.LF) :
    Work.CDcl.Aop (Work.CDcl.toL c * x)
      = Work.CDcl.toL (Work.CDcl.rhoK * Submission.CDT.dRat c) * x
        + Work.CDcl.toL c * Work.CDcl.Aop x := by
  rw [Work.CDcl.Aop, Work.CDcl.dL_toL_mul]
  have h : Work.CDcl.rhoL * (Work.CDcl.toL (Submission.CDT.dRat c) * x
        + Work.CDcl.toL c * Work.CDcl.dL x)
      = (Work.CDcl.rhoL * Work.CDcl.toL (Submission.CDT.dRat c)) * x
        + Work.CDcl.toL c * (Work.CDcl.rhoL * Work.CDcl.dL x) := by ring
  rw [h, ← Work.CDcl.Aop]
  simp only [Work.CDcl.rhoL, ← Work.CDcl.toL_mul]

/-- `Aop` of a `ℚ(x)`-constant. -/
theorem Aop_toL' (c : RatFunc ℚ) :
    Work.CDcl.Aop (Work.CDcl.toL c)
      = Work.CDcl.toL (Work.CDcl.rhoK * Submission.CDT.dRat c) := by
  rw [Work.CDcl.Aop, Work.CDcl.dL_toL]
  simp only [Work.CDcl.rhoL, ← Work.CDcl.toL_mul]

/-- `Aop` of `dL f`, using the order-two ODE `f'' = α f' + β f + γ` (as `hf`). -/
theorem Aop_dL_of_ode (f : Work.CDcl.LF) (aa bb gg : RatFunc ℚ)
    (hf : Work.CDcl.dL (Work.CDcl.dL f)
      = Work.CDcl.toL aa * Work.CDcl.dL f + Work.CDcl.toL bb * f + Work.CDcl.toL gg) :
    Work.CDcl.Aop (Work.CDcl.dL f)
      = Work.CDcl.toL (Work.CDcl.rhoK * bb) * f
        + Work.CDcl.toL (Work.CDcl.rhoK * aa) * Work.CDcl.dL f
        + Work.CDcl.toL (Work.CDcl.rhoK * gg) := by
  simp only [Work.CDcl.Aop, hf, Work.CDcl.rhoL, map_mul]
  ring

/-- **The induction step of `reduce_generic`**, in general form: applying `Aop` to
`a·f + b·f' + d` produces again a combination of `f`, `f'` and `1`, with coefficients given by
the recursion defining `seqOf`. -/
theorem Aop_comb (f : Work.CDcl.LF) (aa bb gg : RatFunc ℚ)
    (hf : Work.CDcl.dL (Work.CDcl.dL f)
      = Work.CDcl.toL aa * Work.CDcl.dL f + Work.CDcl.toL bb * f + Work.CDcl.toL gg)
    (a b d : RatFunc ℚ) :
    Work.CDcl.Aop (Work.CDcl.toL a * f + Work.CDcl.toL b * Work.CDcl.dL f + Work.CDcl.toL d)
      = Work.CDcl.toL (Work.CDcl.rhoK * (Submission.CDT.dRat a + b * bb)) * f
        + Work.CDcl.toL (Work.CDcl.rhoK * (a + Submission.CDT.dRat b + b * aa))
            * Work.CDcl.dL f
        + Work.CDcl.toL (Work.CDcl.rhoK * (Submission.CDT.dRat d + b * gg)) := by
  have hAopf : Work.CDcl.Aop f = Work.CDcl.toL Work.CDcl.rhoK * Work.CDcl.dL f := by
    simp only [Work.CDcl.Aop, Work.CDcl.rhoL]
  rw [Aop_add', Aop_add', Aop_toL_mul', Aop_toL_mul', Aop_toL', hAopf,
    Aop_dL_of_ode f aa bb gg hf]
  simp only [map_mul, map_add]
  ring

theorem reduce_generic (f : Work.CDcl.LF) (aa bb gg : RatFunc ℚ)
    (hf : Work.CDcl.dL (Work.CDcl.dL f)
      = Work.CDcl.toL aa * Work.CDcl.dL f + Work.CDcl.toL bb * f + Work.CDcl.toL gg)
    (k : ℕ) :
    Work.CDcl.Aop^[k] f = Work.CDcl.toL (Work.ADcl.seqOf aa bb gg k).1 * f
      + Work.CDcl.toL (Work.ADcl.seqOf aa bb gg k).2.1 * Work.CDcl.dL f
      + Work.CDcl.toL (Work.ADcl.seqOf aa bb gg k).2.2 := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, seqOf, Work.CDcl.toL_one, Work.CDcl.toL_zero]
      ring
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [Aop_comb f aa bb gg hf (seqOf aa bb gg k).1 (seqOf aa bb gg k).2.1
        (seqOf aa bb gg k).2.2]
      simp only [seqOf]

end

end Work.ADcl
