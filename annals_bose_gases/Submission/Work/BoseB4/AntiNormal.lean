import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.MonoOp
import Submission.Work.BoseB4.a0dpow_comp_a0pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.AntiNormal` — putting FS-shaped terms into anti-normal form

The operators of FS `eq:HLambdaSecond` have the shape

    `(a₀†)^q (lift B) (a₀)^p`    (`q` creations on the left, `p` annihilations on the
                                  right, one spectator operator `B` in the middle),

e.g. `a₀† a_k† a_k a₀` (FS's `∫ Ŵ₁ a_k†a_k` term) or `a₀†a₀ a_k† a₀` (FS's `χ̂_Λ`
term).  The `c`-number substitution (`Work.BoseB4.Kafz_sum`) applies to the
**anti-normal** form `a₀^p (a₀†)^q (lift B)` instead, so the two forms have to be
related.  Since `lift B` commutes with `a₀` (`Work.BoseB4.lift_comm_a0`) and with
`a₀†` (`Work.BoseB4.lift_comm_a0d`),

    `(a₀†)^q (lift B) (a₀)^p = ((a₀†)^q (a₀)^p) (lift B)`,

and the Wick expansion `Work.BoseB4.a0dpow_comp_a0pow`

    `(a₀†)^q (a₀)^p = ∑_{k≤min(p,q)} (−1)^k k! C(p,k) C(q,k) (a₀)^{p−k} (a₀†)^{q−k}`

turns the result into a finite sum of anti-normal monomials
`monoOp (p−k) (q−k) B`.  The two lemmas of this file are that statement in operator
form (`a0dpow_comp_lift_comp_a0pow`) and its symbol form
(`symbol_antiNormal`), which is the input of `Work.BoseB4.Kafz_sum` /
`Work.BoseB4.Kafz_lower_bound`.

The sign is the one forced by `[a₀, a₀†] = 1` (FS `eq:subst-z`): with
`(a₀†)a₀ = a₀a₀† − 1`, the expansion of `(a₀†)^q a₀^p` has alternating signs.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A spectator operator commutes with the powers of condensate annihilation. -/
lemma lift_comp_a0pow (B : E →ₗ[ℂ] E) (p : ℕ) :
    (lift B).comp (a0pow p) = (a0pow p).comp (lift B) := by
  induction p with
  | zero => ext x; simp
  | succ d ih =>
    rw [a0pow_succ, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, lift_comm_a0,
      ← LinearMap.comp_assoc, ← a0pow_succ]

/-- **FS-shaped terms in anti-normal form.**  With
`c_k = (−1)^k k! C(p,k) C(q,k)`,

    `(a₀†)^q (lift B) (a₀)^p = ∑_{k≤p} c_k · monoOp (p−k) (q−k) B`,

a finite sum of anti-normal monomials — the shape consumed by the `c`-number
substitution `Work.BoseB4.Kafz_sum`. -/
theorem a0dpow_comp_lift_comp_a0pow (p q : ℕ) (B : E →ₗ[ℂ] E) :
    ((a0dpow q : FockCore E →ₗ[ℂ] FockCore E)).comp ((lift B).comp (a0pow p))
      = ∑ k ∈ Finset.range (p + 1),
          (((-1 : ℂ) ^ k) * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
              * ((q.choose k : ℕ) : ℂ)) • monoOp (p - k) (q - k) B := by
  rw [lift_comp_a0pow B p, ← LinearMap.comp_assoc, a0dpow_comp_a0pow p q]
  refine LinearMap.ext fun Ψ => ?_
  rw [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, monoOp]

/-- The **symbol** of an FS-shaped term, i.e. the right-hand side of FS
`eq:subst-z` for the operator `(a₀†)^q (lift B) (a₀)^p`:

    `z ⟼ ∑_{k≤p} (−1)^k k! C(p,k) C(q,k) · (z^{p−k} z̄^{q−k}) • B`. -/
theorem symbol_antiNormal (p q : ℕ) (B : E →ₗ[ℂ] E) (z : ℂ) :
    (∑ k ∈ Finset.range (p + 1),
        symbol (p - k) (q - k)
          ((((-1 : ℂ) ^ k) * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
              * ((q.choose k : ℕ) : ℂ)) • B) z)
      = ∑ k ∈ Finset.range (p + 1),
          ((((-1 : ℂ) ^ k) * ((k.factorial : ℕ) : ℂ) * ((p.choose k : ℕ) : ℂ)
              * ((q.choose k : ℕ) : ℂ))
            * (z ^ (p - k) * (starRingEnd ℂ z) ^ (q - k))) • B := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [symbol_smul, symbol, smul_smul]

end Work.BoseB4
