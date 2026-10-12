import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.a0_comp_a0d_sq` — the double commutator `[a₀, (a₀†)²] = 2a₀†`

On the algebraic core `FockCore E = ℕ →₀ E` of the Fock space `Fock E = ⨁ₙ E`
the condensate ladder operators satisfy the canonical commutation relation
`a₀ a₀† = a₀† a₀ + 1` (`Defs.ccr`).  Applying it twice,

    a₀ (a₀†)² = (a₀ a₀†) a₀† = (a₀† a₀ + 1) a₀† = a₀† (a₀ a₀†) + a₀†
              = a₀† (a₀† a₀ + 1) + a₀† = (a₀†)² a₀ + 2 a₀†,

which is the identity

    `a0.comp (a0d.comp a0d) = (a0d.comp a0d).comp a0 + 2 • a0d`

recorded here.  Componentwise it reads

    `a₀ (a₀†)² Ψ n = √n (n+1) • Ψ (n-1) = ((a₀†)² a₀ Ψ) n + 2√n • Ψ (n-1)`,

i.e. the diagonal of the anti-normal monomial `a₀(a₀†)²` is shifted by `2√n`
relative to the normal-ordered one — the mechanism by which the anti-normal
ordering of FS §8 (`monoOp`) produces the lower order correction terms of the
`c`-number substitution `thm:Kaz`, here the term `2a₀†` of second degree.

The proof below is at the level of vectors: it is the pointwise form
`a₀ a₀† = a₀† a₀ + 1` of `Defs.ccr` applied to `a₀†Ψ` and then to `Ψ`.
-/

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The pointwise form of the canonical commutation relation `Defs.ccr`:
`a₀ (a₀†Ψ) = a₀† (a₀Ψ) + Ψ`. -/
lemma a0_a0d_apply (Ψ : FockCore E) : a0 (a0d Ψ) = a0d (a0 Ψ) + Ψ := by
  have := congrArg (fun (f : FockCore E →ₗ[ℂ] FockCore E) => f Ψ) (ccr (E := E))
  simpa using this

/-- **`a₀ (a₀†)² = (a₀†)² a₀ + 2 a₀†`**, i.e. `[a₀, (a₀†)²] = 2 a₀†` on the core:
the second-degree case of the anti-normal ordering rule of FS §8. -/
theorem a0_comp_a0d_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (Work.BoseB4.a0 : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E).comp
        (Work.BoseB4.a0d.comp Work.BoseB4.a0d)
      = (Work.BoseB4.a0d.comp Work.BoseB4.a0d).comp Work.BoseB4.a0
        + (2 : ℂ) • (Work.BoseB4.a0d : Work.BoseB4.FockCore E →ₗ[ℂ] Work.BoseB4.FockCore E) := by
  refine LinearMap.ext fun Ψ => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [a0_a0d_apply (a0d Ψ), a0_a0d_apply Ψ, map_add]
  rw [two_smul]
  abel

end Work.BoseB4
