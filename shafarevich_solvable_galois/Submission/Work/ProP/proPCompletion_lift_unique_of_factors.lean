import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- `proj p n ν ∘ canonical = freePQuotientMk p n ν`. -/
theorem proj_comp_canonical (p n ν : ℕ) :
    (proPCompletion.proj p n ν).comp (proPCompletion.canonical p n) =
      freePQuotientMk p n ν := by
  ext x
  rw [MonoidHom.comp_apply, proPCompletion.proj_canonical]

/-- Uniqueness of the extension of a homomorphism from `F^(n)` to a homomorphism out of the
pro-`p`-completion, among maps that factor through one fixed finite quotient.  If
`ψ₁ = u₁ ∘ p_ν` and `ψ₂ = u₂ ∘ p_ν` (where `p_ν = proPCompletion.proj p n ν` is the `ν`-th
coordinate projection) agree after composition with the canonical map
`ι = proPCompletion.canonical`, then `ψ₁ = ψ₂`.

Proof: `u₁ ∘ p_ν ∘ ι = u₂ ∘ p_ν ∘ ι`; since `p_ν ∘ ι = freePQuotientMk p n ν`
(`proPCompletion.proj_canonical`) and `freePQuotientMk` is surjective
(`freePQuotientMk_surjective`), conclude `u₁ = u₂`.
(Without the factorisation hypothesis, uniqueness fails: the pro-`p`-completion is much larger
than the discrete free group — for `n = 1` it is `ℤ_p`, where there are exotic homomorphisms
`ℤ_p → ℤ/p` — so only the continuous maps, i.e. those factoring through a finite stage, are
determined by their restriction to `F^(n)`.) -/
theorem proPCompletion_lift_unique_of_factors {p n : ℕ} {P : Type*} [Group P] (ν : ℕ)
    {ψ₁ ψ₂ : proPCompletion p n →* P} {u₁ u₂ : FreePQuotient p n ν →* P}
    (h₁ : ψ₁ = u₁.comp (proPCompletion.proj p n ν))
    (h₂ : ψ₂ = u₂.comp (proPCompletion.proj p n ν))
    (h : ψ₁.comp (proPCompletion.canonical p n) = ψ₂.comp (proPCompletion.canonical p n)) :
    ψ₁ = ψ₂ := by
  rw [h₁, h₂, MonoidHom.comp_assoc, MonoidHom.comp_assoc,
    proj_comp_canonical p n ν] at h
  have huu : u₁ = u₂ := by
    apply MonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := freePQuotientMk_surjective p n ν y
    exact congrFun (congrArg DFunLike.coe h) x
  rw [h₁, h₂, huu]

end Work.ProP
