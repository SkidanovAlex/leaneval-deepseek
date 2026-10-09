import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- The pro-`p`-completion extends any homomorphism whose kernel contains a term of the
`p`-central filtration: if `F^(n)(ν) ≤ ker φ` then `φ` factors through the canonical map
`F^(n) → proPCompletion p n`.

Proof: `φ` factors through `FreePQuotient p n ν` by the universal property of the quotient
(`QuotientGroup.lift`, using `h`), say `φ = u ∘ mk`; then `ψ := u ∘ (proPCompletion.proj p n ν)`
satisfies `ψ ∘ canonical = u ∘ (proj p n ν) ∘ canonical = u ∘ mk = φ` by
`proPCompletion.proj_canonical`.  This is the discrete form of the universal property of the
pro-`p`-completion; the topological formulation would additionally require the extension to be
continuous, which is where the hypothesis that the kernel contains some `F^(n)(ν)` comes from. -/
theorem proPCompletion_exists_lift_of_le_ker {p n : ℕ} {P : Type*} [Group P]
    (φ : FreeGroup (Fin n) →* P) (ν : ℕ)
    (h : Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker) :
    ∃ ψ : proPCompletion p n →* P, ψ.comp (proPCompletion.canonical p n) = φ := by
  -- `φ` factors through the finite quotient `F^(n)/F^(n)(ν)` by the universal property of
  -- the quotient group.
  let u : FreePQuotient p n ν →* P := QuotientGroup.lift _ φ h
  -- Compose this factorization with the `ν`-th coordinate projection of the completion.
  refine ⟨u.comp (proPCompletion.proj p n ν), ?_⟩
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply]
  show u (proPCompletion.proj p n ν (proPCompletion.canonical p n x)) = φ x
  rw [proPCompletion.proj_canonical]
  exact QuotientGroup.lift_mk' _ h x

end Work.ProP
