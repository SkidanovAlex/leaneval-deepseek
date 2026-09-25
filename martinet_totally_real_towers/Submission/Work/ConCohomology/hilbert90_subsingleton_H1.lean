/-
Copyright: the martinet_totally_real_towers team.

# Hilbert 90, in the form `H¹(Gal(L/K), Lˣ) = 0`

This module packages `Work.ConCohomology.hilbert90_infinite_units` -- every *locally constant*
`1`-cocycle `a : Gal(L/K) → Additive Lˣ` is a coboundary -- into the statement actually used by
the rest of the chapter:

`Subsingleton (H1 (Gal(L/K)) (Additive Lˣ))`,

i.e. the first continuous cohomology of the Galois group with coefficients in the units of the
extension is trivial.

## The argument

`H1 G M` is the quotient `Z1 G M ⧸ B1' G M` of the continuous crossed homomorphisms by the
principal ones, so it is enough to show `B1' G M = ⊤`, i.e. that every element
`z : Z1 G M` is a coboundary.  Unwinding the definitions, `z` is a `LocallyConstant G M` carrying
the proof that it is a `1`-cocycle `IsCocycle1 ⇑z` (`mem_Z1`), which is exactly the input of
`hilbert90_infinite_units`; the resulting `β : Additive Lˣ` with `⇑z = d⁰β` exhibits
`↑z = d0Hom G M β ∈ B1 G M` (`mem_B1`), and `z ∈ B1' G M` follows (`mem_B1'`).
-/

import Mathlib
import Submission.Work.ConCohomology.GaloisUnits
import Submission.Work.ConCohomology.hilbert90_infinite_units

namespace Work.ConCohomology

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Hilbert 90 for an arbitrary (possibly infinite) Galois extension, on `H¹`.**
The first continuous cohomology of `Gal(L/K)` with coefficients in the multiplicative group
`Lˣ` (written additively) is trivial. -/
theorem hilbert90_subsingleton_H1 {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] : Subsingleton (H1 (Gal(L/K)) (Additive Lˣ)) := by
  -- Every `1`-cocycle is a coboundary: `B¹ = ⊤` inside `Z¹`.
  have htop : B1' (Gal(L/K)) (Additive Lˣ) = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro z
    -- `z : Z¹` is a locally constant crossed homomorphism `Gal(L/K) → Lˣ`
    rw [mem_B1', mem_B1]
    obtain ⟨β, hβ⟩ := hilbert90_infinite_units (z : Gal(L/K) → Additive Lˣ)
      ((mem_Z1).mp z.2) z.1.isLocallyConstant
    -- `β` is the required coboundary
    refine ⟨β, LocallyConstant.ext fun σ => ?_⟩
    show d0Fun (G := Gal(L/K)) β σ = (z.1 : Gal(L/K) → Additive Lˣ) σ
    rw [← hβ]
  -- hence the quotient is a subsingleton
  rw [show H1 (Gal(L/K)) (Additive Lˣ)
        = ((Z1 (Gal(L/K)) (Additive Lˣ)) ⧸ (B1' (Gal(L/K)) (Additive Lˣ))) from rfl]
  rw [htop]
  exact QuotientAddGroup.subsingleton_quotient_top

end Work.ConCohomology
