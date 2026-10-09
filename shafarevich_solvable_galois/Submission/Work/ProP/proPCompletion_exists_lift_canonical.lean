import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.ProP.proPCompletion_exists_lift_of_le_ker
import Submission.Work.ProP.factors_through_freePQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- **The universal property of the pro-`p`-completion (discrete form).**  Every homomorphism
from the free group on `n` generators to a finite `p`-group extends to the pro-`p`-completion:
there is `ψ : proPCompletion p n →* P` with `ψ ∘ proPCompletion.canonical = φ`.

Proof: by the cofinality of the `p`-central filtration, there is `ν` with
`pCentralSeries p (FreeGroup (Fin n)) ν ≤ φ.ker` (apply the cofinality to the quotient
`FreeGroup (Fin n) ⧸ φ.ker ≃* φ.range`, a finite `p`-group of order `p ^ j`; or prove the
special case directly by induction on `Nat.card P` through the centre).  Then `φ` factors through
`FreePQuotient p n ν` (`QuotientGroup.lift`) and one composes with the `ν`-th coordinate
projection `proPCompletion.proj p n ν` of the completion, using
`Work.ProP.proPCompletion_exists_lift_of_le_ker` or `proPCompletion.proj_canonical` directly.

The hypothesis that `P` is a finite `p`-group is used exactly here, to produce a `ν`; a general
homomorphism out of the completion need not be determined by its restriction to the discrete free
group (for `n = 1` the completion is `ℤ_p`, which has exotic homomorphisms to `ℤ/p`). -/
theorem proPCompletion_exists_lift_canonical {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup p P) (φ : FreeGroup (Fin n) →* P) :
    ∃ ψ : proPCompletion p n →* P, ψ.comp (proPCompletion.canonical p n) = φ := by
  -- Cofinality of the `p`-central filtration: the map `φ` kills some term `F^(n)(ν)`.
  obtain ⟨ν, hν⟩ := pCentralSeries_le_ker_of_freeGroup n hP φ
  -- Hence it factors through the `ν`-th finite quotient of the completion.
  exact proPCompletion_exists_lift_of_le_ker φ ν hν

end Work.ProP
