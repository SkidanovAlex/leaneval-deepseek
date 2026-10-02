import Mathlib
import Submission.Work.Cohomology.Chains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The zeroth singular homology of a space is free

For any topological space `X`, the zeroth singular homology `H₀(X; ℤ)` is a free `ℤ`-module: it is
the free abelian group on the set of path components of `X`.

Mathlib computes `H₀` as the coproduct over the path components of copies of the coefficient ring,
`TopCat.singularHomology₀Iso : H₀(X;R) ≅ ∐ (fun _ : ZerothHomotopy X ↦ R)`, and a coproduct in
`ModuleCat ℤ` of free modules is the direct sum of those modules, hence free
(`ModuleCat.coprodIsoDirectSum`, `Module.Free.directSum`). Transporting `Module.Free` along the two
linear equivalences gives the result.

## Main result

* `homology_zero_free` — `H₀(X;ℤ)` is a free `ℤ`-module.
-/

set_option linter.style.haveILetI false

namespace Work.Cohomology

open CategoryTheory Limits

/-- **The zeroth singular homology of any space is free** (it is the free abelian group on the set
of path components; `.lake/packages/mathlib` has `TopCat.singularHomology₀Iso : H₀(X;R) ≅ ∐ (fun _
: ZerothHomotopy X ↦ R)`, and `Module.Free` transports across it). -/
theorem homology_zero_free (X : TopCat) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ X).homology 0) := by
  letI : DecidableEq (ZerothHomotopy X) := Classical.decEq _
  -- `H₀(X;ℤ)` is the coproduct of copies of `ℤ` indexed by the path components of `X`.
  have e : ((Work.Cohomology.singularChains ℤ X).homology 0) ≅
      ∐ (fun _ : ZerothHomotopy X ↦ ModuleCat.of ℤ ℤ) :=
    TopCat.singularHomology₀Iso X (ModuleCat.of ℤ ℤ)
  -- that coproduct is the direct sum of copies of `ℤ`, which is free
  haveI hfree : Module.Free ℤ ↥(∐ (fun _ : ZerothHomotopy X ↦ ModuleCat.of ℤ ℤ)) :=
    Module.Free.of_equiv'
      (Module.Free.directSum ℤ (fun _ : ZerothHomotopy X ↦ ℤ))
      (ModuleCat.coprodIsoDirectSum
        (fun _ : ZerothHomotopy X ↦ ModuleCat.of ℤ ℤ)).toLinearEquiv.symm
  exact Module.Free.of_equiv' hfree e.symm.toLinearEquiv

end Work.Cohomology
