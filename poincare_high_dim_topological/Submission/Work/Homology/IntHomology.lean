import Mathlib

/-! Local copy (lead) of the aspherical challenge definition used by the ported Homology library.
In the poincare workspace there is no ChallengeDeps; this file stands in for it. -/

namespace LeanEval
namespace Topology
open CategoryTheory AlgebraicTopology

/-- `Hₖ(X; ℤ)`, the `k`-th singular homology with integer coefficients. -/
noncomputable def intHomology (k : ℕ) (X : TopCat) : ModuleCat ℤ :=
  ((singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj X

end Topology
end LeanEval
