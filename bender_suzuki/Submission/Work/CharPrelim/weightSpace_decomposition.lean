import Mathlib
import Submission.Work.CharPrelim.weightSpace_span
import Submission.Work.CharPrelim.weightSpace_indep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The weight space decomposition

This file contains the main theorem `Work.CharPrelim.weightSpace_decomposition`.  The auxiliary
material lives in the sibling modules:

* `Submission.Work.CharPrelim.weightSpace_defs`: `weightSpace` (the common eigenspace
  `V_χ = ⨅ z, ker (ρ z - χ z • 1)`), the character projection `charProj`, the character
  orthogonality relation `sum_eq_zero_of_ne_one`, restriction `restrictRep` of a representation
  to an invariant submodule, and the single-operator spectral decomposition
  `iSup_eigenspace_eq_top_of_pow_eq_one`;
* `Submission.Work.CharPrelim.weightSpace_indep`: linear independence of the weight spaces;
* `Submission.Work.CharPrelim.weightSpace_finDim` and `...weightSpace_span`: the weight spaces
  span the ambient space (finite-dimensional case, then the general case by restricting to the
  finite-dimensional invariant subspace spanned by the orbit of a vector).
-/

set_option linter.style.haveILetI false

namespace Work.CharPrelim

/-- **Weight decomposition over an algebraically closed field.**  Let `k` be an algebraically
closed field, `Z` a finite **abelian** group with `|Z|` invertible in `k`, and `ρ : Z →* End k V`
a representation of `Z` on a `k`-vector space `V`.  Then the weight spaces
`V_χ = ⨅ z, ker (ρ z - χ z • 1)` (for the characters `χ : Z →* kˣ`) are linearly independent
(`iSupIndep`) and span `V` (`⨆ χ, V_χ = ⊤`).

Proof route (the projections): for each character `χ` put
`P_χ := (|Z| : k)⁻¹ • ∑_{z : Z} (χ z : k)⁻¹ • ρ z : Module.End k V`.
Character orthogonality (`∑_{z} (χ z)⁻¹ * ψ z = if χ = ψ then |Z| else 0`, and
`∑_{χ} χ z = if z = 1 then |Z| else 0`) gives `P_χ * P_ψ = if χ = ψ then P_χ else 0` and
`∑_χ P_χ = 1`; then `V_χ = LinearMap.range (P_χ)` (the range is contained in the weight space
because each `ρ z` commutes with `P_χ` — `Z` is abelian — and `P_χ` acts as the identity on the
weight space).  The `P_χ` are orthogonal idempotents, so their ranges are independent
(`iSupIndep`) and their sum is `⊤`.  Note the sum over characters is over the (finite) type
`Z →* kˣ`. -/
theorem weightSpace_decomposition {k V Z : Type*} [Field k] [IsAlgClosed k] [CommGroup Z]
    [Finite Z] [AddCommGroup V] [Module k V] (ρ : Z →* Module.End k V)
    (hcard : IsUnit ((Nat.card Z : ℕ) : k)) :
    (⨆ (χ : Z →* kˣ), ⨅ (z : Z), LinearMap.ker ((ρ z : Module.End k V) - (χ z : k) • 1)) = ⊤ ∧
    iSupIndep (fun (χ : Z →* kˣ) =>
      ⨅ (z : Z), LinearMap.ker ((ρ z : Module.End k V) - (χ z : k) • 1)) := by
  classical
  letI := Fintype.ofFinite Z
  exact ⟨weightSpace_span ρ hcard, weightSpace_indep ρ hcard⟩

end Work.CharPrelim
