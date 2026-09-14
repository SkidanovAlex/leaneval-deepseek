import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace Commons.LinearAlgebra.Independence

/- If a family of elements of a submodule is linearly independent when viewed in the ambient
module, then it is linearly independent inside the submodule.  Mathlib-only, generic over any
ring/module.

PROOF: a linear relation in P over R, `Σ i, c i • v i = 0` (the module operation inside P),
coerces to the same relation in M, `Σ i, c i • ((v i : P) : M) = 0`, because the inclusion
`P → M` is R-linear (Submodule.subtype) and `Submodule.map_sum`/`map_smul`-style facts push
sums and scalar multiples through.  Then use the ambient independence hypothesis.
Alternatively use the basis-free `LinearIndependent` machinery with Fintype sums over the
support.  Notes: `Submodule.subtype` is R-linear; `(v i : P)` coerces to `M` via the subtype
inclusion; the R-action on P agrees with the R-action on M for these elements.
Keep the statement exactly as given (same binder names/types). -/
theorem linearIndependent_of_ambient {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (P : Submodule R M) {ι : Type*} (v : ι → P)
    (h : LinearIndependent R (fun i : ι => ((v i : P) : M))) : LinearIndependent R v := by
  -- The ambient family is the image of `v` under the R-linear inclusion
  -- `P.subtype : P →ₗ[R] M` (the coercion `↑(v i)` is defeq to `P.subtype (v i)`).
  -- `LinearIndependent.of_comp` states that if the image of a family under a linear map is
  -- linearly independent, then so is the original family.
  exact LinearIndependent.of_comp P.subtype h

end Commons.LinearAlgebra.Independence