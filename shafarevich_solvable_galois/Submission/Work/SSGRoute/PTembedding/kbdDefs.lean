import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.NK.FrobeniusBridge.Basic
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for the base case of local duality: the local field of a finite place

The local input `kummerBaseDim` compares the `𝔽_p`-dimension of the local `H¹` at a finite place
`A` of `Ω` over `k` with trivial coefficients and with coefficients in `μ_p`.  The arithmetic
content of that comparison lives at the completion `k_𝔭` of `k` at the prime `𝔭` below `A`, and is
read off from the absolute Galois group of that completion.

This file exposes the vocabulary in which the arithmetic pieces are stated:

* `localFieldOf k A hA = k_𝔭`, the `𝔭`-adic completion of `k` with `𝔭` the prime of `k` below `A`
  (a re-export of `NK.FrobeniusBridge.localField`);
* `localClosureOf k A hA = k̄_𝔭 = SeparableClosure k_𝔭`;
* `localGalOf k A hA = Gal(k̄_𝔭/k_𝔭)`.

Nothing here is arithmetic: all three are definitions.
-/

open scoped Pointwise

namespace Work.SSGRoute.PTembedding

/-- **The local field of a finite place** `A` of `Ω` over `k`: the completion `k_𝔭` of `k` at the
prime `𝔭` of `k` below `A`. -/
noncomputable abbrev localFieldOf (k : Type) [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type :=
  NK.FrobeniusBridge.localField (K := k) (K' := Ω) ⟨A, hA⟩

/-- **The local closure at a finite place**: the separable closure `k̄_𝔭` of the completion `k_𝔭`. -/
noncomputable abbrev localClosureOf (k : Type) [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type :=
  SeparableClosure (localFieldOf k A hA)

/-- **The local absolute Galois group** `Gal(k̄_𝔭/k_𝔭)` of a finite place, with the Krull topology
of `NK.FrobeniusBridge` (the same convention as the rest of the local lane). -/
noncomputable abbrev localGalOf (k : Type) [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : Type :=
  localClosureOf k A hA ≃ₐ[localFieldOf k A hA] localClosureOf k A hA

end Work.SSGRoute.PTembedding
