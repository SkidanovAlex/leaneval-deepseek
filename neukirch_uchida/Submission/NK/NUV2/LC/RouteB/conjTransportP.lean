import Mathlib
import Submission.NK.NUV2.LC.conjTransport

/-!
# Route B's `p`-general conjugation transport

`Submission/Work/NUV2/LC/RouteB/decompContainment_B.lean` lists among the reusable inputs a
"`p`-general `ConjTransport` (the proved one is `p = 2`)".  The underlying result is in fact
already stated for every `p`: `NK.NUV2.LC.nontrivial_H2Profinite_conjSub`
(`Submission/Work/NUV2/LC/conjTransport.lean`, sorry-free) says that conjugation of a subgroup of
`Gal(K'/K)` preserves non-triviality of the profinite cohomology `H²(·, Z/p)` — the whole
construction (`conjLevel`, `levelConjEquiv`, the two transport maps and their round trip) is
carried out with the prime `p` as a parameter, and only the final *quantification* over `p` is
added here.

This file only records the quantified statement, so that Route B can consume it by name.
-/

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

/-- **The `p`-general conjugation transport**: for any prime `p`, any closed-free subgroup
`V ≤ Gal(K'/K)` and any `σ ∈ Gal(K'/K)`, non-triviality of `H²(V, Z/p)` is equivalent to
non-triviality of `H²(σVσ⁻¹, Z/p)`.  (Only the forward implication is stated, which is what
Route B uses; the reverse follows on replacing `σ` by `σ⁻¹`.) -/
theorem nontrivial_conjSub_p {p : ℕ} {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K))
    (h : Nontrivial (H2Profinite (K := K) (K' := K') p V)) :
    Nontrivial (H2Profinite (K := K) (K' := K') p (V.map (MulAut.conj σ).toMonoidHom)) :=
  NK.NUV2.LC.nontrivial_H2Profinite_conjSub h

/-- **Route B's `p`-general `ConjTransport`**, in the universally quantified form in which the
design file uses it. -/
def ConjTransportP : Prop :=
  ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup Gal(K'/K)) (σ : Gal(K'/K)),
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) →
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V.map (MulAut.conj σ).toMonoidHom))

/-- **`ConjTransportP` holds** (see `nontrivial_conjSub_p`). -/
theorem conjTransportP : ConjTransportP := fun K K' _ _ _ _ _ p V σ h =>
  nontrivial_conjSub_p (K := K) (K' := K') (p := p) V σ h

end NK.NUV2.LC.RouteB
