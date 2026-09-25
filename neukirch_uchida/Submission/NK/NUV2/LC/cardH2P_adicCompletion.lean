import Mathlib
import Submission.NK.NUV2.ABHN.muColimCardFree
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.NUV2.LC.h2CardTransport
import Submission.NK.NUV2.LC.LeafInputs

/-!
# The local Brauer cardinality `|H²(G_κ, Z/p)| = p` at an arbitrary prime `p` with `ζ_p ∈ κ`

`NK.NUV2.LC.cardGlobalTwo_of_hkc` proves `Nat.card (H²(U, Z/2)) = 2` for a closed subgroup
`U ≤ Gal(K'/K)` continuously isomorphic to the absolute Galois group of a `p`-adic field
`κ = 𝔮.adicCompletion L` — the case `p = 2` of the local computation, where the cyclotomic
coefficient module `μ_2` is automatically trivial.

The present file isolates the *general* prime: if `κ` contains a primitive `p`-th root of unity (the
hypothesis under which the coefficient module `μ_p` *is* the trivial module `Z/p` on the levels),
then `H²(U, Z/p)` has exactly `p` elements.  This is the local input `(L0)` of the route-B design
(`Submission/Work/NUV2/LC/RouteB/decompContainment_B.lean`), which works at an **odd** prime `p`
with `ζ_p` fixed (so that the archimedean places contribute nothing).

The proof is a repackaging of three on-disk results:

* `NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot` — for `ζ_p ∈ κ`, the `μ_p`-colimit and
  the trivial-coefficient profinite cohomology `H²(G_κ, Z/p)` are equivalent;
* `NK.NUV2.ABHN.muColimCardFree` — the `μ_p`-colimit has `p` elements (Kummer + the local
  fundamental class);
* `NK.NUV2.LC.h2CardTransport` — the cardinality is transported along the continuous labelling
  `U ≃ₜ* Gal(κ'/κ)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace NK.NUV2.LC

/-- **The local Brauer group of a `p`-adic field at the prime `p`, when `ζ_p` is present.**
For a number field `K` and a finite prime `𝔮`, if the completion `κ = 𝔮.adicCompletion K` contains a
primitive `p`-th root of unity, then `H²(G_κ, Z/p)` has exactly `p` elements — the `μ_p`-Kummer
description of the `p`-torsion of `Br(κ) ≅ ℚ/ℤ`. -/
theorem card_h2P_top_adicCompletion (K : Type) [Field K] [NumberField K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hζ : ∃ ζ : 𝔮.adicCompletion K, IsPrimitiveRoot ζ p) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion K)
      (K' := SeparableClosure (𝔮.adicCompletion K)) p ⊤) = p := by
  obtain ⟨e⟩ := NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
    (K := 𝔮.adicCompletion K) (K' := SeparableClosure (𝔮.adicCompletion K)) hp hζ
  rw [← Nat.card_congr e]
  exact NK.NUV2.ABHN.muColimCardFree K 𝔮 hp hζ

/-- **The labelled form of the local Brauer computation.**  Let `U ≤ Gal(K'/K)` be a closed subgroup
continuously isomorphic to the absolute Galois group of a `p`-adic field `κ = 𝔮.adicCompletion L`
with `ζ_p ∈ κ`.  Then `H²(U, Z/p)` has `p` elements.

This is `NK.NUV2.LC.CardGlobalTwo` with `2` replaced by an arbitrary prime `p` (and the
hypothesis `ζ_p ∈ κ` that makes the coefficients trivial). -/
theorem card_h2P_of_homeomorph {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p : ℕ}
    (hp : p.Prime) (hζ : ∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p)
    (U : Subgroup Gal(K'/K)) (hU : IsClosed (U : Set Gal(K'/K)))
    (e : ↥U ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) = p := by
  rw [NK.NUV2.LC.h2CardTransport p K K' (𝔮.adicCompletion L)
    (SeparableClosure (𝔮.adicCompletion L)) U hU e]
  exact card_h2P_top_adicCompletion L 𝔮 hp hζ

end NK.NUV2.LC
