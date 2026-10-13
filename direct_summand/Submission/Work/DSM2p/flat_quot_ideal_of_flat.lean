import Mathlib

/-!
# Flatness of `S ⧸ IS` over `R ⧸ I` when `S` is flat over `R`

Let `R → S` be a ring homomorphism and `I ⊆ R` an ideal.  If `S` is flat as an `R`-module then
`S ⧸ IS` is flat as an `R ⧸ I`-module, where `IS = Ideal.map (algebraMap R S) I`.

This is the standard fact that flatness is preserved by base change, applied to the base change
`R → R ⧸ I`: the canonical comparison map is an `R ⧸ I`-algebra isomorphism
`S ⧸ IS ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] S`
(`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`), which identifies `S ⧸ IS` with the base
change `(R ⧸ I) ⊗[R] S` of the flat module `S`; base change of a flat module is flat
(`Module.Flat.baseChange`).
-/

set_option linter.style.haveILetI false

namespace Work.DSM2p

open TensorProduct

/-- If `S` is a flat `R`-module and `I ⊆ R` is an ideal, then `S ⧸ IS` is flat over `R ⧸ I`. -/
theorem flat_quot_ideal_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (h : Module.Flat R S) :
    Module.Flat (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I) := by
  -- Regard the hypothesis as an instance so that typeclass search can use it.
  haveI : Module.Flat R S := h
  -- Base change of a flat module is flat: `(R ⧸ I) ⊗[R] S` is flat over `R ⧸ I`.
  haveI : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] S) := Module.Flat.baseChange R (R ⧸ I) S
  -- `S ⧸ IS` is `R ⧸ I`-isomorphic to the base change `(R ⧸ I) ⊗[R] S`.
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv

end Work.DSM2p
