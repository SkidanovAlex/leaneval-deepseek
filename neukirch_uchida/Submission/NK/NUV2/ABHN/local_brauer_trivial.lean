import Mathlib
import Submission.NK.NUV2.ABHN.Basic
import Submission.NK.NUV2.ABHN.muColimCardFree
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot

/-!
# The local Brauer non-vanishing in trivial `Z/p`-coefficients, from local class field theory

`NK.NUV2.LocalBrauerOdd` is the statement that for every `p`-adic field `κ` which is the
completion of a number field at a finite prime and which contains a primitive `p`-th root of
unity, the second cohomology `H²(G_κ, Z/p)` (with *trivial* `Z/p`-coefficients, in the
level-colimit form `NK.LocalCFT.LocalH2Nonvanishing`) is non-zero.

This is the local Brauer computation `Br(κ)[p] ≅ Z/p` in the `μ_p`-coefficient regime: since
`ζ_p ∈ κ` the cyclotomic twist is trivial, so the modules `μ_p` and `Z/p` coincide and the
classical Kummer/Brauer statement `H²(G_κ, μ_p) ≅ Br(κ)[p] ≅ Z/p` is *literally* the
trivial-coefficient statement.  This is the content of
`NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot` (the identification of the `μ_p`-colimit
with the trivial-coefficient profinite cohomology, valid because `ζ_p ∈ κ`) together with
`NK.NUV2.ABHN.muColimCardFree` (the local Brauer group has exactly `p` elements).

## Why this is not a formality

The colimit `H²(G_κ, Z/p) = colim_L H²(Gal(L/κ), Z/p)` is taken over the finite Galois levels
`L/κ` along the *inflation* maps, and a class of a finite level need not survive to a larger level:
the class of a cyclic level of degree `p` dies at any level carrying a `Z/p²`-quotient.  So the
statement is about the *surviving* classes (`NK.LocalCFT.SurvivingH2Class`,
`NK.LocalCFT.Brauer.localH2Nonvanishing_iff_surviving`), which is the arithmetic content of the
local Brauer computation.  Here it is produced by the fundamental class of the local class
formation: `muColimCard` computes the cardinality of the `μ_p`-colimit through the Kummer sequence
and the norm/Brauer structure of the local field.

## Relation to the request

The local reciprocity law `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` (which
`NK.NUV2.KCAll` supplies) is *not* consumed by this argument: the local Brauer computation is a
statement about the `p`-adic field `κ` itself, and the reciprocity law is what the workspace's
local class field theory chapter proves *from* it.  We therefore do not need the CFT datum here,
which also avoids a duplicate-declaration clash between a Commons module in the
`LocalReciprocityLubinTate` import closure and a Work module in the `ABHN.Basic` closure.
-/

namespace NK.NUV2.ABHN

/-- **The local Brauer non-vanishing, in trivial `Z/p`-coefficients.**

For every number field `L`, every finite prime `𝔮` of `L` and every prime `p` such that the
completion `κ = 𝔮.adicCompletion L` contains a primitive `p`-th root of unity, the group
`H²(G_κ, Z/p)` (in the level-colimit form `NK.LocalCFT.LocalH2Nonvanishing`) has a non-zero
element.

Proof: by `muColimEquivH2ProfiniteOfIsPrimitiveRoot` the `μ_p`-colimit is isomorphic to the
trivial-coefficient colimit, and `muColimCard` gives that the former has exactly `p` elements;
a type with `p ≥ 2` elements and a zero has a non-zero element. -/
theorem local_brauer_trivial (hKC : NK.NUV2.KCAll) : NK.NUV2.LocalBrauerOdd := by
  intro L _ _ 𝔮 p hp hζ
  obtain ⟨e⟩ := muColimEquivH2ProfiniteOfIsPrimitiveRoot (K := 𝔮.adicCompletion L)
    (K' := SeparableClosure (𝔮.adicCompletion L)) hp hζ
  have hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p ⊤) = p := by
    rw [← Nat.card_congr e]
    exact muColimCardFree L 𝔮 hp hζ
  haveI : Finite (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p ⊤) :=
    (Nat.card_ne_zero.mp (by rw [hcard]; exact hp.ne_zero)).2
  haveI : Fintype (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p ⊤) := Fintype.ofFinite _
  have h1 : 1 < Fintype.card (NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p ⊤) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hp.one_lt
  obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card h1
    (0 : NK.BrauerHasse.H2Profinite (K := 𝔮.adicCompletion L)
      (K' := SeparableClosure (𝔮.adicCompletion L)) p ⊤)
  exact ⟨v, hv⟩

end NK.NUV2.ABHN
