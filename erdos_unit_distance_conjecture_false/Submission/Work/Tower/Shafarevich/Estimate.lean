import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Shafarevich.Defs

/-!
# Shafarevich's relation-rank estimate: the arithmetic input

This file isolates the arithmetic content of Shafarevich's relation-rank estimate (paper
Proposition 3.5 / A.10) in the cohomological form in which it enters the tower construction, and
records precisely what remains to be proved.

## The mathematics

Let `F` be a number field and `K/F` a finite, everywhere-unramified Galois extension with group
`Γ = Gal(K/F)`.  Shafarevich's theorem (Shafarevich, *Extensions with given points of
ramification*, 1963; see also Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter X
§10, and Koch, *Galois theory of p-extensions*, Chapter 11) bounds the **relation rank** of the
maximal unramified pro-`p` group.  Writing `d = dim_{𝔽_p} H¹` and `r = dim_{𝔽_p} H²`, for
`G = Gal(F^{ur,p}/F)` and `S = ∅` (unramified everywhere) with `p` odd one has

`r(G) ≤ d(G) + (r₁ + r₂ - 1 + θ)`,

where `r₁, r₂` are the numbers of real and complex places of `F` and `θ = 1` iff `ζ_p ∈ F`
(otherwise `0`).  For totally real cubic `F` and `p = 3` this is `r(G) ≤ d(G) + 2`.  (See
D. C. Mayer's survey *Recent progress in determining p-class field towers*, Theorem 1.1, which
states the same bound as `ρ ≤ d₂G_S ≤ ρ + r + θ` with `ρ` the `p`-class rank and
`r = r₁ + r₂ - 1` the torsion-free Dirichlet unit rank.)

For a finite level `K` of the tower which is **maximal** among the everywhere-unramified Galois
`3`-extensions in which a finite set `T` of primes splits completely, `Γ = Gal(K/F)` is a quotient
of `G` by the normal closure of the `|T|` Frobenius elements at the primes of `T` (conjugacy
classes, and hence `|T|` normal generators).  Adding `|T|` relations gives

`r(Γ) ≤ r(G) + |T| ≤ d(Γ) + C₀ + |T|`,

which is the inequality required by the tower construction (`Work.Tower.shafarevich_relation_bound`).

## What is formalised here

Only the *statement* of this arithmetic input (`H2Estimate`).

The proof of `H2Estimate` is the deepest missing input of the whole project.  It needs

* global class field theory for the everywhere-unramified extension `K/F` (the Artin map, the
  fundamental class, Hilbert's theorem 94, the norm-index theorem) — not in Mathlib;
* the cohomology of the unit group `𝒪_K^×` and the ambiguous class number formula
  (Herbrand quotients, Dirichlet's unit theorem, Hilbert 90);
* the Schur-multiplier identity `dim H²(Γ, 𝔽_p) = d(Γ) + dim (H₂(Γ, ℤ) ⊗ 𝔽_p)` (Swan; Hopf's
  formula).

**The invariant mismatch.**  `H2Estimate` bounds `dim_{𝔽_p} H²(Γ, 𝔽_p)`, the *pro-`p` relation
rank* of `Γ` (`Work.Tower.Shafarevich.proPRelationRank`).  The deliverable
`Work.Tower.shafarevich_relation_bound` is phrased with the *abstract* relation rank
`Work.Tower.relationRankWith Γ (generatorRank Γ)`.  For a finite `p`-group one always has

`dim_{𝔽_p} H²(Γ, 𝔽_p) ≤ relationRankWith Γ (generatorRank Γ)`,

with equality exactly when `Γ` is **efficient**; whether every finite `p`-group is efficient is
Mann's Question 18 (Kourovka notebook), open.  Thus `H2Estimate` does **not** by itself bound the
abstract relation rank from above: the deliverable as literally stated additionally requires the
efficiency of the finite `3`-groups `Gal(K/F)`.  See `Work.Tower.Shafarevich.Main` and Gardam,
*Finite groups of arbitrary deficiency*, arXiv:1705.02040, inequality (⋆).

A note on the role of maximality: the estimate is **false** without the maximality hypothesis
`IsMaximalSplittingExtension`.  For instance, for an unramified abelian `3`-extension `K/F` with
`Γ = (ℤ/3)^d` one has `dim H²(Γ, 𝔽_3) = d(d+1)/2`, which for `d ≥ 3` exceeds `d + C₀ + |T|`; such
`K` is not maximal for the class field tower (indeed the tower is then infinite, by
Golod–Shafarevich).  This is why the maximality hypothesis, and not merely unramifiedness, is part
of the interface.
-/

open NumberField
open scoped Classical

namespace Work.Tower.Shafarevich

/-- **Shafarevich's relation-rank estimate**, in the cohomological form used by the tower
construction: for every everywhere-unramified Galois `3`-extension `K` of a totally real cubic
field `F` which is maximal among those in which the primes of `T` split completely (with the
primes of `T` having trivial Frobenius class in the Frattini quotient), the `𝔽₃`-dimension of
`H²(Gal(K/F), 𝔽₃)` exceeds that of `H¹` by at most the absolute constant `C₀` plus `|T|`. -/
def H2Estimate (C₀ : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      ∀ (T : Finset (Ideal (𝓞 F))),
        IsFrobeniusTrivialInFrattini F T → IsMaximalSplittingExtension F K T →
        Module.finrank (ZMod 3) (H2Fp 3 (Gal(K/F))) ≤
          Module.finrank (ZMod 3) (H1Fp 3 (Gal(K/F))) + C₀ + T.card

/-- The same estimate for the maximal unramified group itself (`T = ∅`), i.e. Shafarevich's
estimate `r(G) ≤ d(G) + C₀` in cohomological form, for an `F`-maximal unramified `3`-extension. -/
def H2EstimateNoSplitting (C₀ : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
    Module.finrank ℚ F = 3 →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      IsMaximalSplittingExtension F K ∅ →
      Module.finrank (ZMod 3) (H2Fp 3 (Gal(K/F))) ≤
        Module.finrank (ZMod 3) (H1Fp 3 (Gal(K/F))) + C₀

end Work.Tower.Shafarevich
