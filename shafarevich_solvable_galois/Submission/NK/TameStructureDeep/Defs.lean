/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.TameStructureDeep`: the local structure theorem of `G_κ`, deeper than `NK.TameStructure`

This chapter is the *deep* layer of the local structure theory of the absolute Galois group
`G_κ = Gal(K'/κ)` of a `p`-adic field `κ`: it turns the input catalogue
`Submission/Work/TameData/Definitions.lean` (`TameInertiaInput`, `TameAbelianisationInput`,
`TameTorsionInput`, `NK.LocalStructure.TameFrobeniusCore`) into theorems, at every place of
every number field, in the sense required by `NK.ResidueFrob.LocalStructureData`.

The sibling chapter `Submission/Work/TameStructure/` already reduced the catalogue to a list of
*named classical inputs* (`UnramifiedZhat`, `TameInertiaStructure`, `FrobeniusNormalisation`,
`TameAbelianisationStructure`).  This chapter goes one layer down: it introduces a **single**
residual structure `TameRamificationCore` for the classical local structure theorem

  `G_κ^{tr} = G_κ/V_κ ≅ Ẑ ⋉ ∏_{ℓ ≠ p} ℤ_ℓ(1)`

(NSW, *Cohomology of Number Fields*, (7.5.6), (7.5.7) Corollary, (7.5.11), (12.1.8); Iwasawa,
*On Galois groups of local fields*; Shimizu, arXiv:2009.10431, Lemma 2.1), states each of its
components in the workspace's own vocabulary with its reference, and *proves* every consequence
used by the endgame from it.  The residual is *strictly weaker* than the previous list: the fields
`isProPrimeToP_tameInertia` and `tameInertia_commutator_mem` (which `NK.LocalStructure.TameCore`
and `NK.TameData.TameInertiaInput` carry as inputs) are *derived* here, as is the arithmetic
`q = p ^ f` of the residue cardinality, and the existence of the Frobenius and its normalisation
are fused into a single equivalence.

## What is in the residual, and why

| field | content | reference |
|---|---|---|
| `hp` | `p` is prime | — |
| `unramifiedQuotient` | `G_κ ⧸ I_κ ≅ Ẑ` | NSW (7.5.6), (7.5.7) Cor. |
| `isTameInertia` | `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ ⧸ V_κ` | NSW (7.5.7) Cor.; Iwasawa |
| `exists_frobenius` | there is `x ∈ G_κ` outside `I_κ` acting on `μ_{p'}` by `ζ ↦ ζ^q` | NSW (7.5.6) |
| `frobenius_iff` | `ζ ↦ ζ^q` on `μ_{p'}` ⟺ the `q`-th power map on `I_κ/V_κ` | NSW (12.1.8); Iwasawa |
| `abelianisation` | `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` | Shimizu 2.1 (local CFT) |

Everything else — the commutator relation `[I_κ, I_κ] ≤ V_κ`, the pro-prime-to-`p`-ness of
`I_κ/V_κ`, the closedness of `V_κ` (`TameRamificationCore.wildInertia_closed`, see
`Submission/Work/TameStructureDeep/Support/wildInertiaSubgroup_isClosed.lean`), the residue
cardinality `q = p^f`, the Frobenius normalisation core, the torsion of `G_κ^{tr,ab}`,
`NK.LocalStructure.TameCore`, `NK.TameData.TameDataInput` and
`NK.ResidueFrob.LocalStructureData` — is proved *from* this residual, in the sibling modules of
this directory.

## The vocabulary

The residual is expressed in the vocabulary of `Submission/Work/LocalTame/`,
`Submission/Work/LocalAnabelian/` and `Submission/Work/LocalStructure/`; the notational
dictionary is

* `V_κ = NK.LocalTame.wildInertiaSubgroup p` — the join of the normal pro-`p` subgroups of
  `G_κ` (`NK.LocalTame.wildInertiaSubgroup_isProP` shows it is pro-`p`, hence the maximal closed
  normal pro-`p` subgroup once it is known to be closed),
* `I_κ = NK.LocalAnabelian.inertiaSubgroup p` — the kernel of the action on the roots of unity
  of order prime to `p` (equivalently the fixing subgroup of `κ^ur = κ(μ_{p'})`),
* `κ(μ_{p'}) = NK.LocalAnabelian.unramifiedClosure p`,
* `Ẑ = NK.LocalAnabelian.Zhat` — the profinite completion of `ℤ`,
* `G_κ^{tr} = NK.LocalTame.tameQuotient p = G_κ ⧸ V_κ`,
* `I_κ/V_κ = NK.LocalTame.tameInertiaSubgroup p`,
* `G_κ^{tr,ab} = NK.LocalTame.tameAbelianization p = (G_κ ⧸ V_κ)^{ab}`,
* `μ_{q-1} = Multiplicative (ZMod (q-1))`,
* `IsFrobeniusFor p q x` — `x ∉ I_κ` and `x` acts on `μ_{p'}` by `ζ ↦ ζ^q`,
* `IsTameFrobeniusLift q V I x` — `x ∉ I` and `x y x⁻¹ ≡ y^q (mod V)` for `y ∈ I`.
-/
import Submission.NK.TameStructure.All
import Submission.NK.TameData.All
import Submission.NK.LocalStructure.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## The residual: the classical local structure theorem -/

/-- **The classical local structure theorem for `G_κ`, as a single residual.**

For a `p`-adic field `κ` with residue field of `q` elements and separable closure `K'`, this
records exactly the arithmetic content of

  `G_κ^{tr} = G_κ/V_κ ≅ Ẑ ⋉ ∏_{ℓ ≠ p} ℤ_ℓ(1)`,

namely: the unramified quotient, the maximality of the tame inertia, the closedness of the wild
inertia, the Frobenius and its normalisation, and the abelianised tame quotient.  Every other
statement of the local structure theory is *proved* from these in the sibling modules of this
directory; the two fields of `NK.TameData.TameInertiaInput` that used to be inputs
(`isProPrimeToP_tameInertia`, `tameInertia_commutator_mem`) are among the consequences.

Note that the residue field cardinality `q` is a *parameter*: for a genuine local field
`κ = K_𝔭` it is pinned to `NK.LocalStructure.residueCard K 𝔭` by the arithmetic of the
completion, and `q` is provably a power of `p` (`NK.TameStructureDeep.q_eq_of_charP`). -/
structure TameRamificationCore (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  /-- `p` is a prime number (the residue characteristic of `κ`) -/
  hp : p.Prime
  /-- **NSW (7.5.6), (7.5.7) Corollary**: the unramified quotient is `Ẑ`,
  `G_κ ⧸ I_κ ≅ Gal(κ^ur/κ) ≅ Ẑ` -/
  unramifiedQuotient :
    Nonempty ((Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) ≃*
      NK.LocalAnabelian.Zhat)
  /-- **NSW (7.5.7) Corollary; Iwasawa**: `I_κ/V_κ` is the maximal closed normal pro-cyclic
  subgroup of `G_κ^{tr} = G_κ ⧸ V_κ` (equivalently: the maximal tamely ramified extension of `κ`
  is `κ^ur(π^{1/n} : (n,p) = 1)` for a uniformiser `π`, so `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ`) -/
  isTameInertia :
    NK.LocalTame.IsMaxNormalProCyclicInQuotient
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)
  /-- **NSW (7.5.6)**: the normalised Frobenius exists — an element outside `I_κ` acting on the
  roots of unity of order prime to `p` by `ζ ↦ ζ^q` -/
  exists_frobenius : ∃ x : Gal(K'/κ), NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x
  /-- **NSW (12.1.8) Lemma; Iwasawa**: the Frobenius normalisation.  An element of `G_κ` acts on
  the prime-to-`p` roots of unity by `ζ ↦ ζ^q` **iff** it lies outside `I_κ` and conjugates the
  tame inertia `I_κ/V_κ` by the `q`-th power map.  Equivalently: the cyclotomic character
  identifies `G_κ/I_κ ≅ Ẑ` with `ℤ q ⊆ Aut(I_κ/V_κ) = ∏_{ℓ ≠ p} ℤ_ℓ^×`, and it is injective. -/
  frobenius_iff : ∀ x : Gal(K'/κ),
    NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ↔
      NK.LocalTame.IsTameFrobeniusLift q
        (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x
  /-- **Shimizu, arXiv:2009.10431, Lemma 2.1** (via local class field theory): the abelianised
  tame quotient is `Ẑ × μ_{q-1}` -/
  abelianisation : Nonempty
    (NK.LocalTame.tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))

/-! ## Basic API of the residual -/

namespace TameRamificationCore

variable {p q : ℕ} (h : TameRamificationCore p q κ K')

include h

/-- The wild inertia is contained in the inertia subgroup: the first component of the maximality
of `I_κ/V_κ`. -/
theorem wildInertia_le_inertia :
    NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p ≤
      NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.isTameInertia.1

/-- The tame inertia `I_κ/V_κ` is pro-cyclic in the workspace's sense (all finite quotients are
cyclic): the second component of the maximality. -/
theorem isProCyclic_tameInertia :
    NK.LocalTame.IsProCyclic
      ↥(NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)) :=
  h.isTameInertia.2.2.1

/-- The maximality statement, unpacked: any `J ≥ V_κ` whose image in `G_κ^{tr}` is normal and
pro-cyclic lies in the inertia subgroup. -/
theorem le_inertia_of_isProCyclic {J : Subgroup (Gal(K'/κ))}
    (hJ : NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p ≤ J)
    (hJn : (NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      J).Normal)
    (hJc : NK.LocalTame.IsProCyclic
      ↥(NK.LocalTame.quotientImage (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p) J)) :
    J ≤ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.isTameInertia.2.2.2 J hJ hJn hJc

/-- The Frobenius normalisation, in the direction used to produce a Frobenius lift from a
Frobenius element. -/
theorem isTameFrobeniusLift_of_isFrobeniusFor {x : Gal(K'/κ)}
    (hx : NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x) :
    NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x :=
  (h.frobenius_iff x).mp hx

/-- The Frobenius normalisation, in the direction used to derive the cyclotomic action on the
roots of unity from the action on the tame inertia. -/
theorem actsAsFrobenius_of_isTameFrobeniusLift {x : Gal(K'/κ)}
    (hx : NK.LocalTame.IsTameFrobeniusLift q
      (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
      (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x) :
    NK.LocalAnabelian.ActsAsFrobenius (κ := κ) (K' := K') p q x :=
  ((h.frobenius_iff x).mpr hx).2

/-- The Frobenius element supplied by the residual, together with both of its defining
properties. -/
theorem exists_isFrobeniusFor_and_isTameFrobeniusLift :
    ∃ x : Gal(K'/κ),
      NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ∧
        NK.LocalTame.IsTameFrobeniusLift q
          (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p)
          (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x := by
  obtain ⟨x, hx⟩ := h.exists_frobenius
  exact ⟨x, hx, h.isTameFrobeniusLift_of_isFrobeniusFor hx⟩

end TameRamificationCore

end

end NK.TameStructureDeep
