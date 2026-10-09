/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Frobenius normalisation at a `𝔭`-adic completion

This file discharges **deliverable 3** of the area: the structure
`NK.LocalStructure.TameFrobeniusCore p q (K_𝔭) K'` (NSW, *Cohomology of Number Fields*,
(12.1.8) Lemma; Iwasawa, *On Galois groups of local fields*) for a genuine local field
`κ = K_𝔭 = 𝔭.adicCompletion K` and `K'` a separable closure of `κ`.

The mathematical content is isolated in the named input `NK.TameStructure.FrobeniusNormalisation`
(NSW (12.1.8)), the two halves of which are: the canonical Frobenius — normalised by its action
`ζ ↦ ζ^q` on the prime-to-`p` roots of unity, whose existence is the *separate* classical input
`NK.TameStructure.ResidueFrobenius` (NSW (7.5.6)) — conjugates the tame inertia `I_κ/V_κ` by the
`q`-th power map; and conversely.  The identification behind both is the Kummer-theoretic
description of the `G_κ`-module `I_κ/V_κ = Gal(κ^{tr}/κ^ur)` as the Tate twist `∏_{ℓ ≠ p} ℤ_ℓ(1)`,
whose Kummer dual is `μ_{p'}` with the cyclotomic action.
-/
import Submission.NK.TameStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructure

universe u

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- **The normalised Frobenius exists, from the Frobenius normalisation.**  The first half of
(12.1.8) supplies an element which both acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` and
conjugates the tame inertia by the `q`-th power map; in particular the normalised Frobenius
exists (`NK.TameStructure.ResidueFrobenius`).  This shows that `ResidueFrobenius` is *not* an
independent input once the Frobenius normalisation is available. -/
theorem residueFrobenius_of_frobeniusNormalisation
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (h : FrobeniusNormalisation p q K 𝔭 K') : ResidueFrobenius p q K 𝔭 K' :=
  ⟨h.1.choose, h.1.choose_spec.1⟩

/-- **The Frobenius from the normalisation is a Frobenius lift.** -/
theorem isTameFrobeniusLift_of_frobeniusNormalisation
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (h : FrobeniusNormalisation p q K 𝔭 K') :
    ∃ x : Gal(K'/𝔭.adicCompletion K),
      NK.LocalAnabelian.IsFrobeniusFor (κ := 𝔭.adicCompletion K) (K' := K') p q x ∧
        NK.LocalTame.IsTameFrobeniusLift q
          (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
          (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p) x :=
  h.1

/-- **Deliverable 3**: for a `p`-adic field `κ = K_𝔭` with residue field of `q` elements, the
Frobenius is normalised by its action on the tame inertia (NSW (12.1.8) Lemma; Iwasawa).

The two fields of `NK.LocalStructure.TameFrobeniusCore` are exactly the two components of the
named input `NK.TameStructure.FrobeniusNormalisation`, so this lemma is the (short) repackaging;
the table in `NK.TameStructure.Defs` records the classical references. -/
theorem tameFrobeniusCore_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ} (hp : p.Prime)
    (h : FrobeniusNormalisation p q K 𝔭 K') :
    NK.LocalStructure.TameFrobeniusCore p q (𝔭.adicCompletion K) K' where
  hp := hp
  exists_frob := h.1
  actsAsFrobenius_of_isTameFrobeniusLift := h.2

/-- **The Frobenius normalisation from the *characterisation* of the Frobenius lifts.**  If every
element acting on the prime-to-`p` roots of unity by `ζ ↦ ζ ^ q` is a Frobenius lift and
conversely (`NK.LocalTame.FrobeniusLiftCharacterisation`, i.e. the packaged form of (12.1.8)
used downstream), then — together with the existence of a Frobenius element — the normalisation
input holds. -/
theorem frobeniusNormalisation_of_characterisation
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ}
    (hex : ResidueFrobenius p q K 𝔭 K')
    (hchar : ∀ x : Gal(K'/𝔭.adicCompletion K),
      NK.LocalAnabelian.IsFrobeniusFor (κ := 𝔭.adicCompletion K) (K' := K') p q x ↔
        NK.LocalTame.IsTameFrobeniusLift q
          (NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p)
          (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K') p) x) :
    FrobeniusNormalisation p q K 𝔭 K' := by
  obtain ⟨x, hx⟩ := hex
  refine ⟨⟨x, hx, (hchar x).mp hx⟩, ?_⟩
  intro y hy
  exact ((hchar y).mpr hy).2

end

end NK.TameStructure
