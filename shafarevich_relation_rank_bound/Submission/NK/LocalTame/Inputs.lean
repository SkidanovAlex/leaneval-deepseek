/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The named inputs: the local structure theory of `G_κ`

This file collects, as explicit `structure`s, the *arithmetic* inputs of the theory: the
classical structure theorems about the absolute Galois group `G_κ = Gal(κ̄/κ)` of a `p`-adic
field `κ` that cannot be proved from the group theory of `NK.LocalTame.Basic` alone.  Each
structure carries the exact reference to the literature; everything *derived* from them is
proved in `NK.LocalTame.Main` and `NK.LocalTame.Global`.

Throughout, `κ` is a `p`-adic field (concretely `κ = K_𝔭`, the `𝔭`-adic completion of a number
field `K`), `K'` is a separable closure of `κ`, and `q` is the cardinality of the residue field
of `κ`.

The four inputs are

* `TameStructureInput p q κ K'` — the structure of the tame quotient `G_κ^{tr} = G_κ/V_κ`
  (NSW, *Cohomology of Number Fields*, (7.5.7) Corollary and (7.5.11); Iwasawa, *On Galois
  groups of local fields*): `V_κ` is the maximal closed normal pro-`p` subgroup, it lies in the
  inertia subgroup `I_κ`, and `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of
  `G_κ^{tr}`; the latter is pro-prime-to-`p`, and the quotient `G_κ^{tr}/(I_κ/V_κ) = G_κ/I_κ`
  is `Ẑ`.
* `ResidueCardRecovery p q κ K'` — the recovery of `q` from the torsion of the abelianised tame
  quotient (Shimizu, arXiv:2009.10431, Lemma 2.1, via local class field theory).  The classical
  statement is `q = #((G_κ^{tr,ab})_{tor}/(G_κ^{tr,ab})[p^∞]) + 1`; since `q` is a power of `p`
  the `p`-primary part of the torsion is trivial and this is the statement recorded here.
* `FrobeniusLiftCharacterisation p q κ K'` — the classical Frobenius normalisation: the
  elements of `G_κ` acting on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` are exactly the
  elements lying outside `I_κ` whose conjugation action on the tame inertia `I_κ/V_κ` is the
  `q`-th power map.  This is the statement that `Ẑ` acts on the tame inertia through the
  cyclotomic character, and that this action determines the coset of the Frobenius
  (NSW (12.1.8) Lemma; Iwasawa).
* `Zl2ResidueChar p κ K'` — Shimizu's characterisation of the residue characteristic: `p` is the
  unique prime `ℓ` such that `G_κ` admits a surjection onto `ℤ_ℓ²` (equivalently: has
  `ℓ`-cohomological dimension `2` with a free `ℤ_ℓ²`-quotient).  Here this is phrased in finite
  quotients as: `G_κ ↠ (ℤ/ℓ^n)²` for all `n ≥ 1`.  Proof (Shimizu, Lemma 2.1, from local class
  field theory): for `ℓ = p`, `G_κ^{(p)}` is a Demushkin group of rank `[κ:ℚ_p] + 2 ≥ 3`
  (NSW (7.5.11)), whose abelianisation is free of rank `≥ 2` over `ℤ_p`; for `ℓ ≠ p` the maximal
  pro-`ℓ` quotient of `G_κ` is pro-cyclic, namely `ℤ_ℓ`.
-/
import Submission.NK.LocalAnabelian.All
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.Galois

open scoped Classical
open IntermediateField
open NK.LocalAnabelian

namespace NK.LocalTame

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## The structure of the tame quotient -/

/-- **The structure of the tame quotient `G_κ^{tr} = G_κ/V_κ` of a `p`-adic field.**

`q` is the cardinality of the residue field of `κ`.  The fields record

* the wild inertia `V_κ` is contained in the inertia subgroup `I_κ` (which is the fixing
  subgroup of `κ^ur = κ(μ_{p'})`, see `NK.LocalAnabelian.unramifiedClosure`);
* `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}` and is
  pro-prime-to-`p` — so `G_κ^{tr}` is an extension of `Ẑ` by the free pro-prime-to-`p` group
  `I_κ/V_κ`;
* the extension splits: there is a Frobenius, i.e. an element outside `I_κ` (the classical
  existence of the canonical generator of `Gal(κ^ur/κ) ≅ Ẑ`; the field `exists_frobeniusLift`
  records it, and `NK.LocalAnabelian.ResidueCardInput.frob` supplies such an element);
* the unramified quotient `G_κ/I_κ` is `Ẑ`.

Reference: NSW, *Cohomology of Number Fields*, (7.5.7) Corollary, (7.5.11); Iwasawa, *On Galois
groups of local fields*.  (The corresponding statement for the `p`-Sylow subgroups of the
tame quotient is Ivanov, arXiv:1309.2801, Lemma 2.2, the "`p`-decomposition type" case, whose
group theory is in `Submission/Work/LocalAnabelian/`.) -/
structure TameStructureInput (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  hp : p.Prime
  /-- the residue field cardinality is a power of `p`, `q = p^f` with `f ≥ 1` -/
  q_eq : ∃ f : ℕ, 0 < f ∧ q = p ^ f
  /-- the wild inertia is contained in the inertia subgroup -/
  wildInertia_le_inertia :
    wildInertiaSubgroup (κ := κ) (K' := K') p ≤ inertiaSubgroup (κ := κ) (K' := K') p
  /-- `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}` -/
  isTameInertia : IsMaxNormalProCyclicInQuotient (wildInertiaSubgroup (κ := κ) (K' := K') p)
    (inertiaSubgroup (κ := κ) (K' := K') p)
  /-- the tame inertia is pro-prime-to-`p` -/
  isProPrimeToP_tameInertia : IsProPrimeToP p ↥(tameInertiaSubgroup (κ := κ) (K' := K') p)
  /-- the tame inertia is pro-cyclic, hence abelian: the commutator of two inertia elements lies
  in the wild inertia.  (Pro-cyclicity is stated above through finite quotients; this is its
  abelian consequence, which is what the coset structure of the Frobenius lifts uses.) -/
  tameInertia_commutator_mem : ∀ y ∈ inertiaSubgroup (κ := κ) (K' := K') p,
    ∀ z ∈ inertiaSubgroup (κ := κ) (K' := K') p,
      y * z * y⁻¹ * z⁻¹ ∈ wildInertiaSubgroup (κ := κ) (K' := K') p
  /-- the unramified quotient is `Ẑ`: `G_κ/I_κ ≅ Ẑ` -/
  unramifiedQuotient : Nonempty ((Gal(K'/κ) ⧸ inertiaSubgroup (κ := κ) (K' := K') p) ≃* Zhat)
  /-- the Frobenius exists: there is an element outside the inertia subgroup, so that the
  extension of `Ẑ` by the tame inertia `I_κ/V_κ` splits (the classical existence of the
  canonical generator of `Gal(κ^ur/κ) ≅ Ẑ`; the Frobenius normalisation of such an element is
  the input `NK.LocalTame.FrobeniusLiftCharacterisation`) -/
  exists_frobeniusLift : ∃ x : Gal(K'/κ), x ∉ inertiaSubgroup (κ := κ) (K' := K') p

/-- **`V_κ` is the unique maximal closed normal pro-`p` subgroup of `G_κ`** (NSW (7.5.7)
Corollary), restated: every closed normal pro-`p` subgroup of `G_κ` is contained in `V_κ`. -/
theorem TameStructureInput.le_wildInertia {p q : ℕ} (h : TameStructureInput p q κ K')
    {N : Subgroup (Gal(K'/κ))} (hN : N.Normal) (hNp : IsProP p ↥N) :
    N ≤ wildInertiaSubgroup (κ := κ) (K' := K') p :=
  le_wildInertiaSubgroup hN hNp

/-- **`I_κ/V_κ` is the unique maximal closed normal pro-cyclic subgroup of `G_κ^{tr}`**
(NSW (7.5.7) Corollary): any subgroup `J ≥ V_κ` whose image in `G_κ^{tr}` is normal with
pro-cyclic (equivalently: finite quotients cyclic) image lies in `I_κ`. -/
theorem TameStructureInput.le_inertia {p q : ℕ} (h : TameStructureInput p q κ K')
    {J : Subgroup (Gal(K'/κ))}
    (hJ : wildInertiaSubgroup (κ := κ) (K' := K') p ≤ J)
    (hJn : (quotientImage (wildInertiaSubgroup (κ := κ) (K' := K') p) J).Normal)
    (hJc : IsProCyclic ↥(quotientImage (wildInertiaSubgroup (κ := κ) (K' := K') p) J)) :
    J ≤ inertiaSubgroup (κ := κ) (K' := K') p :=
  h.isTameInertia.2.2.2 J hJ hJn hJc

/-! ## The residue field cardinality -/

/-- **The order of the residue field of `κ` is recovered from `G_κ`** (Shimizu,
arXiv:2009.10431, Lemma 2.1, using local class field theory):

  `q = #((G_κ^{tr,ab})_{tor}/(G_κ^{tr,ab})[p^∞]) + 1`.

Indeed `G_κ^{ab} ≅ κˣ^{∧} ≅ μ_{q-1} × (pro-`p` part) × Ẑ`, and killing the wild inertia
(a pro-`p` group) leaves `G_κ^{tr,ab} ≅ μ_{q-1} × Ẑ`, whose torsion subgroup is cyclic of order
`q - 1`.  Since `q` is a power of `p`, the `p`-primary part of the torsion is trivial, so the
quotient by `(G_κ^{tr,ab})[p^∞]` does not change the order; this is why the statement below
records `#(G_κ^{tr,ab})_{tor} = q - 1`. -/
structure ResidueCardRecovery (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  hp : p.Prime
  /-- `q` is a power of `p` -/
  q_eq : ∃ f : ℕ, 0 < f ∧ q = p ^ f
  /-- the torsion of the abelianised tame quotient has order `q - 1` -/
  card_torsion : Nat.card (tameTorsion (κ := κ) (K' := K') p) = q - 1

/-! ## The Frobenius normalisation -/

/-- **Frobenius lifts are detected by their action on the tame inertia** (NSW (12.1.8) Lemma;
Iwasawa, *On Galois groups of local fields*).

An element `x ∈ G_κ` acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` if and only if it lies
outside `I_κ` and conjugates the tame inertia `I_κ/V_κ` by the `q`-th power map.  Equivalently:
the cyclotomic character identifies `G_κ/I_κ ≅ Ẑ` with the subgroup `ℤ q` of
`Aut(I_κ/V_κ) = ∏_{ℓ ≠ p} ℤ_ℓ^×` generated by the `q`-th power map, and this identification is
injective, so the Frobenius coset — i.e. the set of Frobenius lifts — is visible from
`G_κ^{tr} = G_κ/V_κ` and the integer `q`. -/
structure FrobeniusLiftCharacterisation (p q : ℕ) (κ K' : Type*) [Field κ] [Field K']
    [Algebra κ K'] : Prop where
  hp : p.Prime
  /-- the Frobenius lifts are the elements acting on the tame inertia by the `q`-th power map -/
  iff : ∀ x : Gal(K'/κ), IsFrobeniusFor p q x ↔
    IsTameFrobeniusLift q (wildInertiaSubgroup (κ := κ) (K' := K') p)
      (inertiaSubgroup (κ := κ) (K' := K') p) x

/-! ## The residue characteristic -/

/-- **Shimizu's characterisation of the residue characteristic** (arXiv:2009.10431, Lemma 2.1):
the residue characteristic `p` of `κ` is the unique prime `ℓ` such that `G_κ` admits a
surjection onto `ℤ_ℓ²`.

Formally `HasZl2Quotient ℓ (Gal(K'/κ))` says that for every `n ≥ 1` there is a surjection
`G_κ ↠ (ℤ/ℓ^n)²`, which for the profinite group `G_κ` is the same as a surjection onto the free
pro-`ℓ` group `ℤ_ℓ²` of rank two. -/
structure Zl2ResidueChar (p : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] :
    Prop where
  hp : p.Prime
  /-- `p` is the unique prime `ℓ` with a surjection `G_κ ↠ ℤ_ℓ²` -/
  detects : ∀ ℓ : ℕ, ℓ.Prime → (HasZl2Quotient ℓ (Gal(K'/κ)) ↔ ℓ = p)

/-- **The residue characteristic is the unique prime with a `ℤ_ℓ²`-quotient**, stated as a
named theorem. -/
theorem Zl2ResidueChar.residueChar_unique {p : ℕ} {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] (h : Zl2ResidueChar p κ K') {ℓ : ℕ} (hℓ : ℓ.Prime) :
    HasZl2Quotient ℓ (Gal(K'/κ)) ↔ ℓ = p :=
  h.detects ℓ hℓ

/-! ## The bundled input -/

/-- **All the local tame inputs for a `p`-adic field `κ` with residue field of `q` elements**, in
one structure.  A caller who has the four inputs separately can build this, and the main results
of `NK.LocalTame.Main` take it (or the separate pieces). -/
structure TameData (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K'] : Prop where
  structure_input : TameStructureInput p q κ K'
  residueCard : ResidueCardRecovery p q κ K'
  frobeniusLift : FrobeniusLiftCharacterisation p q κ K'

/-! ## The structure of the tame quotient, stated as one theorem -/

/-- **The tame quotient `G_κ^{tr}` is an extension of `Ẑ` by the free pro-prime-to-`p` tame
inertia `I_κ/V_κ`, acted on by `Ẑ` through the cyclotomic character** — the structure statement of
NSW (7.5.7)/(7.5.11), in the form in which this development uses it.  Concretely:

* `V_κ ⊆ I_κ`;
* `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}`;
* `I_κ/V_κ` is pro-prime-to-`p` (so the extension is by a pro-prime-to-`p` group);
* `G_κ/I_κ ≅ Ẑ` (the unramified quotient);
* the action of `G_κ^{tr}` on `I_κ/V_κ` is the cyclotomic one: the Frobenius lifts are exactly the
  elements acting on `I_κ/V_κ` by the `q`-th power map. -/
theorem TameData.tameQuotient_structure {p q : ℕ} (h : TameData p q κ K') :
    wildInertiaSubgroup (κ := κ) (K' := K') p ≤ inertiaSubgroup (κ := κ) (K' := K') p ∧
      IsMaxNormalProCyclicInQuotient (wildInertiaSubgroup (κ := κ) (K' := K') p)
        (inertiaSubgroup (κ := κ) (K' := K') p) ∧
      IsProPrimeToP p ↥(tameInertiaSubgroup (κ := κ) (K' := K') p) ∧
      Nonempty ((Gal(K'/κ) ⧸ inertiaSubgroup (κ := κ) (K' := K') p) ≃* Zhat) ∧
      (∀ x : Gal(K'/κ), IsFrobeniusFor p q x ↔
        IsTameFrobeniusLift q (wildInertiaSubgroup (κ := κ) (K' := K') p)
          (inertiaSubgroup (κ := κ) (K' := K') p) x) :=
  ⟨h.structure_input.wildInertia_le_inertia, h.structure_input.isTameInertia,
    h.structure_input.isProPrimeToP_tameInertia, h.structure_input.unramifiedQuotient,
    h.frobeniusLift.iff⟩

/-- **Shimizu's formula for the residue field order**: the order of the residue field is
`#((G_κ^{tr,ab})_{tor}) + 1`, i.e. `#torsion + 1 = q` in the notation of `tameTorsion`.  (The
classical statement has `(G_κ^{tr,ab})_{tor}/(G_κ^{tr,ab})[p^∞]` in place of `(G_κ^{tr,ab})_{tor}`;
since `q` is a power of `p`, the `p`-primary part of the torsion is trivial, so the two agree.) -/
theorem ResidueCardRecovery.card_torsion_add_one {p q : ℕ} (h : ResidueCardRecovery p q κ K') :
    Nat.card (tameTorsion (κ := κ) (K' := K') p) + 1 = q := by
  obtain ⟨f, hf, hqf⟩ := h.q_eq
  have hq0 : q ≠ 0 := by rw [hqf]; exact pow_ne_zero _ h.hp.ne_zero
  have := h.card_torsion
  omega

end

end NK.LocalTame
