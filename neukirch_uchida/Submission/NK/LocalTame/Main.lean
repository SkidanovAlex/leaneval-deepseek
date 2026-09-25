/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.LocalTame.Main`: the local Frobenius correspondence

This is the main theorem of the area: **an isomorphism of the absolute Galois groups of two
`p`-adic fields maps the Frobenius lifts onto the Frobenius lifts** — the local statement of
Shimizu, *The Neukirch–Uchida theorem with restricted ramification*, arXiv:2009.10431, Lemma 2.1
(see also NSW, *Cohomology of Number Fields*, (12.1.8) Lemma).  It is the local input that lets
the Neukirch–Uchida endgame match Frobenius elements at corresponding places.

## The shape of the argument

Let `κ`, `κ₂` be `p`-adic fields with separable closures `K'`, `L'`, and let
`Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)` be an isomorphism of their absolute Galois groups.  All the group
theory below is about the *abstract* group `Gal(K'/κ)`; no continuity of `Φ` is needed, and none
is assumed (the predicates of `NK.LocalTame.Basic` are isomorphism invariants).

1. **The residue characteristics agree** (`residueChar_eq_of_zl2`): by
   `NK.LocalTame.Zl2ResidueChar`, the residue characteristic is the unique prime `ℓ` with a
   surjection `Gal(K'/κ) ↠ ℤ_ℓ²`, a group-theoretic property.  (Equivalently, one can use
   Ivanov's `ℓ`-tower rank, `NK.LocalAnabelian.ResidueCharInput`.)
2. **The wild inertias correspond** (`mulEquiv_maps_wildInertia`): `V_κ = wildInertiaSubgroup p`
   is *by definition* the join of all normal pro-`p` subgroups and *provably* pro-`p`
   (`NK.LocalTame.wildInertiaSubgroup_isProP`), so it is the maximal closed normal pro-`p`
   subgroup; maximality is an isomorphism invariant, so `Φ(V_κ) = V_{κ₂}`.
3. **The inertia subgroups correspond** (`mulEquiv_maps_inertia`): `I_κ/V_κ` is the maximal
   closed normal pro-cyclic subgroup of `G_κ^{tr}` (the input `TameStructureInput.isTameInertia`,
   NSW (7.5.7) Corollary); this property transfers along `Φ`, so `Φ(I_κ) = I_{κ₂}`.
4. **The residue field orders agree** (`residueCard_eq_of_tameData`): the order `q` of the
   residue field is `#((G_κ^{tr,ab})_{tor}) + 1` (the input `ResidueCardRecovery`, Shimizu
   Lemma 2.1 via local class field theory); this cardinality is an isomorphism invariant of the
   abelianised tame quotient `G_κ^{tr,ab} = G_κ/V_κ`, so `q = q₂`.
5. **The Frobenius lifts correspond** (`isFrobeniusFor_map_iff_of_eq`): by the input
   `FrobeniusLiftCharacterisation` (NSW (12.1.8) Lemma, Iwasawa), a Frobenius lift is exactly an
   element `x ∉ I_κ` acting on `I_κ/V_κ` by `y ↦ y^q`, i.e. satisfying the *pure group theory*
   predicate `IsTameFrobeniusLift q V_κ I_κ x`; that predicate is preserved by any isomorphism
   carrying `V_κ ↦ V_{κ₂}` and `I_κ ↦ I_{κ₂}` and sending `q ↦ q`
   (`NK.LocalTame.isTameFrobeniusLift_map_iff`).
-/
import Submission.NK.LocalAnabelian.All
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.Basic.isTameFrobeniusLift_mul_mem_inertia
import Submission.NK.LocalTame.Basic.isTameFrobeniusLift_of_mul_mem_inertia
import Submission.NK.LocalTame.Galois
import Submission.NK.LocalTame.Inputs
import Submission.NK.LocalTame.WildInertiaProP
import Submission.NK.LocalTame.Transfer.IsMaxNormalProCyclicInQuotient_map
import Submission.NK.LocalTame.Transfer.natCard_torsion_mulEquiv

set_option linter.style.haveILetI false

open scoped Classical
open NK.LocalAnabelian
open NK.LocalTame.Transfer
open NK.LocalTame.Basic

namespace NK.LocalTame

universe u

noncomputable section

variable {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂] [Field K'] [Field L']
  [Algebra κ K'] [Algebra κ₂ L']

/-! ## The residue characteristic -/

/-- **Shimizu's detection of the residue characteristic**: an isomorphism of absolute Galois
groups of `p`-adic fields forces the residue characteristics to coincide (arXiv:2009.10431,
Lemma 2.1: `p` is the unique prime `ℓ` with a surjection `G_κ ↠ ℤ_ℓ²`). -/
theorem residueChar_eq_of_zl2 {p p₂ : ℕ} (h : Zl2ResidueChar p κ K')
    (h₂ : Zl2ResidueChar p₂ κ₂ L') (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : p = p₂ := by
  have h1 : HasZl2Quotient p (Gal(K'/κ)) := (h.detects p h.hp).mpr rfl
  have h2 : HasZl2Quotient p (Gal(L'/κ₂)) := (hasZl2Quotient_congr Φ p).mp h1
  exact (h₂.detects p h.hp).mp h2

/-- The same conclusion from the `ℓ`-tower-rank detection of the residue characteristic
(`NK.LocalAnabelian.ResidueCharInput`, Ivanov Lemma 3.12): only a group isomorphism is needed,
not a homeomorphism. -/
theorem residueChar_eq_of_residueCharInput {p p₂ : ℕ} {κ κ₂ K' L' : Type*} [Field κ] [Field κ₂]
    [Field K'] [Field L'] [Algebra κ K'] [Algebra κ₂ L'] [IsSepClosure κ K']
    [IsSepClosure κ₂ L'] (h : ResidueCharInput p κ K') (h₂ : ResidueCharInput p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : p = p₂ :=
  residueChar_eq_of_mulEquiv h h₂ Φ

/-! ## The wild inertia and the inertia subgroup -/

/-- **An isomorphism of absolute Galois groups of `p`-adic fields maps the wild inertia onto the
wild inertia** (for a fixed residue characteristic `p`).  This is Shimizu's Lemma 2.1 step
`Φ(V_{κ₁}) = V_{κ₂}`, here a consequence of `V_κ` being the maximal closed normal pro-`p`
subgroup — with the pro-`p`-ness of `wildInertiaSubgroup` proved in
`NK.LocalTame.WildInertiaProP`. -/
theorem mulEquiv_maps_wildInertia (p : ℕ) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    (wildInertiaSubgroup (κ := κ) (K' := K') p).map (Φ : Gal(K'/κ) →* Gal(L'/κ₂)) =
      wildInertiaSubgroup (κ := κ₂) (K' := L') p :=
  (IsWildInertia.map (wildInertiaSubgroup_isWildInertia (κ := κ) (K' := K') p) Φ).eq
    (wildInertiaSubgroup_isWildInertia (κ := κ₂) (K' := L') p)

/-- The isomorphism induced by `Φ` between the tame quotients `G_κ^{tr} = G_κ/V_κ` and
`G_κ₂^{tr} = G_κ₂/V_κ₂`. -/
noncomputable def mulEquivTameQuotient (p : ℕ) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    tameQuotient (κ := κ) (K' := K') p ≃* tameQuotient (κ := κ₂) (K' := L') p :=
  QuotientGroup.congr _ _ Φ (mulEquiv_maps_wildInertia (κ := κ) (K' := K') (κ₂ := κ₂) (L' := L')
    p Φ)

/-- **The induced isomorphism on the abelianised tame quotients** `G_κ^{tr,ab} ≃* G_κ₂^{tr,ab}`,
through which the residue field order is compared. -/
noncomputable def mulEquivTameAbelianization (p : ℕ) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    tameAbelianization (κ := κ) (K' := K') p ≃* tameAbelianization (κ := κ₂) (K' := L') p :=
  abelianizationMulEquiv (mulEquivTameQuotient (κ := κ) (K' := K') (κ₂ := κ₂) (L' := L') p Φ)

/-- **An isomorphism of absolute Galois groups of `p`-adic fields maps the inertia subgroup onto
the inertia subgroup.**  `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of the tame
quotient (NSW (7.5.7) Corollary, the input `TameStructureInput.isTameInertia`); this maximality
transfers along `Φ`, and `V_κ` is mapped to `V_κ₂` by `mulEquiv_maps_wildInertia`. -/
theorem mulEquiv_maps_inertia {p p₂ q q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hp : p = p₂) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    (inertiaSubgroup (κ := κ) (K' := K') p).map (Φ : Gal(K'/κ) →* Gal(L'/κ₂)) =
      inertiaSubgroup (κ := κ₂) (K' := L') p₂ := by
  subst hp
  have hV := mulEquiv_maps_wildInertia (κ := κ) (K' := K') (κ₂ := κ₂) (L' := L') p Φ
  have h1 : IsMaxNormalProCyclicInQuotient (wildInertiaSubgroup (κ := κ₂) (K' := L') p)
      ((inertiaSubgroup (κ := κ) (K' := K') p).map (Φ : Gal(K'/κ) →* Gal(L'/κ₂))) :=
    IsMaxNormalProCyclicInQuotient_map h.structure_input.isTameInertia Φ hV
  exact h1.eq h₂.structure_input.isTameInertia

/-- The same statement with the residue characteristic unified in advance. -/
theorem mulEquiv_maps_inertia' {p q q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p q₂ κ₂ L') (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    (inertiaSubgroup (κ := κ) (K' := K') p).map (Φ : Gal(K'/κ) →* Gal(L'/κ₂)) =
      inertiaSubgroup (κ := κ₂) (K' := L') p :=
  mulEquiv_maps_inertia h h₂ rfl Φ

/-! ## The residue field cardinality -/

/-- **An isomorphism of absolute Galois groups of `p`-adic fields forces the residue fields to
have the same cardinality** (Shimizu, arXiv:2009.10431, Lemma 2.1).  The order `q` of the residue
field is the order of the torsion subgroup of the abelianised tame quotient
(`ResidueCardRecovery`), which is an isomorphism invariant of `G_κ^{tr,ab} = G_κ/V_κ`. -/
theorem residueCard_eq_of_tameData {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hp : p = p₂) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) : q = q₂ := by
  subst hp
  have hcard : Nat.card (tameTorsion (κ := κ) (K' := K') p) =
      Nat.card (tameTorsion (κ := κ₂) (K' := L') p) :=
    natCard_torsion_mulEquiv (mulEquivTameAbelianization (κ := κ) (K' := K') (κ₂ := κ₂)
      (L' := L') p Φ)
  have h1 := h.residueCard.card_torsion
  have h2 := h₂.residueCard.card_torsion
  have h3 : q - 1 = q₂ - 1 := by
    rw [← h1, ← h2]
    exact hcard
  obtain ⟨f, hf, hqf⟩ := h.residueCard.q_eq
  obtain ⟨g, hg, hqg⟩ := h₂.residueCard.q_eq
  have hq0 : q ≠ 0 := by rw [hqf]; exact pow_ne_zero _ h.residueCard.hp.ne_zero
  have hq₂0 : q₂ ≠ 0 := by rw [hqg]; exact pow_ne_zero _ h₂.residueCard.hp.ne_zero
  omega

/-- The residue field orders also determine the residue *degrees*: both are powers of `p`, and
`q = q₂` forces the exponents to agree. -/
theorem residueDeg_eq_of_tameData {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hp : p = p₂) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    ∀ f g : ℕ, q = p ^ f → q₂ = p ^ g → f = g := by
  intro f g hf hg
  have hq : q = q₂ := residueCard_eq_of_tameData h h₂ hp Φ
  have hp2 : 2 ≤ p := h.structure_input.hp.two_le
  have : p ^ f = p ^ g := by rw [← hf, hq, hg]
  exact Nat.pow_right_injective hp2 this

/-! ## The Frobenius correspondence -/

/-- **The local Frobenius correspondence** (Shimizu, arXiv:2009.10431, Lemma 2.1; NSW (12.1.8)
Lemma): an isomorphism `Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)` of absolute Galois groups of `p`-adic fields
with the *same* residue characteristic `p` and the same residue field cardinality `q` maps the set
of Frobenius lifts of `κ` onto the set of Frobenius lifts of `κ₂`. -/
theorem isFrobeniusFor_map_iff_of_eq {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hp : p = p₂) (hq : q = q₂)
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) (τ : Gal(K'/κ)) :
    IsFrobeniusFor p q τ ↔ IsFrobeniusFor p₂ q₂ (Φ τ) := by
  subst hp
  subst hq
  have hV := mulEquiv_maps_wildInertia (κ := κ) (K' := K') (κ₂ := κ₂) (L' := L') p Φ
  have hI := mulEquiv_maps_inertia' h h₂ Φ
  rw [h.frobeniusLift.iff τ, h₂.frobeniusLift.iff (Φ τ)]
  exact isTameFrobeniusLift_map_iff Φ hV hI τ

/-- **The local Frobenius correspondence**, without assuming that the residue characteristics and
residue field cardinalities agree: they are *forced* to agree by the isomorphism
(`residueChar_eq_of_zl2`, `residueCard_eq_of_tameData`), and then the Frobenius lifts correspond.

This is the precise form in which the Neukirch–Uchida endgame consumes the local input: an
element `τ` of `Gal(K'/κ)` is a Frobenius lift for `κ` if and only if `Φ τ` is a Frobenius lift
for `κ₂`. -/
theorem isFrobeniusFor_map_iff {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hZ : Zl2ResidueChar p κ K') (hZ₂ : Zl2ResidueChar p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) (τ : Gal(K'/κ)) :
    IsFrobeniusFor p q τ ↔ IsFrobeniusFor p₂ q₂ (Φ τ) :=
  isFrobeniusFor_map_iff_of_eq h h₂ (residueChar_eq_of_zl2 hZ hZ₂ Φ)
    (residueCard_eq_of_tameData h h₂ (residueChar_eq_of_zl2 hZ hZ₂ Φ) Φ) Φ τ

/-- The one-directional form used by the endgame: a Frobenius lift is mapped to a Frobenius
lift. -/
theorem IsFrobeniusFor.map {p q p₂ q₂ : ℕ} (h : TameData p q κ K') (h₂ : TameData p₂ q₂ κ₂ L')
    (hZ : Zl2ResidueChar p κ K') (hZ₂ : Zl2ResidueChar p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) {τ : Gal(K'/κ)} (hτ : IsFrobeniusFor p q τ) :
    IsFrobeniusFor p₂ q₂ (Φ τ) :=
  (isFrobeniusFor_map_iff h h₂ hZ hZ₂ Φ τ).mp hτ

/-- **The Frobenius correspondence as a bijection on the sets of Frobenius lifts.** -/
theorem frobeniusLiftSet_image {p q p₂ q₂ : ℕ} (h : TameData p q κ K')
    (h₂ : TameData p₂ q₂ κ₂ L') (hZ : Zl2ResidueChar p κ K') (hZ₂ : Zl2ResidueChar p₂ κ₂ L')
    (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) :
    ((fun τ : Gal(K'/κ) => Φ τ) '' {τ | IsFrobeniusFor p q τ}) =
      {τ | IsFrobeniusFor p₂ q₂ τ} := by
  ext x
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (isFrobeniusFor_map_iff h h₂ hZ hZ₂ Φ τ).mp hτ
  · intro hx
    refine ⟨Φ.symm x, ?_, by simp⟩
    exact (isFrobeniusFor_map_iff h h₂ hZ hZ₂ Φ (Φ.symm x)).mpr (by simpa using hx)

/-- **Membership in the inertia subgroup is preserved by `Φ`**: the unramified quotients
`G_κ/I_κ` and `G_κ₂/I_κ₂` are identified by `Φ`. -/
theorem mem_inertia_map_iff {p p₂ q q₂ : ℕ} (h : TameData p q κ K') (h₂ : TameData p₂ q₂ κ₂ L')
    (hp : p = p₂) (Φ : Gal(K'/κ) ≃* Gal(L'/κ₂)) (τ : Gal(K'/κ)) :
    Φ τ ∈ inertiaSubgroup (κ := κ₂) (K' := L') p₂ ↔
      τ ∈ inertiaSubgroup (κ := κ) (K' := K') p := by
  rw [← mulEquiv_maps_inertia h h₂ hp Φ]
  constructor
  · rintro ⟨x, hx, hxτ⟩
    have hx' : x = τ := Φ.injective hxτ
    rwa [hx'] at hx
  · intro hτ
    exact ⟨τ, hτ, rfl⟩

/-- **The Frobenius lifts form a coset of the inertia subgroup**: if `τ` is a Frobenius lift and
`ν ∈ I_κ`, then `ν * τ` is again a Frobenius lift.  (Consequently the set of Frobenius lifts is
the preimage in `G_κ` of the Frobenius class in the unramified quotient `G_κ/I_κ`.) -/
theorem IsFrobeniusFor.mul_mem_inertia {p q : ℕ} (h : TameData p q κ K')
    {τ : Gal(K'/κ)} (hτ : IsFrobeniusFor p q τ) {ν : Gal(K'/κ)}
    (hν : ν ∈ inertiaSubgroup (κ := κ) (K' := K') p) : IsFrobeniusFor p q (ν * τ) := by
  rw [h.frobeniusLift.iff] at hτ ⊢
  exact isTameFrobeniusLift_mul_mem_inertia (wildInertiaSubgroup_normal p)
    h.structure_input.wildInertia_le_inertia h.structure_input.tameInertia_commutator_mem hτ hν

/-- The converse of `IsFrobeniusFor.mul_mem_inertia`: multiplying a Frobenius lift on the left by
an inertia element does not change the Frobenius-lift property, so the Frobenius lifts form a
coset of `I_κ` in `G_κ`. -/
theorem IsFrobeniusFor.of_mul_mem_inertia {p q : ℕ} (h : TameData p q κ K')
    {τ ν : Gal(K'/κ)} (hν : ν ∈ inertiaSubgroup (κ := κ) (K' := K') p)
    (hτ : IsFrobeniusFor p q (ν * τ)) : IsFrobeniusFor p q τ := by
  rw [h.frobeniusLift.iff] at hτ ⊢
  exact isTameFrobeniusLift_of_mul_mem_inertia (wildInertiaSubgroup_normal p)
    h.structure_input.wildInertia_le_inertia h.structure_input.tameInertia_commutator_mem hν hτ

end

end NK.LocalTame
