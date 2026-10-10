import Mathlib
import ChallengeDeps
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# `Work.MotA` — the basic-open chapter of the Lin–Shinder development

This area provides the *commutative-algebraic* half of the project (audit nodes `A1`, `A2a`,
`A2b`, `A4`, `A1P`, `A3`): the reduction of the non-vanishing of the part-`A` invariant `cInv` to
an explicit computation with polynomials, their prime factors and the residue fields of the
corresponding height-one primes.

## Conventions fixed here

* `polyRing 𝕜 n = MvPolynomial (Fin n) 𝕜` is the coordinate ring `𝕜[x₁,…,xₙ]`;
* `polySpec 𝕜 n = Spec 𝕜[x₁,…,xₙ]` is affine `n`-space in the `PrimeSpectrum` model, equipped
  with the structure map over `Spec 𝕜` coming from `algebraMap 𝕜 𝕜[x]`
  (`Work.MotA.instOverPolySpec`) and with a `Variety 𝕜` instance
  (`Work.MotA.instVarietyPolySpec`);
* `Work.MotA.polySpecIsoAffine 𝕜 n : polySpec 𝕜 n ≅ 𝔸(Fin n; Spec 𝕜)` is the canonical
  identification with `MotivicInvariants`' affine space (Mathlib's `AffineSpace.SpecIso`), so that
  statements about `polySpec` can be transported to `Cr 𝕜 n`;
* `Work.MotA.divCount 𝕜 n F z` counts the codimension-one points of `polySpec 𝕜 n` that lie on
  `V(F)` (i.e. `F ∈ x.asIdeal`) and whose residue field is `𝕜`-isomorphic to `κ(z)`.  For a
  *prime* `F` (and more generally for any nonzero `F`) this is exactly the number of exceptional
  divisors of the birational map inverse to the open immersion `D(F) ↪ 𝔸ⁿ` whose birational class
  is that of `z` — see `Work.MotA.excCount_partialIsoOfDense_symm` and the main formula
  `Work.MotA.exists_awayBirationalMap_cInv`.
-/

noncomputable section

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

/-- The polynomial ring `𝕜[x₁, …, xₙ]`, the coordinate ring of affine `n`-space. -/
abbrev polyRing (𝕜 : Type) [Field 𝕜] (n : ℕ) : Type := MvPolynomial (Fin n) 𝕜

/-- Affine `n`-space over `𝕜`, in the model `Spec 𝕜[x₁, …, xₙ]`.  Its points are the prime ideals
of `𝕜[x₁, …, xₙ]`, so that `x.asIdeal`, `Ideal.height x.asIdeal = Order.coheight x` etc. are
available directly. -/
abbrev polySpec (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme.{0} :=
  Spec (CommRingCat.of (MvPolynomial (Fin n) 𝕜))

/-- The structure morphism `Spec 𝕜[x₁,…,xₙ] ⟶ Spec 𝕜` of affine `n`-space over `𝕜`, induced by
the algebra structure `algebraMap 𝕜 𝕜[x₁,…,xₙ]`. -/
instance instOverPolySpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    (polySpec 𝕜 n).Over (Spec (.of 𝕜)) :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜)))⟩

/-- The structure morphism of `polySpec` is locally of finite type (`𝕜[x₁,…,xₙ]` is a finitely
generated `𝕜`-algebra). -/
theorem locallyOfFiniteType_polySpec (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    LocallyOfFiniteType ((polySpec 𝕜 n) ↘ (Spec (.of 𝕜))) := by
  show LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial (Fin n) 𝕜))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **Affine `n`-space is a variety over `𝕜`** in the `Spec 𝕜[x₁,…,xₙ]` model. -/
instance instVarietyPolySpec (𝕜 : Type) [Field 𝕜] (n : ℕ) : Variety 𝕜 (polySpec 𝕜 n) := by
  haveI := locallyOfFiniteType_polySpec 𝕜 n
  exact ⟨⟩

/-- The canonical isomorphism `Spec 𝕜[x₁,…,xₙ] ≅ 𝔸ⁿ` over `Spec 𝕜` (Mathlib's
`AffineSpace.SpecIso`).  It is the bridge between the `MvPolynomial`-based statements of this
area and the group `Cr 𝕜 n` of `MotivicInvariants`. -/
noncomputable def polySpecIsoAffine (𝕜 : Type) [Field 𝕜] (n : ℕ) :
    polySpec 𝕜 n ≅ 𝔸(Fin n; Spec (.of 𝕜)) :=
  (AffineSpace.SpecIso (Fin n) (CommRingCat.of 𝕜)).symm

/-- The basic open `D(F) ⊆ 𝔸ⁿ` (the complement of `V(F)`), for `F ∈ 𝕜[x₁,…,xₙ]`. -/
abbrev basicOpen (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜) :
    (polySpec 𝕜 n).Opens :=
  PrimeSpectrum.basicOpen F

/-- Membership in the basic open: `x ∈ D(F) ↔ F ∉ x.asIdeal`. -/
theorem mem_basicOpen_iff {𝕜 : Type} [Field 𝕜] {n : ℕ} {F : MvPolynomial (Fin n) 𝕜}
    {x : polySpec 𝕜 n} : x ∈ basicOpen 𝕜 n F ↔ F ∉ x.asIdeal :=
  PrimeSpectrum.mem_basicOpen F x

/-- The generic point of `𝔸ⁿ = Spec 𝕜[x₁,…,xₙ]`, i.e. the point defined by the zero ideal. -/
noncomputable abbrev genericPoint (𝕜 : Type) [Field 𝕜] (n : ℕ) : polySpec 𝕜 n :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- The basic open of a nonzero polynomial is dense in `𝔸ⁿ`. -/
theorem basicOpen_dense (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜)
    (hF : F ≠ 0) : Dense (basicOpen 𝕜 n F : Set (polySpec 𝕜 n)) := by
  have hne : (basicOpen 𝕜 n F : Set (polySpec 𝕜 n)).Nonempty :=
    ⟨genericPoint 𝕜 n, (mem_basicOpen_iff (𝕜 := 𝕜) (n := n) (F := F)
      (x := genericPoint 𝕜 n)).mpr (fun h => hF (Ideal.mem_bot.mp h))⟩
  exact IsOpen.dense (basicOpen 𝕜 n F).2 hne

/-- The point of `Spec 𝕜[x₁,…,xₙ]` defined by a prime element `p` (i.e. the height-one prime
ideal `(p)`). -/
noncomputable def primePoint (𝕜 : Type) [Field 𝕜] {n : ℕ} (p : MvPolynomial (Fin n) 𝕜)
    (hp : Prime p) : polySpec 𝕜 n :=
  ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩

/-- The birational map `𝔸ⁿ ⤏ D(F)` inverse to the open immersion of the basic open `D(F)`
(`F ≠ 0`).  Its exceptional divisors are exactly the codimension-one points of `𝔸ⁿ` at which `F`
vanishes; see `Work.MotA.excCount_basicOpenBirationalMap`. -/
noncomputable def basicOpenBirationalMap (𝕜 : Type) [Field 𝕜] (n : ℕ)
    (F : MvPolynomial (Fin n) 𝕜) (hF : F ≠ 0) [IrreducibleSpace ↑(basicOpen 𝕜 n F)] :
    (polySpec 𝕜 n).BirationalMap ↑(basicOpen 𝕜 n F) :=
  ((basicOpen 𝕜 n F).partialIsoOfDense (basicOpen_dense 𝕜 n F hF)).symm.toBirationalMap

/-- `divCount 𝕜 n F z` is the number of codimension-one points `x` of `𝔸ⁿ = Spec 𝕜[x₁,…,xₙ]` at
which `F` vanishes (`F ∈ x.asIdeal`) and whose residue field is `𝕜`-isomorphic to `κ(z)`.

For `F ≠ 0` this is the weight of the exceptional divisors of the birational map
`𝔸ⁿ ⤏ D(F)` (the inverse of the open immersion of the basic open `D(F)`) at the base point `z`;
this is the content of `Work.MotA.exists_awayBirationalMap_cInv`.  Note that only the *prime*
factors of `F` matter, not their multiplicities: `F ∈ x.asIdeal ↔ rad (F) ⊆ x.asIdeal` for `x`
prime. -/
noncomputable def divCount (𝕜 : Type) [Field 𝕜] (n : ℕ) (F : MvPolynomial (Fin n) 𝕜)
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) : ℕ :=
  Set.ncard {x : polySpec 𝕜 n | Order.coheight x = 1 ∧ F ∈ x.asIdeal ∧ ResEquiv 𝕜 x z}

end Work.MotA

end
