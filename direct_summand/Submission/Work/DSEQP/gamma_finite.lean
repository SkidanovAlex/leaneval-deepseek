import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSEQP.gf_isProjOver_isProper
import Submission.Work.DSCOH.chartCech_finite_vanishing
import Submission.Work.DSEQP.gf_bridge

/-!
# `Work.DSEQP.gamma_finite` — `Γ(X, 𝒪_X)` is a finite `A`-module for `X` projective over `A`

The target statement of this file is the node `gamma_finite` of the equal-characteristic-`p`
route of the direct-summand project:

```
theorem gamma_finite (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (hp : DSMap.IsProjOver A f) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (op ⊤))
```

i.e. Grothendieck's finiteness theorem for the *global sections* of the structure sheaf of a
closed subscheme of `ℙᴺ_A` over a Noetherian ring `A`.

## Route

Mathlib supplies one half of the statement in the form of the *integrality* of the map on global
sections of any universally closed morphism over an affine base,
`AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`.  Combined with the classical theorem
"integral + finitely generated ⟹ finite" (`RingHom.finite_iff_isIntegral_and_finiteType`) the
target is therefore *equivalent* to

  `Algebra.FiniteType A Γ(X, ⊤)`  ("`Γ(X, ⊤)` is a finitely generated `A`-algebra").

This file records that reduction rigorously (`gamma_finite_of_finiteType`), together with the
elementary facts about `DSMap.phi` that it needs (`phi_eq_appTop_apply`).

The remaining input — the finite generation of `Γ(X, ⊤)` as an `A`-algebra, which is the
coherence theorem for the structure sheaf of a projective scheme (Serre/EGA III 3.2.1) — is the
content of the sibling developments; the file
`Submission.Work.DSEQP.gamma_finite_coh` records the interface it is used through.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.DSEQP

universe a

/-- `DSMap.phi A X f` is `f.appTop` composed with the inverse of the canonical isomorphism
`Γ(Spec A, ⊤) ≅ A`; this is the structural identity relating the challenge's `φ` to the map on
global sections induced by `f`. -/
theorem phi_eq_appTop_apply (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (a : A) :
    DSMap.phi A X f a = (f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hkey : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A)))
      (CommRingCat.ofHom (DSMap.phi A X f)).op = f := Equiv.apply_symm_apply _ _
  have h := ΓSpec_adjunction_homEquiv_eq (X := X) (B := CommRingCat.of A)
    (CommRingCat.ofHom (DSMap.phi A X f))
  rw [hkey] at h
  rw [h]
  simp

/-- The structure map `A → Γ(X, ⊤)` induced by `f` is integral, whenever `f` is universally
closed (e.g. proper) over the affine scheme `Spec A`.  This is Mathlib's
`isIntegral_appTop_of_universallyClosed`, transported across `phi_eq_appTop_apply`. -/
theorem phi_isIntegral (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [UniversallyClosed f] : (DSMap.phi A X f).IsIntegral := by
  have hcomp : (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) =
      DSMap.phi A X f := by
    ext a
    exact (phi_eq_appTop_apply A X f a).symm
  rw [← hcomp]
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

/-- **The reduction**: for a universally closed `f` (in particular for `f` proper, which is what
`IsProjOver` gives), the finiteness of `Γ(X, ⊤)` over `A` follows from the finite generation of
`Γ(X, ⊤)` as an `A`-algebra. -/
theorem gamma_finite_of_finiteType (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [UniversallyClosed f]
    (hft : letI := (DSMap.phi A X f).toAlgebra
      Algebra.FiniteType A ↥(X.presheaf.obj (Opposite.op ⊤))) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (Opposite.op ⊤)) := by
  letI := (DSMap.phi A X f).toAlgebra
  have hint : (algebraMap A ↥(X.presheaf.obj (Opposite.op ⊤))).IsIntegral :=
    phi_isIntegral A X f
  have hfin : (algebraMap A ↥(X.presheaf.obj (Opposite.op ⊤))).Finite := by
    rw [RingHom.finite_iff_isIntegral_and_finiteType]
    exact ⟨hint, hft⟩
  exact RingHom.finite_algebraMap.mp hfin

theorem gamma_finite_of_finiteType_proj (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (hp : DSMap.IsProjOver A f)
    (hft : letI := (DSMap.phi A X f).toAlgebra
      Algebra.FiniteType A ↥(X.presheaf.obj (Opposite.op ⊤))) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (Opposite.op ⊤)) := by
  haveI : IsProper f := gf_isProjOver_isProper A X f hp
  exact gamma_finite_of_finiteType A X f hft

/-- **The assembly**: given the geometric bridge — a finitely generated graded module over
`A[x₀,…,x_N]` whose chart Čech cohomology in degree `0` computes `Γ(X, ⊤)` — the target follows
from Serre's finiteness theorem for the chart Čech complex of a finitely generated graded module,
`Work.DSCOH.chartCech_finite_vanishing`. -/
theorem gamma_finite_of_bridge (A : Type a) [CommRing A] [IsNoetherianRing A] {N : ℕ}
    {X : Scheme.{a}} (f : X ⟶ Spec (.of A))
    (M : Type a) [AddCommGroup M] [Module A M] [Module (MvPolynomial (Fin (N + 1)) A) M]
    [IsScalarTower A (MvPolynomial (Fin (N + 1)) A) M] (ℳ : ℕ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) ℳ]
    [Module.Finite (MvPolynomial (Fin (N + 1)) A) M]
    (h : letI := (DSMap.phi A X f).toAlgebra
      Nonempty (↥(X.presheaf.obj (Opposite.op ⊤)) ≃ₗ[A]
        ↥((Work.DSCOH.chartCech (A := A) (n := N + 1) (M := M) ℳ).homology 0))) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (Opposite.op ⊤)) := by
  letI := (DSMap.phi A X f).toAlgebra
  have h0 : Module.Finite A
      ↥((Work.DSCOH.chartCech (A := A) (n := N + 1) (M := M) ℳ).homology 0) :=
    (Work.DSCOH.chartCech_finite_vanishing (A := A) (n := N + 1) (M := M) ℳ).1 0
  obtain ⟨e⟩ := h
  exact Module.Finite.equiv e.symm

/-- The target of this file, given the geometric bridge `Work.DSEQP.gf_bridge`. -/
theorem gamma_finite_of_gf_bridge (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (hp : DSMap.IsProjOver A f)
    (hbridge : ∀ {N : ℕ} (i : X ⟶ DSMap.PSpace A N), IsClosedImmersion i →
      i ≫ DSMap.PSpace.toSpec A N = f → ∃ (M : Type a) (h1 : AddCommGroup M) (h2 : Module A M)
        (h3 : Module (MvPolynomial (Fin (N + 1)) A) M)
        (h4 : IsScalarTower A (MvPolynomial (Fin (N + 1)) A) M)
        (ℳ : ℕ → Submodule A M) (h5 : DirectSum.Decomposition ℳ)
        (h6 : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) ℳ)
        (h7 : Module.Finite (MvPolynomial (Fin (N + 1)) A) M),
        letI := h1; letI := h2; letI := h3; letI := h4; letI := h5; letI := h6; letI := h7
        letI := (DSMap.phi A X f).toAlgebra
        Nonempty (↥(X.presheaf.obj (Opposite.op ⊤)) ≃ₗ[A]
          ↥((Work.DSCOH.chartCech (A := A) (n := N + 1) (M := M) ℳ).homology 0))) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (Opposite.op ⊤)) := by
  obtain ⟨N, i, hi, hif⟩ := hp
  obtain ⟨M, h1, h2, h3, h4, ℳ, h5, h6, h7, h⟩ := hbridge i hi hif
  letI := h1; letI := h2; letI := h3; letI := h4; letI := h5; letI := h6; letI := h7
  exact gamma_finite_of_bridge A f M ℳ h

theorem gamma_finite (A : Type a) [CommRing A] [IsNoetherianRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (hp : DSMap.IsProjOver A f) :
    letI := (DSMap.phi A X f).toAlgebra
    Module.Finite A ↥(X.presheaf.obj (Opposite.op ⊤)) :=
  gamma_finite_of_gf_bridge A X f hp (fun i hi hif => gf_bridge A i hi f hif)

end Work.DSEQP
