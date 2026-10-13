import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSEQP.evalIdeal_ne_bot
import Submission.Work.DSEQP.gamma_finite

/-!
# `Work.DSEQP.area_GAMMA_proved`

The node **GAMMA** of the equal-characteristic-`p` route: for `A` a Noetherian domain, `X` an
integral scheme and `f : X ⟶ Spec A` proper, surjective and projective (a closed subscheme of
`ℙᴺ_A`), the `A`-module `Γ(X, ⊤)` admits an `A`-linear functional which does not vanish at `1`.

The proof has three inputs.

* `Work.DSEQP.gamma_finite` (the projective coherence theorem, proved in a sibling file): with
  `A` Noetherian and `f` projective, `Γ(X, ⊤)` is a *finitely generated* `A`-module.  This is
  Grothendieck's finiteness theorem for the global sections of `O_X`, transported to `Γ(X,⊤)`.
* `φ = DSMap.phi A X f : A →+* Γ(X, ⊤)` is *injective*: it is `f.appTop` composed with the
  canonical isomorphism `Γ(Spec A, ⊤) ≅ A`, and `f.appTop` is injective because `f` is
  surjective (hence dominant) and `Spec A` is reduced.
* `Work.DSEQP.evalIdeal_ne_bot`: for a finite, faithful (here: injective structure map) extension
  of a Noetherian domain, the evaluation ideal is nonzero, i.e. there is a functional which does
  not vanish at `1`.
-/

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DSMap
open scoped AlgebraicGeometry

namespace Work.DSEQP

universe a

/-- `DSMap.phi A X f` is `f.appTop` composed with the inverse of the canonical isomorphism
`Γ(Spec A, ⊤) ≅ A`. -/
theorem phi_eq_appTop_apply' (A : Type a) [CommRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) (a : A) :
    DSMap.phi A X f a = (f.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
  have hkey : (ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of A)))
      (CommRingCat.ofHom (DSMap.phi A X f)).op = f := Equiv.apply_symm_apply _ _
  have h := ΓSpec_adjunction_homEquiv_eq (X := X) (B := CommRingCat.of A)
    (CommRingCat.ofHom (DSMap.phi A X f))
  rw [hkey] at h
  rw [h]
  simp

/-- The structure map `A →+* Γ(X, ⊤)` of a surjective morphism onto `Spec A` with `A` a domain
is injective. -/
theorem phi_injective (A : Type a) [CommRing A] [IsDomain A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f) :
    Function.Injective (DSMap.phi A X f) := by
  haveI : IsDominant f := ⟨hs.denseRange⟩
  haveI : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have happ : Function.Injective (Scheme.Hom.app f ⊤).hom :=
    fun a b hab => Scheme.Hom.app_injective f ⊤ hab
  intro a b hab
  rw [phi_eq_appTop_apply' A X f a, phi_eq_appTop_apply' A X f b] at hab
  have h3 := happ hab
  have h2 := congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).hom) h3
  simpa using h2

theorem area_GAMMA_proved (A : Type a) [CommRing A] [IsDomain A] [IsNoetherianRing A] (X : Scheme.{a})
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hp : IsProjOver A f) :
    letI := (phi A X f).toAlgebra
    ∃ φ : Γ(X, ⊤) →ₗ[A] A, φ 1 ≠ 0 := by
  letI := (phi A X f).toAlgebra
  -- finiteness of `Γ(X,⊤)` over `A` (the projective coherence theorem)
  haveI hfin : Module.Finite A Γ(X, ⊤) := gamma_finite A X f hp
  have hinj : Function.Injective (algebraMap A Γ(X, ⊤)) := by
    have h : DSMap.phi A X f = algebraMap A Γ(X, ⊤) := rfl
    rw [← h]
    exact phi_injective A X f hs
  haveI : Nontrivial Γ(X, ⊤) := Function.Injective.nontrivial hinj
  have hne : Work.DSEQP.evalIdeal A Γ(X, ⊤) ≠ ⊥ :=
    Work.DSEQP.evalIdeal_ne_bot A Γ(X, ⊤) hinj
  exact (Work.DSEQP.evalIdeal_ne_bot_iff A Γ(X, ⊤)).mp hne

end Work.DSEQP
