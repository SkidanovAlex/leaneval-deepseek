import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.CechBicomp

/-!
# `Work.DSEQ0` : definitions for the Euler-characteristic lemma `eulerChar_ne_zero`

The target of `Submission/Work/DSEQ0/eulerChar_ne_zero.lean` is

`Σ_{i ∈ [lo,hi]} (-1)^i rk (F^i) ≠ 0` for a bounded complex `F` of finite free `A`-modules
quasi-isomorphic to the Čech complex `Č(U; 𝒪_X)` of a finite affine cover of a scheme `X` proper,
surjective and generically finite over `Spec A`, with `A` a Noetherian domain.

The number is the *generic degree*: it equals `dim_K (K ⊗_A Γ(X,⊤))` for `K = Frac A`.  The proof
localises at a single element `g` such that `f` is finite over `D(g)` (this exists because `f` is
generically finite), where the Čech complex becomes a resolution of the affine scheme
`W = f ⁻¹ᵁ D(g)`; this file records the two objects involved:

* `awayOpen A X f g = f ⁻¹ᵁ D(g)`;
* `curryPresheaf A X f W`, the presheaf `V ↦ Γ(X, W ⊓ V)` whose Čech complex along `U` is the
  "restricted" Čech complex of the affine scheme `W`;
* `cechZAway A X f U g`, the base change of `Č(U; 𝒪_X)` along `A → A_g = Localization.Away g`.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe a

noncomputable section

variable (A : Type a) [CommRing A]

/-- `W = f ⁻¹ᵁ D(g)`, the open subscheme of `X` on which the global section `g` becomes
invertible. -/
noncomputable def awayOpen (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (g : A) : X.Opens :=
  f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (AlgebraicGeometry.Spec (.of A)).Opens)

/-- The presheaf of `A`-modules `V ↦ Γ(X, W ⊓ V)` on `X`; its Čech complex along a family of
opens `U` is the Čech complex of the cover `{W ⊓ U i}` of the open subscheme `W`. -/
noncomputable def curryPresheaf (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (W : X.Opens) :
    X.Opensᵒᵖ ⥤ ModuleCat.{a} A :=
  (cechPresheafCurry f).obj (Opposite.op W)

/-- The base change of the Čech complex `Č(U; 𝒪_X)` along `A → A_g`. -/
noncomputable def cechZAway (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type a} (U : ι → X.Opens) (g : A) :
    CochainComplex (ModuleCat.{a} (Localization.Away g)) ℤ :=
  ((ModuleCat.extendScalars (algebraMap A (Localization.Away g))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (DSMap.cechZ A X f U)

/-- The Čech complex (over `ℤ`) of the curried presheaf at `W`. -/
noncomputable def curryComplexZ (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (W : X.Opens) {ι : Type a} (U : ι → X.Opens) :
    CochainComplex (ModuleCat.{a} A) ℤ :=
  (((CategoryTheory.cechComplexFunctor U).obj (curryPresheaf A X f W)).extend
    ComplexShape.embeddingUpNat)

end

end Work.DSEQ0
