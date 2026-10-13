import Mathlib
import Submission.Work.DSG4a.Split

/-!
# DSG4a: the chain-level splitting condition and the interface to `DSplit`

The local-to-global area `G4a` has two halves.

* The **algebraic half** (`Split.lean`, `Present.lean`, `Flat.lean`, `LocalGlobal.lean`):
  if an element `e` of a finitely presented `A`-module becomes unimodular
  (`Module.IsUnimodular`) after a flat local base change `A → A'` over every maximal ideal,
  then it was already unimodular over `A`.
* The **interface half** (this file): the derived condition `DSplit A X f` of the frozen
  proof map — equivalently, of the challenge statement — is, once a K-projective finite
  free model `P` of `RΓ(X, 𝒪)` is available (this is the output of the areas `F1` and
  `COH`), *equivalent* to the chain-level condition `ChainSplit` on the representative
  `cc : A[0] → P` of the unit, and hence to the algebra of the first half applied to
  `coker (d⁻¹ : P.X (-1) → P.X 0)`.

Concretely, with `P` a cochain complex of `A`-modules and

`cc : (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj (ModuleCat.of A A) ⟶ P`

a chain map (a "coaugmentation"), the two notions are:

* `ChainSplit P cc` : there is an `A`-linear `s : P.X 0 →ₗ[A] A` with `s ∘ d⁻¹ = 0` and
  `s (coaugElem P cc) = 1`, where `coaugElem P cc = cc.f 0 (1)` is the class of the unit
  (`singleObjXSelf` transports `1 : A` into degree `0` of the single complex).  For
  complexes concentrated in degrees `≤ 0` this is exactly a retraction of `cc` at the level
  of chain complexes.
* `modelModule P` : the finitely presented module `P.X 0 ⧸ im (d⁻¹)`, and `modelElem cc`
  its element `[coaugElem P cc]`.  Then `ChainSplit P cc ↔ Module.IsUnimodular A (modelElem cc)`
  (`chainSplit_iff_isUnimodular`), which is the bridge to `splitIdeal`/`Module.IsUnimodular`
  and hence to the flat base change and local-to-global theorems of this area.

## Status, and how it connects

1. `isSplitMono_Q_map_iff_chainSplit` (module
   `Submission.Work.DSG4a.isSplitMono_Q_map_iff_chainSplit`): for a K-projective `P`,
   `IsSplitMono (Q.map cc)` iff `ChainSplit P cc`.  Proved: `IsSplitMono` is "there exists a
   retraction"; maps `Q P ⟶ Q (single A)` out of a K-projective complex are homotopy classes
   of chain maps (`CochainComplex.IsKProjective.Qh_map_bijective`, transported along
   `DerivedCategory.quotientCompQhIso`), and a chain map `P ⟶ single A` is the same as a
   linear map `P.X 0 →ₗ[A] A` killed by `d⁻¹`.
2. `isSplitMono_rgUnit_iff_chainSplit` (module
   `Submission.Work.DSG4a.isSplitMono_rgUnit_iff_chainSplit`, with the definitions of
   `F1UnitCompatible` and `unitComparison` in `Submission.Work.DSG4a.F1Interface`): the same
   statement for the challenge's own unit `rgUnit A X f` in `D⁺(A)`, given precisely the
   compatibility clause of the frozen `area_F1_cech`.  Composing it with
   `chainSplit_iff_isUnimodular` turns the *statement* of the area `F1` (plus the finiteness
   of `COH` needed to replace `cechZ` by a K-projective finite free complex, and the choice of
   bases) into the model criterion `DSplit A X f ↔ Module.IsUnimodular A e` used by the
   local-to-global algebra of this area.
3. The flat base change of the model: if `P` is a model of `RΓ(X, 𝒪)` then `P ⊗_A A'` is a
   model of `RΓ(X_{A'}, 𝒪)`, with `ChainSplit`/`modelElem` carried along (this is the
   Čech-flatness statement of the area `F1`).  Not available here.

Given 1–3, the frozen `area_G4a_localGlobal` is proved by: fix the ambient derived
category instances; take a model `P` of `X` over `A` and the corresponding element
`e = modelElem cc` of `modelModule P`; for each maximal ideal `𝔪`, the hypothesis gives a
flat local `ψ : A → A'` over `𝔪` and a splitting over `A'`; by 3 and 1–2 (over `A'`) the
base change `1 ⊗ e` is unimodular; by `isUnimodular_of_forall_maximal` the element `e` is
unimodular over `A`; by 1–2 again, `DSplit A X f` holds.  This is exactly
`area_G4a_localGlobal_of_models` of `Submission.Work.DSG4a.Main`.
-/

namespace Work.DSG4a

open CategoryTheory

universe u

namespace Criterion

/-- The element `cc.f 0 1 ∈ P.X 0` of a coaugmentation `cc : A[0] ⟶ P`: the image of the
unit of `A` under `cc` in degree `0`, using the canonical isomorphism
`(single A).X 0 ≅ A` (`HomologicalComplex.singleObjXSelf`). -/
noncomputable def coaugElem {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) : P.X 0 :=
  ModuleCat.Hom.hom ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of A A)).inv ≫ cc.f 0) (1 : A)

/-- The chain-level splitting condition for a coaugmentation `cc : A[0] ⟶ P` of a cochain
complex `P` of `A`-modules: there is an `A`-linear functional `s` on `P.X 0` which vanishes
on the image of the differential `d⁻¹ : P.X (-1) ⟶ P.X 0` and takes the value `1` at
`cc.f 0 1`.  For complexes concentrated in degrees `≤ 0` this is exactly a retraction of
`cc` at the level of chain complexes. -/
def ChainSplit {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) : Prop :=
  ∃ s : P.X 0 →ₗ[A] A, s.comp (P.d (-1) 0).hom = 0 ∧ s (coaugElem P cc) = 1

/-- The finitely presented module `coker (d⁻¹ : P.X (-1) ⟶ P.X 0)` attached to a model `P`
of `RΓ(X, 𝒪)`: it is the module whose unimodularity is equivalent to splitting. -/
abbrev modelModule {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    Type u :=
  P.X 0 ⧸ LinearMap.range (P.d (-1) 0).hom

/-- The class of `cc.f 0 1` in `modelModule P`. -/
noncomputable def modelElem {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ P) : modelModule P :=
  Submodule.mkQ _ (coaugElem P cc)

end Criterion

end Work.DSG4a
