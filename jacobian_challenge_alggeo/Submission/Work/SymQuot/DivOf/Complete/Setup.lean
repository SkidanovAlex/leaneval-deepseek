/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The point of `Symⁿ C` attached to an effective divisor of degree `n` (area SY)

This file collects the *definitions* used in the construction of the point `p_D` of `Symⁿ C`
attached to an effective divisor `D` of degree `n` on `C_F` (the completeness half of the
point/divisor dictionary, `Submission/Work/NOTES_LEAD_jacobian_divof.md` §5):

* `idealOfDiv` — the ideal `∏_z m_z^{D(z)} ⊆ Γ(C_F, V_F)` of definition of `D`;
* `ptVal` — the value map `Γ(C,V) →+* S` of an `S`-point of an affine open `V ⊆ C`;
* `ptOfAlgHom` — an `S`-point of the affine open `V ⊆ C` from a `K`-algebra homomorphism
  `Γ(C,V) →ₐ[K] S`;
* `evalAlg` — evaluation of a regular function on `Vⁿ ⊆ Cⁿ` at `n` points.

The factorisation of the construction of `p_D` through these is described in
`Submission/Work/SymQuot/NOTES.md`.
-/
import Submission.Work.SymQuot.DivOf.DivOf
import Submission.Work.SymQuot.DivOf.SymChart
import Submission.Work.SymQuot.DivOf.CharIdealGenDefs
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.ProdOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.DivOf

open Work.CurveBasics

variable {K : Type u} [Field K] {C : Curve K} {n : ℕ}

/-- **The ideal of definition of a divisor** supported in an affine open `V`: the product of the
maximal ideals `m_z` of the places `z` in the support, to the power `D z`. -/
noncomputable def idealOfDiv (C : Curve K) (V : C.left.Opens) [Nonempty V]
    (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)] (D : C.Div)
    (hs : ∀ z ∈ D.support, z.point ∈ V) : Ideal Γ(C.left, V) :=
  ∏ z ∈ D.support.attach, placeIdeal C V ↑z (hs ↑z z.2) ^ (D ↑z).toNat

/-- **The value map of an `S`-point of an affine open `V ⊆ C`**: the pullback of regular
functions along the point, using that its image lies in `V`. -/
noncomputable def ptVal (C : Curve K) (V : C.left.Opens) {S : Type u} [CommRing S]
    [Algebra K S] (x : Work.SpecLin.RPt C.toOver S) (h : ⊤ ≤ x.left ⁻¹ᵁ V) :
    Γ(C.left, V) →+* S :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom).comp
    ((Scheme.Hom.appLE x.left V ⊤ h).hom)

/-- **Evaluation of a regular function on `Vⁿ` at `n` points**: the pullback of sections along
`Π_m x_m : Spec S ⟶ Cⁿ`, using that the image lies in the product open `Vⁿ`. -/
noncomputable def evalAlg (C : Curve K) (V : C.left.Opens) (n : ℕ) {S : Type u} [CommRing S]
    [Algebra K S] (x : Fin n → Work.SpecLin.RPt C.toOver S)
    (h : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶ prod C.toOver n).left ⁻¹ᵁ
      piOpen C.toOver V n) : Γ((prod C.toOver n).left, piOpen C.toOver V n) →+* S :=
  ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom).comp
    ((Scheme.Hom.appLE (Limits.Pi.lift x).left (piOpen C.toOver V n) ⊤ h).hom)

/-- **An `S`-point of the affine open `V ⊆ C` from a `K`-algebra homomorphism of its sections**:
the composite `Spec S ⟶ Spec Γ(C,V) ⟶ C` of the point of `Spec Γ(C,V)` with the canonical
immersion of the affine open. -/
noncomputable def ptOfAlgHom (C : Curve K) {V : C.left.Opens} (hV : IsAffineOpen V) {S : Type u}
    [CommRing S] [Algebra K S] (κ : Γ(C.left, V) →ₐ[K] S) : Work.SpecLin.RPt C.toOver S :=
  Over.homMk ((Work.SpecLin.specOfMap (K := K) κ).left ≫ hV.fromSpec) (by
    have h1 : hV.fromSpec ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.left, V))) :=
      (Curve.specMap_algebraMap_sections C hV).symm
    rw [Category.assoc, h1]
    change Spec.map (CommRingCat.ofHom κ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(C.left, V))) =
      Spec.map (CommRingCat.ofHom (algebraMap K S))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext k
    exact κ.commutes k)

/-- **The constant sections of the chart of `Vⁿ`**, as a ring homomorphism
`K →+* Γ(Cⁿ,Vⁿ)^{S_n}`: the composite `Spec Γ(Cⁿ,Vⁿ)^{S_n} ⟶ Symⁿ C ⟶ Spec K` of the chart
inclusion with the structure morphism, read off on global sections.  It is the "structure ring
map" of the chart. -/
noncomputable def chartConst (C : Curve K) (n : ℕ) [NeZero n] [CurveAffineCover C]
    (U : (symData C n).Chart) :
    K →+* ↥(chartInvariants (C := C) (n := n) U.1 U.2.2) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    ((symData C n).chartι U ≫ (Sym C n).hom).appTop ≫
    (Scheme.ΓSpecIso (GAction.chartRing (symAction C n) U.1 U.2.2)).hom).hom

end Work.SymQuot.DivOf
