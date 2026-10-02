import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.PontryaginThom.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# The Grassmann chapter instantiates `Work.ThomBordism.PontryaginThom.ThomTarget`

The Pontryagin–Thom chapter (`Submission/Work/ThomBordism/PontryaginThom/Defs.lean`) fixes the
interface `ThomTarget k` of the *universal Thom space*: a based space `T` (in the application the
Thom space `Th(γ)` of the tautological oriented `k`-plane bundle over `G̃r_k(ℝ^{k+m})`), the two
degree-`(k+8)` classes `p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U`, the `(k-1)`-connectedness of `T`, and the
property that the two classes detect torsion.

This module is the bridge: it produces that structure from the model of `Grassmann/Model.lean`.
Because the workspace has no identification `H^*(Th(γ)) ≅ H^*(D γ, S γ)` (excision for the quotient
of a good pair), the two classes are *not* constructed here; their existence-and-detection property
is recorded as the `Prop` `ThomSpaceTorsionDetected` (which is how the Thom isomorphism is actually
consumed).  The two remaining mathematical inputs are exactly

* `ThomSpaceConnected k m` — item 3 of the chapter (the `(k-1)`-connectedness of `Th(γ)`);
* `ThomSpaceTorsionDetected k m` — the coherent form of item 2 (`H^{k+8}(Th(γ);ℚ) = ℚ{p₁²U, p₂U}`,
  which by `ThomPairCohomology` is equivalent to `H^{k+8}(D γ,S γ;ℚ) = ℚ{p₁²U, p₂U}`).

Note that this module imports a sibling area; it is deliberately *separate* from `Grassmann/Model`
so that a consumer of the model alone does not depend on `PontryaginThom`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology
open CategoryTheory

noncomputable section

/-- **The degree-`(k+8)` cohomology classes of the Thom space of the tautological bundle, and the
torsion-detection property.**

Existentially: there are classes `p1sqU`, `p2U ∈ H^{k+8}(Th(γ);ℤ)` — the images of
`p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U` under the identification `H^{k+8}(Th γ;ℤ) ≅ H^{k+8}(Dγ,Sγ;ℤ)` — such
that an integral homology class of degree `k+8` pairing to zero with both is torsion.  Over `ℚ` the
two classes are a basis of the dual, so this is the coefficient-free form of
`H^{k+8}(Th γ;ℚ) = ℚ{p₁²U, p₂U}` (`Thγ` is the Thom space of a rank-`k` bundle, so it has no
homology below degree `k` and its top relative class is the Thom class). -/
def ThomSpaceTorsionDetected (k m : ℕ) : Prop :=
  ∃ p1sqU p2U : (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8),
    ∀ y : (Work.Cohomology.chainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8),
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) p1sqU y = 0 →
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) p2U y = 0 →
      ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0

/-- **The universal Thom target of the Grassmann chapter.**  From

* `ThomSpaceConnected k m` — the `(k-1)`-connectedness of `Th(γ)` (item 3), and
* `ThomSpaceTorsionDetected k m` — the two Thom classes and their torsion-detection property
  (item 2 in the form the Pontryagin–Thom chapter consumes),

the Pontryagin–Thom chapter's `ThomTarget k` with `T = Th(γ)` exists. -/
theorem nonempty_thomTarget (k m : ℕ) (hconn : ThomSpaceConnected k m)
    (hdet : ThomSpaceTorsionDetected k m) :
    Nonempty (Work.ThomBordism.PontryaginThom.ThomTarget k) := by
  obtain ⟨a, b, hab⟩ := hdet
  exact ⟨{ T := TautologicalThomSpace k m
           t₀ := thomBasepoint k m
           p1sqU := a
           p2U := b
           connected := hconn
           detects_torsion := hab }⟩

/-- The `T` of `nonempty_thomTarget` is the Thom space of the tautological bundle. -/
theorem thomTarget_connected_spec (k m : ℕ) : ThomSpaceConnected k m ↔
    (∀ i < k, Subsingleton (HomotopyGroup (Fin i) (TautologicalThomSpace k m)
      (thomBasepoint k m))) := Iff.rfl

/-! ## The two classes of the Thom space, named: `p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U`

The Pontryagin–Thom chapter needs the classes `p₁²U`, `p₂U` of the *space* `T = Th(γ)` to be
*specifically* the Thom-isomorphism images of `p₁(γ)²` and `p₂(γ)` (the Hurewicz pairings of the
Pontryagin–Thom class of a normal bundle with exactly those classes are the *normal* Pontryagin
numbers of the manifold).  So the existential form `ThomSpaceTorsionDetected` above is not enough:
the classes must be named.  Since the workspace has no canonical map
`H^{k+8}(T;ℤ) → H^{k+8}(Dγ,Sγ;ℤ)` (the comparison is the excision/good-pair isomorphism, recorded
here as the *data* `Φ`), the identification is an input, and the classes are
`Φ (p₁(γ)² ⌣ U)` and `Φ (p₂(γ) ⌣ U)`. -/

/-- **The class `p₁(γ)² ⌣ U` of the Thom space**, transported along a prescribed identification `Φ`
of the degree-`(k+8)` cohomology of the Thom space with the relative cohomology of the Thom pair. -/
noncomputable def thomSpaceClass1 (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8)) :
    (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8) :=
  Φ (Work.Thom.thomMap (tautologicalBundle k m) k U.τ 8 (p1Sq k m))

/-- **The class `p₂(γ) ⌣ U` of the Thom space**, transported along the same identification `Φ`. -/
noncomputable def thomSpaceClass2 (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8)) :
    (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8) :=
  Φ (Work.Thom.thomMap (tautologicalBundle k m) k U.τ 8 (p2 k m))

/-- **The two named classes detect torsion**: an integral homology class of degree `k+8` whose
Kronecker pairings with `p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U` vanish is torsion.  This is the
coefficient-free form of `H^{k+8}(Th γ;ℚ) = ℚ{p₁²U, p₂U}` for the *named* classes (which is what the
Pontryagin–Thom chapter consumes). -/
def ThomSpaceClassesDetect (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8)) : Prop :=
  ∀ y : (Work.Cohomology.chainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8),
    Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8)
        (thomSpaceClass1 k m U Φ) y = 0 →
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8)
        (thomSpaceClass2 k m U Φ) y = 0 →
      ∃ N : ℕ, 0 < N ∧ (N : ℤ) • y = 0

/-- **The universal Thom target of the Grassmann chapter, with its classes named.**  Given

* `ThomSpaceConnected k m` — the `(k-1)`-connectedness of `Th(γ)` (item 3),
* a Thom class `U` of `γ` (`tautologicalThomClass k m`),
* an identification `Φ` of the degree-`(k+8)` cohomology of `Th(γ)` with the relative cohomology of
  the Thom pair (the excision/good-pair isomorphism),
* and the detection property of the two *named* classes (`ThomSpaceClassesDetect`),

this is the `Work.ThomBordism.PontryaginThom.ThomTarget k` whose space is `Th(γ)` and whose two
classes are `p₁(γ)² ⌣ U` and `p₂(γ) ⌣ U` — with the identifications exported by
`grassmannThomTarget_T`, `grassmannThomTarget_p1sqU`, `grassmannThomTarget_p2U`. -/
noncomputable def grassmannThomTarget (k m : ℕ) (hconn : ThomSpaceConnected k m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
    (hdet : ThomSpaceClassesDetect k m U Φ) :
    Work.ThomBordism.PontryaginThom.ThomTarget k where
  T := TautologicalThomSpace k m
  t₀ := thomBasepoint k m
  p1sqU := thomSpaceClass1 k m U Φ
  p2U := thomSpaceClass2 k m U Φ
  connected := hconn
  detects_torsion := hdet

/-- The space of `grassmannThomTarget` is the Thom space of the tautological bundle. -/
theorem grassmannThomTarget_T (k m : ℕ) (hconn : ThomSpaceConnected k m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
    (hdet : ThomSpaceClassesDetect k m U Φ) :
    (grassmannThomTarget k m hconn U Φ hdet).T = TautologicalThomSpace k m := rfl

/-- **The first class of `grassmannThomTarget` is `p₁(γ)² ⌣ U`**: it is the Thom image of
`p₁(γ)²` under the prescribed identification. -/
theorem grassmannThomTarget_p1sqU (k m : ℕ) (hconn : ThomSpaceConnected k m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
    (hdet : ThomSpaceClassesDetect k m U Φ) :
    (grassmannThomTarget k m hconn U Φ hdet).p1sqU = thomSpaceClass1 k m U Φ := rfl

/-- **The second class of `grassmannThomTarget` is `p₂(γ) ⌣ U`**. -/
theorem grassmannThomTarget_p2U (k m : ℕ) (hconn : ThomSpaceConnected k m)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
    (hdet : ThomSpaceClassesDetect k m U Φ) :
    (grassmannThomTarget k m hconn U Φ hdet).p2U = thomSpaceClass2 k m U Φ := rfl

/-- The named-classes detection property is a special case of the existential one (so the existing
`nonempty_thomTarget` is the weaker interface). -/
theorem thomSpaceTorsionDetected_of_classes (k m : ℕ)
    (U : Work.Thom.ThomClass (tautologicalBundle k m) k)
    (Φ : Work.Thom.OpenThom (tautologicalBundle k m) (8 + k) ≃ₗ[ℤ]
      (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
    (hdet : ThomSpaceClassesDetect k m U Φ) : ThomSpaceTorsionDetected k m :=
  ⟨thomSpaceClass1 k m U Φ, thomSpaceClass2 k m U Φ, hdet⟩

end

end Work.ThomBordism.Grassmann
