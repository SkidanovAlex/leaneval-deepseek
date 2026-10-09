import Mathlib
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.H2_coeff_transfer
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.groupCohomology_two_iso_cocycles
import Submission.Work.SSGRoute.cocycles_iso_Z2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H²(G, Hom_ℤ(R, X))` for the internal hom `Rep.ihom`

Let `R X : Rep Coeff G` (`Coeff = ULift ℤ`).  The internal hom `(Rep.ihom R).obj X` is the
representation on the `ℤ`-linear maps `R.V →ₗ X.V` with the conjugation action
`(g · f) = X.ρ g ∘ f ∘ R.ρ (g⁻¹)`, and the target of this file is

`groupCohomology ((Rep.ihom R).obj X) 2 ≃+ Work.GroupCohomology.H2 G (R.V →ₗ X.V)`,

i.e. that the second group cohomology of the internal hom agrees with the inhomogeneous
`Z²/B²` description of `Submission.Work.GroupCohomology.Basic`.

Mathematically both sides are the same construction; the only difficulty is formal: the object
`((Rep.ihom R).obj X).V` and the type `R.V →ₗ Coeff X.V` occurring in the target are `LinearMap`
types whose `Module Coeff` instance arguments are *different terms* (`Rep.hV2` versus the canonical
`ULift.module`-instance), so they are not definitionally equal.  Since all `Coeff`-module structures
on an additive commutative group coincide (`moduleCoeff_subsingleton`), the two types are equal and
the reinterpretation of a linear map in the other family is an additive equivalence
(`bridgeEquiv`), which is what `H2_coeff_transfer` needs.

The proof is then a three-step composite:

* `bridgeEquiv` moves `groupCohomology ((Rep.ihom R).obj X) 2` to the group cohomology of
  `homRep R X = Rep.ofDistribMulAction Coeff G (R.V →ₗ X.V)` (`H2_coeff_transfer`);
* `groupCohomology_two_iso_cocycles` identifies the second cohomology of a representation with
  `Z²/B²` (Mathlib's `cocycles₂`/`coboundaries₂`);
* `cocycles_iso_Z2` transports `Z²/B²` to the `Work.GroupCohomology.H2` of its coefficient module.
-/

open CategoryTheory

namespace Work.SSGRoute

open SSGRoute.PTExt

variable {G : Type} [Group G]

/-- The canonical `Coeff = ULift ℤ`-module structure on an additive commutative group, i.e. the one
obtained from the `ℤ`-action via `ULift.module`.  This is the `Module` instance that type class
search produces for a type which is not already a `Rep`'s carrier. -/
noncomputable def canonModule (M : Type) [AddCommGroup M] : Module SSGRoute.PTExt.Coeff M :=
  @ULift.module.{0,0,0} Int M Int.instSemiring _ _

/-- All `Coeff = ULift ℤ`-module structures on an additive commutative group coincide. -/
lemma moduleCoeff_subsingleton (M : Type) [AddCommGroup M] :
    Subsingleton (Module SSGRoute.PTExt.Coeff M) := by
  constructor
  intro P Q
  apply Module.ext
  funext r m
  obtain ⟨k⟩ := r
  have hP : P.smul (ULift.up k) m = k • m := by
    letI := P
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  have hQ : Q.smul (ULift.up k) m = k • m := by
    letI := Q
    rw [← Int.cast_smul_eq_zsmul (R := ULift ℤ) k m]
    rfl
  exact hP.trans hQ.symm

/-- The scalar actions of two `Coeff`-module structures on the same additive commutative group
agree. -/
lemma smul_moduleCoeff_congr (M : Type) [AddCommGroup M]
    (P Q : Module SSGRoute.PTExt.Coeff M) (c : SSGRoute.PTExt.Coeff) (x : M) :
    @SMul.smul SSGRoute.PTExt.Coeff M P.toDistribMulAction.toSMul c x =
      @SMul.smul SSGRoute.PTExt.Coeff M Q.toDistribMulAction.toSMul c x := by
  haveI := moduleCoeff_subsingleton M
  rw [Subsingleton.elim P Q]

/-- The underlying additive homomorphism of a `Coeff`-linear map, with the module instances of the
`LinearMap` type left implicit. -/
abbrev toAHom (R X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff R.V) (Q : Module SSGRoute.PTExt.Coeff X.V)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P Q) : R.V →ₙ+ X.V :=
  @LinearMap.toAddHom SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P Q f

/-- Reinterpret a `Coeff`-linear map `R.V →ₗ X.V` in a different pair of `Coeff`-module
structures.  The underlying function is unchanged; only the `map_smul'` field has to be redone,
which is possible because the scalar actions agree (`smul_moduleCoeff_congr`). -/
noncomputable def lmChange (R X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff R.V) (Q : Module SSGRoute.PTExt.Coeff X.V)
    (P' : Module SSGRoute.PTExt.Coeff R.V) (Q' : Module SSGRoute.PTExt.Coeff X.V)
    (f : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P Q) :
    @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P' Q' :=
  @LinearMap.mk SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
    (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P' Q'
    (toAHom R X P Q f)
    (fun c x => by
      have h1 : @AddHom.toFun R.V X.V _ _ (toAHom R X P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff R.V P'.toDistribMulAction.toSMul c x) =
          @AddHom.toFun R.V X.V _ _ (toAHom R X P Q f)
            (@SMul.smul SSGRoute.PTExt.Coeff R.V P.toDistribMulAction.toSMul c x) :=
        congrArg (@AddHom.toFun R.V X.V _ _ (toAHom R X P Q f))
          (smul_moduleCoeff_congr R.V P' P c x)
      have h2 := @LinearMap.map_smul' SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
        (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P Q f c x
      have h3 : @SMul.smul SSGRoute.PTExt.Coeff X.V Q.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun R.V X.V _ _ (toAHom R X P Q f) x) =
          @SMul.smul SSGRoute.PTExt.Coeff X.V Q'.toDistribMulAction.toSMul
            ((RingHom.id SSGRoute.PTExt.Coeff) c)
            (@AddHom.toFun R.V X.V _ _ (toAHom R X P Q f) x) :=
        smul_moduleCoeff_congr X.V Q Q' ((RingHom.id SSGRoute.PTExt.Coeff) c)
          (@AddHom.toFun R.V X.V _ _ (toAHom R X P Q f) x)
      exact h1.trans (h2.trans h3))

/-- Two `Coeff`-linear maps with the same underlying additive homomorphism are equal. -/
lemma lm_ext (R X : Rep.{0} SSGRoute.PTExt.Coeff G)
    (P : Module SSGRoute.PTExt.Coeff R.V) (Q : Module SSGRoute.PTExt.Coeff X.V)
    {f g : @LinearMap.{0,0,0,0} SSGRoute.PTExt.Coeff SSGRoute.PTExt.Coeff _ _
            (RingHom.id SSGRoute.PTExt.Coeff) R.V X.V _ _ P Q}
    (h : toAHom R X P Q f = toAHom R X P Q g) : f = g := by
  cases f; cases g
  simp only [toAHom] at h
  subst h
  rfl

/-- **The internal hom of `Rep Coeff G` is the `Rep` `homRep`.**  The identity on the underlying
`ℤ`-linear maps `R.V →ₗ X.V` is an additive equivalence between `((Rep.ihom R).obj X).V`
(with the module instances coming from the `Rep` structure, which is what `Rep.ρ` and Mathlib's
`Rep.ihom` use) and the type `(homRep R X).V` underlying the explicit internal-hom representation
`Work.SSGRoute.homRep`, where the module structure is the canonical one produced by type class
search.  The two `Module Coeff`-instances are propositionally equal
(`moduleCoeff_subsingleton`), and the map is the underlying-function identity. -/
noncomputable def bridgeEquiv (R X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ((Rep.ihom R).obj X).V ≃+ (Work.SSGRoute.homRep R X).V where
  toFun := lmChange R X R.hV2 X.hV2 (canonModule R.V) (canonModule X.V)
  invFun := lmChange R X (canonModule R.V) (canonModule X.V) R.hV2 X.hV2
  left_inv := fun f => lm_ext R X R.hV2 X.hV2 rfl
  right_inv := fun g => lm_ext R X (canonModule R.V) (canonModule X.V) rfl
  map_add' := fun f g => by
    apply lm_ext R X (canonModule R.V) (canonModule X.V)
    rfl

/-- The additive equivalence `bridgeEquiv` commutes with the `G`-action: both sides act by
conjugation, `f ↦ X.ρ g ∘ f ∘ R.ρ g⁻¹`. -/
lemma bridgeEquiv_rho (R X : Rep.{0} SSGRoute.PTExt.Coeff G) (g : G)
    (v : ((Rep.ihom R).obj X).V) :
    bridgeEquiv R X (((Rep.ihom R).obj X).ρ g v) =
      Work.SSGRoute.homSMul R X g (bridgeEquiv R X v) := by
  apply lm_ext R X (canonModule R.V) (canonModule X.V)
  rfl

/-- **Shafarevich/`Ext²` bridge, degree `2`, for the internal hom.**  For `R X : Rep Coeff G`, the
second group cohomology of the internal hom `(Rep.ihom R).obj X` is the inhomogeneous `H²` with
coefficients in the conjugation module `Hom_ℤ(R.V, X.V)`. -/
theorem groupCohomology_ihom_deg_two (G : Type) [Group G]
    (R X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty (groupCohomology ((Rep.ihom R).obj X) 2 ≃+
      Work.GroupCohomology.H2 G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V)) := by
  obtain ⟨e1⟩ := H2_coeff_transfer (k := SSGRoute.PTExt.Coeff) (k' := SSGRoute.PTExt.Coeff)
    (G := G) ((Rep.ihom R).obj X)
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
    (bridgeEquiv R X) (bridgeEquiv_rho R X)
  obtain ⟨e2⟩ := groupCohomology_two_iso_cocycles SSGRoute.PTExt.Coeff G
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
  obtain ⟨e3⟩ := cocycles_iso_Z2 SSGRoute.PTExt.Coeff G
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
    (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V) (AddEquiv.refl _) (fun _ _ => rfl)
  exact ⟨e1.trans (e2.trans e3)⟩

end Work.SSGRoute
