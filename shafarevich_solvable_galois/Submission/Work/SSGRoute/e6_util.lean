import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.mapExactFunctor_id
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared small `Ext`-calculus lemmas for the E6 assembly

The generic `Ext`-calculus lemmas of this file are the ones `Submission.Work.SSGRoute.e6_sylow_assembly`
needs (`E6Ω`, the Sylow descent of `Work.SSGRoute.phi1_mono_sylow`) but which are declared in
`Submission.Work.SSGRoute.local_duality_ext` — a module that `e6_sylow_assembly` cannot import,
because `local_duality_ext` and `phiPushClass` (pulled in by `phi1_mono_pgroup_in`, needed for `E5Ω`)
both declare the constant `Work.SSGRoute.pushClass`.  The lemmas here are verbatim copies of the
generic ones in that file; nothing arithmetic is involved.

Namespace `Work.SSGRoute.E6Util`.
-/

open CategoryTheory

noncomputable section

namespace Work.SSGRoute.E6Util

open SSGRoute.PTExt

/-- Associativity of `Ext.comp` when the second factor has degree `0` (the Mathlib gap). -/
theorem comp_assoc_of_first_deg_zero {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z T : C} {a₂ a₃ : ℕ} (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z a₂)
    (γ : Abelian.Ext Z T a₃) :
    (α.comp β (zero_add a₂)).comp γ rfl = α.comp (β.comp γ rfl) (zero_add (a₂ + a₃)) := by
  exact Abelian.Ext.comp_assoc α β γ (zero_add a₂) rfl (by omega)

/-- `extRes` is additive. -/
theorem extRes_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0} Coeff G} {n : ℕ} (x x' : Abelian.Ext.{0} X Y n) :
    extRes f (x + x') = extRes f x + extRes f x' := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_add (Rep.resFunctor f) X Y n x x'

/-- `extRes` kills the zero class. -/
theorem extRes_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep.{0} Coeff G} {n : ℕ} : extRes f (0 : Abelian.Ext.{0} X Y n) = 0 := by
  simpa only [extRes] using Abelian.Ext.mapExactFunctor_zero (Rep.resFunctor f) X Y n

/-- `extHMap` is additive. -/
theorem extHMap_add {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ}
    (y y' : extH A n) : extHMap f ι (y + y') = extHMap f ι y + extHMap f ι y' := by
  simp only [extHMap]
  rw [extRes_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- `extHMap` kills the zero class. -/
theorem extHMap_zero {G H : Type} [Group G] [Group H] (f : H →* G)
    {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ} :
    extHMap f ι (0 : extH A n) = 0 := by
  simp only [extHMap]
  rw [extRes_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- **The identity case of `extRes`**: change of group along the identity is the identity. -/
theorem extRes_id {G : Type} [Group G] {X Y : Rep.{0} Coeff G} {n : ℕ}
    (x : Abelian.Ext.{0} X Y n) : extRes (MonoidHom.id G) x = x := by
  rw [show extRes (MonoidHom.id G) x = x.mapExactFunctor (𝟭 (Rep.{0} Coeff G)) from rfl]
  exact Work.SSGRoute.mapExactFunctor_id x

/-- **Compatibility of the level pairing with inflation** (the inflation-companion of
`SylowIn.levelPair_restrict`). -/
theorem levelPair_extHMap {G H : Type} [Group G] [Group H] (f : H →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h₀ : extH M s) :
    levelPair f ι x (extHMap f (CategoryTheory.CategoryStruct.id (Rep.res f M)) h₀) =
      extHMap f ι (yonedaPair x h₀) := by
  simp only [levelPair, extHMap, yonedaPair, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.comp_mk₀_id]
  exact comp_assoc_of_first_deg_zero _ _ _

/-- **The roundtrip of `extRes` along a hom that is (propositionally) the identity.**  If
`ψ : G →* G` is the identity, then restricting an `Ext`-class along `ψ` and then transporting the
coefficient module back along the corresponding equality of modules (`eqToHom` of the `congrArg` of
`ψ = MonoidHom.id G`) gives back the class.  This is the formal core of the Sylow transfer `E6Ω`:
it converts a class over the subgroup `S = range (e)` into a class over the abstract group `G'`
along the isomorphism `e` and back.

The proof reduces (`cases hψ`) to `extRes (MonoidHom.id G) y = y` (`E6Util.extRes_id`) and
`Ext.mk₀_id_comp`; the two occurrences of `congrArg _ hψ` become `rfl`, whose `eqToHom` is `𝟙`. -/
theorem extRes_cast_roundtrip {G : Type} [Group G] {ψ : G →* G} (hψ : ψ = MonoidHom.id G)
    {X : Rep.{0} Coeff G} {n : ℕ} (y : extH X n) :
    (extRes ψ y).comp
        (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t X) hψ))) (add_zero n) = y := by
  cases hψ
  rw [show (congrArg (fun t => Rep.res t X) (rfl : MonoidHom.id G = MonoidHom.id G)) = rfl
      from Subsingleton.elim _ _, eqToHom_refl]
  rw [Abelian.Ext.comp_mk₀_id]
  exact extRes_id y

/-- **The transport roundtrip of `extRes` along a hom that is (propositionally) the identity**
(general form, for classes between arbitrary coefficient modules).  If `ψ : G →* G` is the identity
and `hX`, `hY` are the induced equalities of coefficient modules, then transporting the source of
`extRes ψ y` back by `hX` and its target forward by `hY` returns `y`.  This is the form needed to
deduce `extRes_injective_of_mulEquiv` (`extRes e.symm ∘ extRes e = id` up to transports for the
group isomorphism `e`).

The proof is the same reduction as `extRes_cast_roundtrip`: `cases hψ` makes `ψ` the identity and
turns both `hX`, `hY` into proofs of definitionally-true propositions, which `Subsingleton.elim`
replaces by `rfl`; then `eqToHom_refl`, `E6Util.extRes_id`, `Ext.mk₀_id_comp`, `Ext.comp_mk₀_id`
close it. -/
theorem extRes_transport_roundtrip {G : Type} [Group G] {ψ : G →* G} (hψ : ψ = MonoidHom.id G)
    {X Y : Rep.{0} Coeff G} (hX : Rep.res ψ X = X) (hY : Rep.res ψ Y = Y) {n : ℕ}
    (y : Abelian.Ext.{0} X Y n) :
    ((Abelian.Ext.mk₀ (eqToHom hX.symm)).comp (extRes ψ y) (zero_add n)).comp
      (Abelian.Ext.mk₀ (eqToHom hY)) (add_zero n) = y := by
  cases hψ
  rw [show hX.symm = (rfl : X = Rep.res (MonoidHom.id G) X) from Subsingleton.elim _ _,
    show hY = (rfl : Rep.res (MonoidHom.id G) Y = Y) from Subsingleton.elim _ _,
    eqToHom_refl, eqToHom_refl]
  rw [extRes_id]
  rw [Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]


section PTorsion

variable {G : Type} [Group G]

/-- A morphism of representations which is pointwise `0` is `0`. -/
theorem Rep.nsmul_id_eq_zero {X : Rep.{0} Coeff G} (p : ℕ) (hX : ∀ x : X, p • x = 0) :
    (p : ℕ) • (CategoryTheory.CategoryStruct.id X) = 0 := by
  letI := X.hV2
  refine Rep.hom_ext ?_
  rw [Rep.nsmul_hom, Rep.zero_hom]
  refine Representation.IntertwiningMap.ext ?_
  ext x
  rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.coe_nsmul,
    Pi.smul_apply, Representation.IntertwiningMap.toLinearMap_apply]
  show p • ((𝟙 X : X ⟶ X) x) = 0
  rw [Rep.id_apply]
  exact hX x

/-- **`Ext` with `p`-torsion coefficients is killed by `p`** (second-variable form). -/
theorem ext_nsmul_p_torsion (p : ℕ) {A : Rep.{0} Coeff G}
    (hA : ∀ a : A, p • a = 0) {n : ℕ} (h : extH A n) : p • h = 0 := by
  have hzero := Rep.nsmul_id_eq_zero (G := G) p hA
  have key : ∀ k : ℕ, h.comp (Abelian.Ext.mk₀ (k • (CategoryTheory.CategoryStruct.id A)))
      (add_zero n) = k • h := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, zero_nsmul]
    | succ k ih =>
        rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add, ih, Abelian.Ext.comp_mk₀_id,
          succ_nsmul]
  rw [← key p, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

/-- **`Ext` of a `p`-torsion module is killed by `p`** (first-variable form). -/
theorem ext_nsmul_p_torsion_left (p : ℕ) {X Y : Rep.{0} Coeff G}
    (hX : ∀ x : X, p • x = 0) {n : ℕ} (h : Abelian.Ext X Y n) : p • h = 0 := by
  have hzero := Rep.nsmul_id_eq_zero (G := G) p hX
  have key : ∀ k : ℕ, (Abelian.Ext.mk₀ (k • (CategoryTheory.CategoryStruct.id X))).comp h
      (zero_add n) = k • h := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp, zero_nsmul]
    | succ k ih =>
        rw [succ_nsmul, Abelian.Ext.mk₀_add, Abelian.Ext.add_comp, ih, Abelian.Ext.mk₀_id_comp,
          succ_nsmul]
  rw [← key p, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]

end PTorsion

end Work.SSGRoute.E6Util

end
