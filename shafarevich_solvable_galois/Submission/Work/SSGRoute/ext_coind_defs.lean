import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shared vocabulary for Shapiro for `Ext` (`Extⁿ_G(M, Coind_D^G N) ≅ Extⁿ_D(res M, N)`)

Two thin wrappers used by the proof of `Work.SSGRoute.ext_coind_iso_proof`:

* `Work.SSGRoute.toSingle K X n`: the additive equivalence identifying degree-`n` cochains from a
  cochain complex `K` into the complex concentrated in degree `0` with object `X` with the
  morphisms `K.X (-n) ⟶ X`.  This is Mathlib's `Cochain.toSingleEquiv` with the (single) degree
  pinned at `0`, i.e. with the index arithmetic `-n + n = 0` fixed.

* `Work.SSGRoute.resCoindEquiv D B N`: the adjunction bijection
  `Hom_D(res_D^G B, N) ≃ Hom_G(B, Coind_D^G N)` of `Rep.resCoindAdjunction`, and its computation
  rule `resCoindEquiv_apply_apply` (`φ ↦ (b ↦ (i ↦ φ (B.ρ i b)))`) together with its naturality
  in the *first* variable, which is what the Shapiro comparison uses.
-/

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

noncomputable section

/-! ## Cochains into a single complex -/

/-- Degree-`n` data of a cochain into a complex concentrated in degree `0`:
`Cochain K ((singleFunctor C 0).obj X) n ≃+ (K.X (-n) ⟶ X)`. -/
def toSingle {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℤ) (X : C) (n : ℤ) :
    CochainComplex.HomComplex.Cochain K ((CochainComplex.singleFunctor C 0).obj X) n ≃+
      (K.X (-n) ⟶ X) :=
  CochainComplex.HomComplex.Cochain.toSingleEquiv (p := -n) (q := 0) (n := n)
    (show -n + n = 0 by ring)

/-- Feeding the data `f : K.X (-n) ⟶ X` into `toSingle`. -/
lemma toSingle_toSingleMk {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℤ) (X : C) (n : ℤ) (f : K.X (-n) ⟶ X) :
    toSingle K X n (CochainComplex.HomComplex.Cochain.toSingleMk f (show -n + n = 0 by ring)) =
      f :=
  CochainComplex.HomComplex.Cochain.toSingleEquiv_toSingleMk (p := -n) (q := 0) (n := n) f
    (show -n + n = 0 by ring)

/-- The inverse of `toSingle`: the cochain of degree `n` with data `f`. -/
lemma toSingle_symm_apply {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℤ) (X : C) (n : ℤ) (f : K.X (-n) ⟶ X) :
    (toSingle K X n).symm f =
      CochainComplex.HomComplex.Cochain.toSingleMk f (show -n + n = 0 by ring) := by
  apply (toSingle K X n).injective
  rw [AddEquiv.apply_symm_apply]
  exact (toSingle_toSingleMk K X n f).symm

/-! ## The adjunction `res ⊣ coind` -/

/-- The adjunction bijection `Hom_D(res_D^G B, N) ≃ Hom_G(B, Coind_D^G N)`. -/
def resCoindEquiv {G : Type} [Group G] (D : Subgroup G) (B : Rep.{0, 0, 0} Coeff G)
    (N : Rep.{0, 0, 0} Coeff D) :
    (Rep.res D.subtype B ⟶ N) ≃ (B ⟶ Rep.coind D.subtype N) :=
  (Rep.resCoindHomEquiv (k := Coeff) D.subtype B N).toEquiv

@[simp] lemma resCoindEquiv_apply {G : Type} [Group G] (D : Subgroup G)
    (B : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff D)
    (u : Rep.res D.subtype B ⟶ N) :
    resCoindEquiv D B N u = Rep.resCoindToHom D.subtype B N u := rfl

/-- Computation rule for the adjunction bijection. -/
lemma resCoindEquiv_apply_apply {G : Type} [Group G] (D : Subgroup G)
    (B : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff D)
    (u : Rep.res D.subtype B ⟶ N) (b : B.V) (i : G) :
    ((resCoindEquiv D B N u).hom b).1 i = u.hom (B.ρ i b) :=
  Rep.resCoindToHom_hom_apply_coe D.subtype B N u b i

/-- The adjunction bijection is additive. -/
lemma resCoindEquiv_add {G : Type} [Group G] (D : Subgroup G) (B : Rep.{0, 0, 0} Coeff G)
    (N : Rep.{0, 0, 0} Coeff D) (u v : Rep.res D.subtype B ⟶ N) :
    resCoindEquiv D B N (u + v) = resCoindEquiv D B N u + resCoindEquiv D B N v := by
  rw [resCoindEquiv_apply, resCoindEquiv_apply, resCoindEquiv_apply]
  exact (Rep.resCoindHomEquiv (k := Coeff) D.subtype B N).map_add u v

/-- Naturality of the adjunction bijection in the **first** variable. -/
lemma resCoindEquiv_naturality_left {G : Type} [Group G] (D : Subgroup G)
    {B' B : Rep.{0, 0, 0} Coeff G} (f : B' ⟶ B) (N : Rep.{0, 0, 0} Coeff D)
    (u : Rep.res D.subtype B ⟶ N) :
    resCoindEquiv D B' N ((Rep.resFunctor D.subtype).map f ≫ u) =
      f ≫ resCoindEquiv D B N u := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  funext i
  simp only [Representation.IntertwiningMap.toLinearMap_apply, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  rw [resCoindEquiv_apply_apply]
  rw [show (Rep.Hom.hom (Rep.resMap D.subtype f ≫ u)) ((B'.ρ i) b)
      = (Rep.Hom.hom u) ((Rep.Hom.hom (Rep.resMap D.subtype f)) ((B'.ρ i) b)) from rfl]
  rw [Rep.resMap_hom_apply, Rep.hom_comm_apply, resCoindEquiv_apply_apply]

/-- Naturality in the first variable for the inverse of the adjunction bijection. -/
lemma resCoindEquiv_symm_naturality_left {G : Type} [Group G] (D : Subgroup G)
    {B' B : Rep.{0, 0, 0} Coeff G} (f : B' ⟶ B) (N : Rep.{0, 0, 0} Coeff D)
    (t : B ⟶ Rep.coind D.subtype N) :
    (resCoindEquiv D B' N).symm (f ≫ t) =
      (Rep.resFunctor D.subtype).map f ≫ (resCoindEquiv D B N).symm t := by
  apply (resCoindEquiv D B' N).injective
  rw [Equiv.apply_symm_apply, resCoindEquiv_naturality_left, Equiv.apply_symm_apply]

/-- The adjunction bijection as an **additive** equivalence. -/
def resCoindAddEquiv {G : Type} [Group G] (D : Subgroup G) (B : Rep.{0, 0, 0} Coeff G)
    (N : Rep.{0, 0, 0} Coeff D) :
    (Rep.res D.subtype B ⟶ N) ≃+ (B ⟶ Rep.coind D.subtype N) :=
  { resCoindEquiv D B N with map_add' := resCoindEquiv_add D B N }

@[simp] lemma resCoindAddEquiv_apply {G : Type} [Group G] (D : Subgroup G)
    (B : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff D)
    (u : Rep.res D.subtype B ⟶ N) :
    resCoindAddEquiv D B N u = Rep.resCoindToHom D.subtype B N u := rfl

/-- `Rep.resCoindToHom` sends `0` to `0`. -/
@[simp] lemma resCoindToHom_zero {G : Type} [Group G] (D : Subgroup G)
    (B : Rep.{0, 0, 0} Coeff G) (N : Rep.{0, 0, 0} Coeff D) :
    Rep.resCoindToHom D.subtype B N 0 = 0 :=
  (resCoindAddEquiv D B N).map_zero

end

end Work.SSGRoute
