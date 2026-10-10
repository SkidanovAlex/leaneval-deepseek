import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Submission.Work.SSGRoute.ext_coind_defs
import Submission.Work.SSGRoute.homRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro for `Ext`: `Extⁿ_G(M, Coind_D^G N) ≅ Extⁿ_D(res_D^G M, N)`

`Ext` is Mathlib's derived-category `CategoryTheory.Abelian.Ext`, computed through a projective
resolution of the *first* variable (`ProjectiveResolution.extAddEquivCohomologyClass`).  Since
`Rep.resFunctor D.subtype` is exact and preserves projective objects, the image of a projective
resolution `P` of `M` is a projective resolution `Q = (resFunctor D.subtype).mapProjectiveResolution P`
of `res M`.  The two computations are then compared by transporting the adjunction bijection
`Rep.resCoindHomEquiv : (res B ⟶ N) ≃ (B ⟶ Coind N)` to the level of cochains:

* `toSingle K X n` identifies `Cochain K ((singleFunctor C 0).obj X) n` with `K.X (-n) ⟶ X`;
* the components of the canonical isomorphism `Φ : F (P.cochainComplex) ≅ Q.cochainComplex`
  (where `F` is the restriction functor) allow the comparison maps `theta` and `xi` on cochains,
  which commute with the differential `δ` and are inverse to each other;
* hence (via `cohomologyClassAddEquivOfCochain`) the cohomology classes — and thus the `Ext`-groups
  — are additively equivalent.
-/

namespace Work.SSGRoute

open CategoryTheory Limits SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

noncomputable section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! ## Auxiliary facts about cochains into a single complex -/

/-- `toSingle` is compatible with unit scalars. -/
lemma toSingle_units_smul {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℤ) (X : C) (n : ℤ) (u : ℤˣ)
    (α : CochainComplex.HomComplex.Cochain K ((CochainComplex.singleFunctor C 0).obj X) n) :
    toSingle K X n (u • α) = u • toSingle K X n α := by
  rw [Units.smul_def, Units.smul_def]
  exact AddMonoidHom.map_zsmul (toSingle K X n).toAddMonoidHom _ _

/-- The `toSingle`-transport of the differential of a cochain into a single complex. -/
lemma toSingle_δ {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    (K : CochainComplex C ℤ) (X : C) (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain K ((CochainComplex.singleFunctor C 0).obj X) n) :
    toSingle K X (n + 1) (CochainComplex.HomComplex.δ n (n + 1) α) =
      (n + 1).negOnePow • (K.d (-(n + 1)) (-n) ≫ toSingle K X n α) := by
  have hα : α = CochainComplex.HomComplex.Cochain.toSingleMk (toSingle K X n α)
      (show -n + n = 0 by ring) := by
    rw [← toSingle_symm_apply]
    exact ((toSingle K X n).symm_apply_apply α).symm
  have hδ : CochainComplex.HomComplex.δ n (n + 1) (CochainComplex.HomComplex.Cochain.toSingleMk
        (toSingle K X n α) (show -n + n = 0 by ring)) =
      (n + 1).negOnePow • CochainComplex.HomComplex.Cochain.toSingleMk
        (K.d (-(n + 1)) (-n) ≫ toSingle K X n α) (show -(n + 1) + (n + 1) = 0 by ring) :=
    CochainComplex.HomComplex.Cochain.δ_toSingleMk (toSingle K X n α)
      (show -n + n = 0 by ring) (n + 1) (-(n + 1)) (show -(n + 1) + (n + 1) = 0 by ring)
  rw [hα, hδ, toSingle_units_smul, toSingle_toSingleMk, toSingle_toSingleMk]

/-! ## `F`-images of complexes extended by zero -/

/-- For an additive functor `F : C ⥤ D` between preadditive categories with zero objects, the
`F`-image of a complex extended by zero is canonically isomorphic to the extension by zero of the
`F`-image. -/
theorem mapHomologicalComplex_extend_iso {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroObject C] [Preadditive C] [Limits.HasZeroObject D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c) :
    Nonempty (((F.mapHomologicalComplex c').obj (K.extend e)) ≅
      ((F.mapHomologicalComplex c).obj K).extend e) := by
  classical
  let Φ : ∀ i', ((F.mapHomologicalComplex c').obj (K.extend e)).X i' ≅
      (((F.mapHomologicalComplex c).obj K).extend e).X i' := fun i' =>
    if h : ∃ i, e.f i = i' then
      (F.mapIso (K.extendXIso e h.choose_spec)).trans
        ((((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec)).symm
    else
      IsZero.iso (by
        rw [Functor.mapHomologicalComplex_obj_X]
        exact Functor.map_isZero F (HomologicalComplex.isZero_extend_X' K e i'
          (ComplexShape.Embedding.r_eq_none e i' (by tauto))))
      (HomologicalComplex.isZero_extend_X' ((F.mapHomologicalComplex c).obj K) e i'
        (ComplexShape.Embedding.r_eq_none e i' (by tauto)))
  refine ⟨HomologicalComplex.Hom.isoOfComponents Φ (fun i' j' hij => ?_)⟩
  by_cases hi : ∃ i, e.f i = i'
  · dsimp only [Φ]
    rw [dif_pos hi]
    by_cases hj : ∃ j, e.f j = j'
    · rw [dif_pos hj]
      rw [Functor.mapHomologicalComplex_obj_d,
        HomologicalComplex.extend_d_eq K e hi.choose_spec hj.choose_spec,
        HomologicalComplex.extend_d_eq ((F.mapHomologicalComplex c).obj K) e
          hi.choose_spec hj.choose_spec]
      simp only [Functor.mapHomologicalComplex_obj_d, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [Functor.map_comp, Functor.map_comp]
      simp only [← Functor.mapIso_inv, Functor.mapIso_hom, Iso.inv_hom_id_assoc, Category.comp_id,
        Category.id_comp]
      simp only [← Functor.mapIso_hom, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id,
        Category.id_comp]
    · rw [dif_neg hj]
      exact IsZero.eq_of_tgt (HomologicalComplex.isZero_extend_X' _ e j'
        (ComplexShape.Embedding.r_eq_none e j' (by tauto))) _ _
  · dsimp only [Φ]
    rw [dif_neg hi]
    apply IsZero.eq_of_src
    rw [Functor.mapHomologicalComplex_obj_X]
    exact Functor.map_isZero F (HomologicalComplex.isZero_extend_X' K e i'
      (ComplexShape.Embedding.r_eq_none e i' (by tauto)))


/-! ## The comparison of cochains -/

section Compare

variable {G : Type} [Group G] (D : Subgroup G) (N : Rep.{0, 0, 0} Coeff D)
variable {M : Rep.{0, 0, 0} Coeff G} (P : ProjectiveResolution M)
variable (Q : ProjectiveResolution (Rep.res D.subtype M))
variable (Φ : ((Rep.resFunctor (k := Coeff) D.subtype).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    P.cochainComplex ≅ Q.cochainComplex)

/-- The single complex on `N` (over `D`). -/
abbrev sN : CochainComplex (Rep.{0, 0, 0} Coeff D) ℤ :=
  (CochainComplex.singleFunctor (Rep.{0, 0, 0} Coeff D) 0).obj N

/-- The single complex on the coinduced module (over `G`). -/
abbrev sC : CochainComplex (Rep.{0, 0, 0} Coeff G) ℤ :=
  (CochainComplex.singleFunctor (Rep.{0, 0, 0} Coeff G) 0).obj (Rep.coind D.subtype N)

/-- Naturality of the adjunction bijection in the first variable, for `resCoindAddEquiv`. -/
lemma resCoindAddEquiv_naturality_left {B' B : Rep.{0, 0, 0} Coeff G}
    (f : B' ⟶ B) (u : Rep.res D.subtype B ⟶ N) :
    resCoindAddEquiv D B' N ((Rep.resFunctor D.subtype).map f ≫ u) =
      f ≫ resCoindAddEquiv D B N u :=
  resCoindEquiv_naturality_left D f N u

/-- **The comparison of cochains**, `D`-side to `G`-side (underlying function). -/
noncomputable def thetaFun (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n) :
    CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n :=
  (toSingle P.cochainComplex (Rep.coind D.subtype N) n).symm
    (resCoindAddEquiv D (P.cochainComplex.X (-n)) N
      (Φ.hom.f (-n) ≫ (toSingle Q.cochainComplex N n) α))

/-- **The comparison of cochains**, `G`-side to `D`-side (underlying function). -/
noncomputable def xiFun (n : ℤ)
    (β : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n) :
    CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n :=
  (toSingle Q.cochainComplex N n).symm
    (Φ.inv.f (-n) ≫ (resCoindAddEquiv D (P.cochainComplex.X (-n)) N).symm
      ((toSingle P.cochainComplex (Rep.coind D.subtype N) n) β))

/-- The comparison maps are additive. -/
lemma thetaFun_add (n : ℤ)
    (a b : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n) :
    thetaFun D N P Q Φ n (a + b) = thetaFun D N P Q Φ n a + thetaFun D N P Q Φ n b := by
  simp only [thetaFun, map_add, Preadditive.comp_add]

lemma xiFun_add (n : ℤ)
    (a b : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n) :
    xiFun D N P Q Φ n (a + b) = xiFun D N P Q Φ n a + xiFun D N P Q Φ n b := by
  simp only [xiFun, map_add, Preadditive.comp_add]

/-- The comparison maps as additive homomorphisms. -/
noncomputable def thetaCochain (n : ℤ) :
    CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n →+
      CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n where
  toFun := thetaFun D N P Q Φ n
  map_zero' := by simp [thetaFun, resCoindToHom_zero]
  map_add' := thetaFun_add D N P Q Φ n

/-- The comparison maps as additive homomorphisms. -/
noncomputable def xiCochain (n : ℤ) :
    CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n →+
      CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n where
  toFun := xiFun D N P Q Φ n
  map_zero' := by simp [xiFun, resCoindToHom_zero]
  map_add' := xiFun_add D N P Q Φ n

/-- The adjunction bijection (as an additive equivalence) commutes with integer scalars. -/
lemma resCoindAddEquiv_zsmul {B : Rep.{0, 0, 0} Coeff G} (k : ℤ)
    (z : Rep.res D.subtype B ⟶ N) :
    resCoindAddEquiv D B N (k • z) = k • resCoindAddEquiv D B N z :=
  (resCoindAddEquiv D B N).toAddMonoidHom.map_zsmul k z

/-- The same for the inverse of the adjunction bijection. -/
lemma resCoindAddEquiv_symm_zsmul {B : Rep.{0, 0, 0} Coeff G} (k : ℤ)
    (z : B ⟶ Rep.coind D.subtype N) :
    (resCoindAddEquiv D B N).symm (k • z) = k • (resCoindAddEquiv D B N).symm z :=
  (resCoindAddEquiv D B N).symm.toAddMonoidHom.map_zsmul k z

/-- Naturality in the first variable for the inverse of the adjunction bijection. -/
lemma resCoindAddEquiv_symm_naturality_left {B' B : Rep.{0, 0, 0} Coeff G}
    (f : B' ⟶ B) (t : B ⟶ Rep.coind D.subtype N) :
    (resCoindAddEquiv D B' N).symm (f ≫ t) =
      (Rep.resFunctor D.subtype).map f ≫ (resCoindAddEquiv D B N).symm t :=
  resCoindEquiv_symm_naturality_left D f N t

/-- `thetaFun` is a map of complexes. -/
lemma thetaFun_δ (n : ℤ) (α : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n) :
    thetaFun D N P Q Φ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) α) =
      CochainComplex.HomComplex.δ n (n + 1) (thetaFun D N P Q Φ n α) := by
  have hrel : (ComplexShape.up ℤ).Rel (-(n + 1)) (-n) := by
    show -((n : ℤ) + 1) + 1 = -n
    ring
  set g : Q.cochainComplex.X (-n) ⟶ N := (toSingle Q.cochainComplex N n) α with hg
  have key : resCoindAddEquiv D (P.cochainComplex.X (-(n + 1))) N
      (Φ.hom.f (-(n + 1)) ≫ (Q.cochainComplex.d (-(n + 1)) (-n) ≫ g)) =
      P.cochainComplex.d (-(n + 1)) (-n) ≫
        resCoindAddEquiv D (P.cochainComplex.X (-n)) N (Φ.hom.f (-n) ≫ g) := by
    rw [← Category.assoc, Φ.hom.comm' (-(n + 1)) (-n) hrel,
      Functor.mapHomologicalComplex_obj_d, Category.assoc,
      resCoindAddEquiv_naturality_left]
  have hL : (toSingle P.cochainComplex (Rep.coind D.subtype N) (n + 1))
      (thetaFun D N P Q Φ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) α)) =
      (n + 1).negOnePow • (P.cochainComplex.d (-(n + 1)) (-n) ≫
        resCoindAddEquiv D (P.cochainComplex.X (-n)) N (Φ.hom.f (-n) ≫ g)) := by
    simp only [thetaFun, AddEquiv.apply_symm_apply]
    rw [toSingle_δ, ← hg, Units.smul_def, Preadditive.comp_zsmul, Units.smul_def,
      resCoindAddEquiv_zsmul, key]
  have hR : (toSingle P.cochainComplex (Rep.coind D.subtype N) (n + 1))
      (CochainComplex.HomComplex.δ n (n + 1) (thetaFun D N P Q Φ n α)) =
      (n + 1).negOnePow • (P.cochainComplex.d (-(n + 1)) (-n) ≫
        resCoindAddEquiv D (P.cochainComplex.X (-n)) N (Φ.hom.f (-n) ≫ g)) := by
    rw [toSingle_δ]
    congr 1
    simp only [thetaFun, AddEquiv.apply_symm_apply, ← hg]
  apply (toSingle P.cochainComplex (Rep.coind D.subtype N) (n + 1)).injective
  rw [hL, hR]

/-- `xiFun` is a map of complexes. -/
lemma xiFun_δ (n : ℤ) (β : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n) :
    xiFun D N P Q Φ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) β) =
      CochainComplex.HomComplex.δ n (n + 1) (xiFun D N P Q Φ n β) := by
  have hrel : (ComplexShape.up ℤ).Rel (-(n + 1)) (-n) := by
    show -((n : ℤ) + 1) + 1 = -n
    ring
  set h : P.cochainComplex.X (-n) ⟶ Rep.coind D.subtype N :=
    (toSingle P.cochainComplex (Rep.coind D.subtype N) n) β with hh
  have key : Φ.inv.f (-(n + 1)) ≫
      (resCoindAddEquiv D (P.cochainComplex.X (-(n + 1))) N).symm
        (P.cochainComplex.d (-(n + 1)) (-n) ≫ h) =
      Q.cochainComplex.d (-(n + 1)) (-n) ≫
        (Φ.inv.f (-n) ≫ (resCoindAddEquiv D (P.cochainComplex.X (-n)) N).symm h) := by
    rw [resCoindAddEquiv_symm_naturality_left, ← Functor.mapHomologicalComplex_obj_d,
      ← Category.assoc, Φ.inv.comm' (-(n + 1)) (-n) hrel, Category.assoc]
  have hL : (toSingle Q.cochainComplex N (n + 1))
      (xiFun D N P Q Φ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) β)) =
      (n + 1).negOnePow • (Q.cochainComplex.d (-(n + 1)) (-n) ≫
        (Φ.inv.f (-n) ≫ (resCoindAddEquiv D (P.cochainComplex.X (-n)) N).symm h)) := by
    simp only [xiFun, AddEquiv.apply_symm_apply]
    rw [toSingle_δ, ← hh, Units.smul_def, resCoindAddEquiv_symm_zsmul,
      Preadditive.comp_zsmul, ← Units.smul_def, key]
  have hR : (toSingle Q.cochainComplex N (n + 1))
      (CochainComplex.HomComplex.δ n (n + 1) (xiFun D N P Q Φ n β)) =
      (n + 1).negOnePow • (Q.cochainComplex.d (-(n + 1)) (-n) ≫
        (Φ.inv.f (-n) ≫ (resCoindAddEquiv D (P.cochainComplex.X (-n)) N).symm h)) := by
    rw [toSingle_δ]
    congr 1
    simp only [xiFun, AddEquiv.apply_symm_apply, ← hh]
  apply (toSingle Q.cochainComplex N (n + 1)).injective
  rw [hL, hR]

/-- `xiFun` is a left inverse of `thetaFun`. -/
lemma xiFun_thetaFun (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) n) :
    xiFun D N P Q Φ n (thetaFun D N P Q Φ n α) = α := by
  apply (toSingle Q.cochainComplex N n).injective
  set g : Q.cochainComplex.X (-n) ⟶ N := (toSingle Q.cochainComplex N n) α with hg
  simp only [xiFun, thetaFun, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply, ← hg]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Φ.inv_hom_id, HomologicalComplex.id_f]
  erw [Category.id_comp]

/-- `thetaFun` is a left inverse of `xiFun`. -/
lemma thetaFun_xiFun (n : ℤ)
    (β : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) n) :
    thetaFun D N P Q Φ n (xiFun D N P Q Φ n β) = β := by
  apply (toSingle P.cochainComplex (Rep.coind D.subtype N) n).injective
  set h : P.cochainComplex.X (-n) ⟶ Rep.coind D.subtype N :=
    (toSingle P.cochainComplex (Rep.coind D.subtype N) n) β with hh
  simp only [thetaFun, xiFun, AddEquiv.apply_symm_apply, ← hh]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Φ.hom_inv_id, HomologicalComplex.id_f]
  erw [Category.id_comp]
  rw [AddEquiv.apply_symm_apply]

/-! ## Cohomology classes of two complexes with mutually inverse cochain maps -/

/-- Two families of additive maps on cochains which commute with the differential and are inverse
to each other on cochains induce an additive equivalence of the cohomology classes. -/
theorem cohomologyClassAddEquivOfCochain {C C' : Type*} [Category C] [Preadditive C]
    [Category C'] [Preadditive C']
    {K L : CochainComplex C ℤ} {K' L' : CochainComplex C' ℤ}
    (θ : ∀ n : ℤ, CochainComplex.HomComplex.Cochain K L n →+
      CochainComplex.HomComplex.Cochain K' L' n)
    (ξ : ∀ n : ℤ, CochainComplex.HomComplex.Cochain K' L' n →+
      CochainComplex.HomComplex.Cochain K L n)
    (hθ : ∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain K L n),
      θ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) z) =
        CochainComplex.HomComplex.δ n (n + 1) (θ n z))
    (hξ : ∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain K' L' n),
      ξ (n + 1) (CochainComplex.HomComplex.δ n (n + 1) z) =
        CochainComplex.HomComplex.δ n (n + 1) (ξ n z))
    (h1 : ∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain K L n), ξ n (θ n z) = z)
    (h2 : ∀ (n : ℤ) (z : CochainComplex.HomComplex.Cochain K' L' n), θ n (ξ n z) = z)
    (n : ℤ) : Nonempty (CochainComplex.HomComplex.CohomologyClass K L n ≃+
      CochainComplex.HomComplex.CohomologyClass K' L' n) := by
  -- the induced maps on cocycles
  let Θ : ∀ m : ℤ, CochainComplex.HomComplex.Cocycle K L m →+
      CochainComplex.HomComplex.Cocycle K' L' m := fun m => {
    toFun := fun z => CochainComplex.HomComplex.Cocycle.mk (θ m (z : CochainComplex.HomComplex.Cochain K L m))
      (m + 1) rfl (by
        rw [← hθ m (z : CochainComplex.HomComplex.Cochain K L m),
          CochainComplex.HomComplex.Cocycle.δ_eq_zero z (m + 1), map_zero])
    map_zero' := by
      apply CochainComplex.HomComplex.Cocycle.ext
      simp
    map_add' := fun a b => by
      apply CochainComplex.HomComplex.Cocycle.ext
      simp }
  have hΘ : ∀ (m : ℤ) (z : CochainComplex.HomComplex.Cocycle K L m),
      (Θ m z : CochainComplex.HomComplex.Cochain K' L' m) =
        θ m (z : CochainComplex.HomComplex.Cochain K L m) := fun _ _ => rfl
  let Ξ : ∀ m : ℤ, CochainComplex.HomComplex.Cocycle K' L' m →+
      CochainComplex.HomComplex.Cocycle K L m := fun m => {
    toFun := fun z => CochainComplex.HomComplex.Cocycle.mk (ξ m (z : CochainComplex.HomComplex.Cochain K' L' m))
      (m + 1) rfl (by
        rw [← hξ m (z : CochainComplex.HomComplex.Cochain K' L' m),
          CochainComplex.HomComplex.Cocycle.δ_eq_zero z (m + 1), map_zero])
    map_zero' := by
      apply CochainComplex.HomComplex.Cocycle.ext
      simp
    map_add' := fun a b => by
      apply CochainComplex.HomComplex.Cocycle.ext
      simp }
  have hΞ : ∀ (m : ℤ) (z : CochainComplex.HomComplex.Cocycle K' L' m),
      (Ξ m z : CochainComplex.HomComplex.Cochain K L m) =
        ξ m (z : CochainComplex.HomComplex.Cochain K' L' m) := fun _ _ => rfl
  have hkillΘ : ∀ m : ℤ, CochainComplex.HomComplex.coboundaries K L m ≤
      ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom (K := K') (L := L')
        (n := m)).comp (Θ m)).ker := by
    intro m x hx
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
      CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom_apply,
      CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff,
      CochainComplex.HomComplex.coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨m', hm', β, hβ⟩ := hx
    refine ⟨m', hm', θ m' β, ?_⟩
    subst hm'
    rw [hΘ (m' + 1) x, ← hβ, hθ m' β]
  have hkillΞ : ∀ m : ℤ, CochainComplex.HomComplex.coboundaries K' L' m ≤
      ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom (K := K) (L := L)
        (n := m)).comp (Ξ m)).ker := by
    intro m x hx
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
      CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom_apply,
      CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff,
      CochainComplex.HomComplex.coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨m', hm', β, hβ⟩ := hx
    refine ⟨m', hm', ξ m' β, ?_⟩
    subst hm'
    rw [hΞ (m' + 1) x, ← hβ, hξ m' β]
  let Φmap : ∀ m : ℤ, CochainComplex.HomComplex.CohomologyClass K L m →+
      CochainComplex.HomComplex.CohomologyClass K' L' m := fun m =>
    CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom _ (hkillΘ m)
  let Ψmap : ∀ m : ℤ, CochainComplex.HomComplex.CohomologyClass K' L' m →+
      CochainComplex.HomComplex.CohomologyClass K L m := fun m =>
    CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom _ (hkillΞ m)
  have hΦ : ∀ (m : ℤ) (z : CochainComplex.HomComplex.Cocycle K L m),
      Φmap m (CochainComplex.HomComplex.CohomologyClass.mk z) =
        CochainComplex.HomComplex.CohomologyClass.mk (Θ m z) := fun _ _ => rfl
  have hΨ : ∀ (m : ℤ) (z : CochainComplex.HomComplex.Cocycle K' L' m),
      Ψmap m (CochainComplex.HomComplex.CohomologyClass.mk z) =
        CochainComplex.HomComplex.CohomologyClass.mk (Ξ m z) := fun _ _ => rfl
  have hleft : Function.LeftInverse (⇑(Ψmap n)) (⇑(Φmap n)) := by
    intro y
    obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
    rw [hΦ, hΨ]
    congr 1
    apply CochainComplex.HomComplex.Cocycle.ext
    rw [hΞ, hΘ]
    exact h1 n (z : CochainComplex.HomComplex.Cochain K L n)
  have hright : Function.RightInverse (⇑(Ψmap n)) (⇑(Φmap n)) := by
    intro y
    obtain ⟨z, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
    rw [hΨ, hΦ]
    congr 1
    apply CochainComplex.HomComplex.Cocycle.ext
    rw [hΘ, hΞ]
    exact h2 n (z : CochainComplex.HomComplex.Cochain K' L' n)
  exact ⟨AddEquiv.mk ⟨Φmap n, Ψmap n, hleft, hright⟩ (Φmap n).map_add⟩


/-- The differential compatibility, phrased for the additive homomorphisms. -/
lemma thetaCochain_δ (m : ℤ) (z : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) m) :
    thetaCochain D N P Q Φ (m + 1) (CochainComplex.HomComplex.δ m (m + 1) z) =
      CochainComplex.HomComplex.δ m (m + 1) (thetaCochain D N P Q Φ m z) := by
  change thetaFun D N P Q Φ (m + 1) (CochainComplex.HomComplex.δ m (m + 1) z) =
    CochainComplex.HomComplex.δ m (m + 1) (thetaFun D N P Q Φ m z)
  exact thetaFun_δ D N P Q Φ m z

/-- The differential compatibility, phrased for the additive homomorphisms. -/
lemma xiCochain_δ (m : ℤ) (z : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) m) :
    xiCochain D N P Q Φ (m + 1) (CochainComplex.HomComplex.δ m (m + 1) z) =
      CochainComplex.HomComplex.δ m (m + 1) (xiCochain D N P Q Φ m z) := by
  change xiFun D N P Q Φ (m + 1) (CochainComplex.HomComplex.δ m (m + 1) z) =
    CochainComplex.HomComplex.δ m (m + 1) (xiFun D N P Q Φ m z)
  exact xiFun_δ D N P Q Φ m z

/-- `xiCochain` is a left inverse of `thetaCochain`. -/
lemma xiCochain_thetaCochain (m : ℤ)
    (α : CochainComplex.HomComplex.Cochain Q.cochainComplex (sN D N) m) :
    xiCochain D N P Q Φ m (thetaCochain D N P Q Φ m α) = α := by
  change xiFun D N P Q Φ m (thetaFun D N P Q Φ m α) = α
  exact xiFun_thetaFun D N P Q Φ m α

/-- `thetaCochain` is a left inverse of `xiCochain`. -/
lemma thetaCochain_xiCochain (m : ℤ)
    (β : CochainComplex.HomComplex.Cochain P.cochainComplex (sC D N) m) :
    thetaCochain D N P Q Φ m (xiCochain D N P Q Φ m β) = β := by
  change thetaFun D N P Q Φ m (xiFun D N P Q Φ m β) = β
  exact thetaFun_xiFun D N P Q Φ m β

end Compare

/-! ## The Shapiro isomorphism for `Ext` -/

theorem ext_coind_iso_proof (G : Type) [Group G] (D : Subgroup G) (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (N : Rep.{0} SSGRoute.PTExt.Coeff D) (n : ℕ) [HasExt (Rep.{0} SSGRoute.PTExt.Coeff G)]
    [HasExt (Rep.{0} SSGRoute.PTExt.Coeff D)] :
    Nonempty (CategoryTheory.Abelian.Ext M (Rep.coind D.subtype N) n ≃+
      CategoryTheory.Abelian.Ext (Rep.res D.subtype M) N n) := by
  let P : ProjectiveResolution M := ProjectiveResolution.of M
  let Q : ProjectiveResolution (Rep.res D.subtype M) :=
    (Rep.resFunctor (k := Coeff) D.subtype).mapProjectiveResolution P
  obtain ⟨Φ⟩ := mapHomologicalComplex_extend_iso (Rep.resFunctor (k := Coeff) D.subtype)
    ComplexShape.embeddingDownNat P.complex
  obtain ⟨e⟩ := cohomologyClassAddEquivOfCochain (C := Rep.{0, 0, 0} Coeff D)
    (C' := Rep.{0, 0, 0} Coeff G)
    (K := Q.cochainComplex) (K' := P.cochainComplex) (L := sN D N) (L' := sC D N)
    (fun m => thetaCochain D N P Q Φ m) (fun m => xiCochain D N P Q Φ m)
    (fun m z => thetaCochain_δ D N P Q Φ m z)
    (fun m z => xiCochain_δ D N P Q Φ m z)
    (fun m z => xiCochain_thetaCochain D N P Q Φ m z)
    (fun m z => thetaCochain_xiCochain D N P Q Φ m z) (↑n)
  exact ⟨(ProjectiveResolution.extAddEquivCohomologyClass P (Y := Rep.coind D.subtype N)
      (n := n)).trans (e.symm.trans
        (ProjectiveResolution.extAddEquivCohomologyClass Q (Y := N) (n := n)).symm)⟩

end

end Work.SSGRoute

