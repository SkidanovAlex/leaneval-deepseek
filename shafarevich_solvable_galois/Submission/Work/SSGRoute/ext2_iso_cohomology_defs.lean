import Mathlib
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Definitions for node `E1a/1`: `Ext²_G(R,X) ≅ H²(G, Hom_ℤ(R,X))` for a `ℤ`-lattice `R`

The route is `Ext²_G(R,X) ≅ H²(Hom_G(P_•,X))` for a projective resolution `P_•` of `R`; the
resolution is the image of Mathlib's bar resolution of the trivial `ℤ[G]`-module `ℤ` under the
exact functor `- ⊗_{ℤ} R` (which exists because `Rep ℤ G` is monoidal, `R` being `ℤ`-free making
the tensor product exact in the other variable).  Its terms are

`P_n = (barResolution.complex).X n ⊗ R`, with differential `(barResolution.complex).d n ▷ R`,

and the augmentation `P_0 = C_0 ⊗ R ⟶ ℤ ⊗ R ≅ R` is `ε ⊗ id`.

The point of this resolution is that, levelwise, the tensor–hom adjunction of the closed monoidal
structure on `Rep ℤ G` identifies its `Hom`-complex with the complex computing `H^•(G, R ⟹ X)`:

`Hom_G(C_n ⊗ R, X) ≅ Hom_G(C_n, R ⟹ X)`,

where `R ⟹ X = (Rep.ihom R).obj X` is the internal hom, i.e. `R.V →ₗ[ℤ] X.V` with the
conjugation action.

This file contains only the two definitions (and their computation rules); the substantive facts
(projectivity of the terms, quasi-isomorphism of the augmentation, and the levelwise tensor–hom
identification) are proved elsewhere.
-/

open CategoryTheory MonoidalCategory

namespace Work.SSGRoute

noncomputable section

variable (G : Type) [Group G]

/-- The complex `(barResolution.complex) ⊗_{ℤ} R`, i.e. the image of the bar resolution of the
trivial `ℤ[G]`-module `ℤ` under the functor `- ⊗_{ℤ} R` (exact in the other variable since `R` is
`ℤ`-free).  This is the projective resolution of `R` used to compute `Ext²_G(R,X)`. -/
noncomputable def stdTensorComplex (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    ChainComplex (Rep.{0} SSGRoute.PTExt.Coeff G) ℕ :=
  ChainComplex.of (fun n => (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.X n ⊗ R)
    (fun n => (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d (n + 1) n ▷ R)
    (fun n => by
      rw [← MonoidalCategory.comp_whiskerRight,
        (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d_comp_d,
        MonoidalPreadditive.zero_whiskerRight])

@[simp] lemma stdTensorComplex_X (R : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) :
    (stdTensorComplex G R).X n = (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.X n ⊗ R := rfl

@[simp] lemma stdTensorComplex_d (R : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) :
    (stdTensorComplex G R).d (n + 1) n =
      (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d (n + 1) n ▷ R := by
  simp [stdTensorComplex]

/-- The augmentation `(barResolution.complex) ⊗ R ⟶ R[0]`: in degree `0` it is
`ε ⊗ id : C_0 ⊗ R ⟶ ℤ ⊗ R ≅ R`, the composite of the augmentation of the bar resolution with the
right unitor. -/
noncomputable def stdTensorAug (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    stdTensorComplex G R ⟶ (ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj R :=
  let hsq : (((ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj
      (Rep.trivial SSGRoute.PTExt.Coeff G SSGRoute.PTExt.Coeff)).X 0)
        = 𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G) := rfl
  (ChainComplex.toSingle₀Equiv (stdTensorComplex G R) R).symm
    ⟨(Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 ▷ R ≫ (eqToHom hsq) ▷ R ≫ (λ_ R).hom, by
      have h0 : (Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 1 = 0 :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (Rep.trivial SSGRoute.PTExt.Coeff G SSGRoute.PTExt.Coeff) 1 (by simp)).eq_of_tgt _ 0
      have hd : (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d 1 0 ≫
          (Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 = 0 := by
        have hc := HomologicalComplex.Hom.comm (Rep.barResolution SSGRoute.PTExt.Coeff G).π 1 0
        rw [← hc, h0, Limits.zero_comp]
      show (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d 1 0 ▷ R ≫
        ((Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 ▷ R ≫
          (eqToHom hsq) ▷ R ≫ (λ_ R).hom) = 0
      have hkey : (Rep.barResolution SSGRoute.PTExt.Coeff G).complex.d 1 0 ▷ R ≫
          (Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 ▷ R = 0 := by
        rw [← MonoidalCategory.comp_whiskerRight, hd, MonoidalPreadditive.zero_whiskerRight]
      simp only [← Category.assoc, hkey, Limits.zero_comp, Category.comp_id]⟩

/-- The degree-`0` component of the augmentation: `ε ⊗ id` followed by the unitor. -/
lemma stdTensorAug_f_zero (R : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (stdTensorAug G R).f 0 =
      (Rep.barResolution SSGRoute.PTExt.Coeff G).π.f 0 ▷ R ≫
        (eqToHom (by rfl : (((ChainComplex.single₀ (Rep.{0} SSGRoute.PTExt.Coeff G)).obj
          (Rep.trivial SSGRoute.PTExt.Coeff G SSGRoute.PTExt.Coeff)).X 0)
            = 𝟙_ (Rep.{0} SSGRoute.PTExt.Coeff G))) ▷ R ≫ (λ_ R).hom :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end

end Work.SSGRoute
