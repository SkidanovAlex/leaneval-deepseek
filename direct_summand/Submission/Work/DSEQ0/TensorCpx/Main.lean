import Mathlib
import Submission.Work.DSEQ0.TensorCpx.Basic

/-!
# The unit map `F ⟶ F ⊗ F` and the extraction of the Leibniz product

Given a cycle `e` in degree `0` of a cochain complex `F`, the "unit" `x ↦ e ⊗ x` is a chain
map `F ⟶ F ⊗ F` (`tU`).  Conversely, given a chain map `μT : F ⊗ F ⟶ F` and a homotopy
exhibiting `tU ≫ μT` as homotopic to the identity, we extract from `μT` a Leibniz product
`μ` on `F` for which `e` is a unit up to homotopy.

The two statements are purely formal unfoldings of the definitions of `T`, `TIncl` and the
Koszul differential.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.DSEQ0.TensorCpx

universe a

open CategoryTheory Limits

variable {A : Type a} [CommRing A]

/-- The `n`-th component of the unit map `F ⟶ F ⊗ F`, `x ↦ e ⊗ x`. -/
noncomputable def tUComp (F : CochainComplex (ModuleCat.{a} A) ℤ) (e : ↥(F.X 0)) (n : ℤ) :
    ↥(F.X n) →ₗ[A] TX F n :=
  (TIncl F 0 n (by omega)) ∘ₗ ((TensorProduct.mk A ↥(F.X 0) ↥(F.X n)) e)

lemma tUComp_apply (F : CochainComplex (ModuleCat.{a} A) ℤ) (e : ↥(F.X 0)) (n : ℤ)
    (x : ↥(F.X n)) :
    tUComp F e n x = TIncl F 0 n (by omega) (e ⊗ₜ[A] x) := rfl

/-- The unit map `F ⟶ F ⊗ F`, `x ↦ e ⊗ x`, for a cycle `e` in degree `0`. -/
noncomputable def tU (F : CochainComplex (ModuleCat.{a} A) ℤ) (e : ↥(F.X 0))
    (he : (F.d 0 1).hom e = 0) : F ⟶ T F where
  f n := ModuleCat.ofHom (tUComp F e n)
  comm' n m h := by
    rw [ComplexShape.up_Rel] at h
    subst h
    rw [T_d]
    apply ModuleCat.hom_ext
    refine LinearMap.ext (fun x => ?_)
    show Td F n (tUComp F e n x) = tUComp F e (n+1) ((F.d n (n+1)).hom x)
    rw [tUComp_apply, Td_apply_incl, TdComp_tmul]
    have he' : (F.d 0 (0+1)).hom e = 0 := by simpa using he
    rw [he', TensorProduct.zero_tmul, map_zero, Int.negOnePow_zero]
    rw [show ((1 : ℤˣ) : A) = 1 from by simp, one_smul, zero_add]
    rw [tUComp_apply]

lemma tU_apply (F : CochainComplex (ModuleCat.{a} A) ℤ) (e : ↥(F.X 0))
    (he : (F.d 0 1).hom e = 0) (n : ℤ) (x : ↥(F.X n)) :
    ((tU F e he).f n).hom x = TIncl F 0 n (by omega) (e ⊗ₜ[A] x) :=
  tUComp_apply F e n x

/-! ## The extraction -/

/-- The chain-map condition of `μT`, pointwise. -/
lemma muT_d (F : CochainComplex (ModuleCat.{a} A) ℤ) (μT : T F ⟶ F) (n : ℤ) (z : TX F n) :
    (F.d n (n+1)).hom ((μT.f n).hom z) = (μT.f (n+1)).hom (Td F n z) := by
  have hc := HomologicalComplex.Hom.comm μT n (n+1)
  have hc' := congrArg (fun (f : (T F).X n ⟶ F.X (n+1)) => f.hom) hc
  simp only [ModuleCat.hom_comp, T_d] at hc'
  exact congrFun (congrArg DFunLike.coe hc') z

/-- Naturality of the components of a chain map `F ⊗ F ⟶ F` under the transport `XIsoOfEq`. -/
lemma XIsoOfEq_muT (F : CochainComplex (ModuleCat.{a} A) ℤ) (μT : T F ⟶ F) {p q : ℤ}
    (h : p = q) (z : TX F p) :
    (F.XIsoOfEq h).hom ((μT.f p).hom z) = (μT.f q).hom (((T F).XIsoOfEq h).hom z) := by
  have hc := HomologicalComplex.XIsoOfEq_hom_naturality μT h
  have hc' := congrArg (fun (f : (T F).X p ⟶ F.X q) => f.hom) hc
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc'
  exact congrFun (congrArg DFunLike.coe hc') z

/-- Naturality of the components of a chain map out of `F ⊗ F` under `XIsoOfEq`. -/
lemma XIsoOfEq_hom_f (F : CochainComplex (ModuleCat.{a} A) ℤ)
    {C : CochainComplex (ModuleCat.{a} A) ℤ} (Φ : T F ⟶ C) {p q : ℤ} (h : p = q)
    (z : TX F p) :
    (C.XIsoOfEq h).hom ((Φ.f p).hom z) = (Φ.f q).hom (((T F).XIsoOfEq h).hom z) := by
  have hc := HomologicalComplex.XIsoOfEq_hom_naturality Φ h
  have hc' := congrArg (fun (f : (T F).X p ⟶ C.X q) => f.hom) hc
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc'
  exact congrFun (congrArg DFunLike.coe hc') z

/-- The same, on a summand. -/
lemma XIsoOfEq_f_TIncl (F : CochainComplex (ModuleCat.{a} A) ℤ)
    {C : CochainComplex (ModuleCat.{a} A) ℤ} (Φ : T F ⟶ C) (i j : ℤ) {p q : ℤ}
    (h : p = q) (hp : i + j = p) (hq : i + j = q) (z : TFam F i j) :
    (C.XIsoOfEq h).hom ((Φ.f p).hom (TIncl F i j hp z)) =
      (Φ.f q).hom (TIncl F i j hq z) := by
  rw [XIsoOfEq_hom_f, T_XIsoOfEq_TIncl]

/-- The same, on a summand. -/
lemma XIsoOfEq_muT_TIncl (F : CochainComplex (ModuleCat.{a} A) ℤ) (μT : T F ⟶ F)
    (i j : ℤ) {p q : ℤ} (h : p = q) (hp : i + j = p) (hq : i + j = q) (z : TFam F i j) :
    (F.XIsoOfEq h).hom ((μT.f p).hom (TIncl F i j hp z)) =
      (μT.f q).hom (TIncl F i j hq z) := by
  rw [XIsoOfEq_muT, T_XIsoOfEq_TIncl]

/-- `TensorProduct.curry` of the `(i,j)`-component of a chain map `F ⊗ F ⟶ F`. -/
noncomputable def muOf (F : CochainComplex (ModuleCat.{a} A) ℤ) (μT : T F ⟶ F) (i j : ℤ) :
    ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i+j)) :=
  TensorProduct.curry ((μT.f (i+j)).hom ∘ₗ (TIncl F i j rfl))

lemma muOf_apply (F : CochainComplex (ModuleCat.{a} A) ℤ) (μT : T F ⟶ F) (i j : ℤ)
    (x : ↥(F.X i)) (y : ↥(F.X j)) :
    muOf F μT i j x y = (μT.f (i+j)).hom ((TIncl F i j rfl) (x ⊗ₜ[A] y)) :=
  rfl

/-- **Extraction.**  From a chain map `μT : F ⊗ F ⟶ F` whose composition with the unit
`x ↦ e ⊗ x` is homotopic to the identity, we extract a Leibniz product on `F` for which `e`
is a unit up to homotopy. -/
theorem exists_leibniz_of_homotopy (A : Type a) [CommRing A]
    (F : CochainComplex (ModuleCat.{a} A) ℤ) (e : ↥(F.X 0))
    (ι : F ⟶ T F)
    (hι : ∀ (n : ℤ) (x : ↥(F.X n)), (ι.f n).hom x = TIncl F 0 n (by omega) (e ⊗ₜ[A] x))
    (μT : T F ⟶ F) (hH : Homotopy (ι ≫ μT) (𝟙 F)) :
    ∃ (μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j)))
      (H : ∀ j : ℤ, ↥(F.X (j + 1)) →ₗ[A] ↥(F.X j)),
      (∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
        (F.d (i + j) (i + j + 1)).hom ((μ i j x) y) =
          (F.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
          + (-1 : A) ^ i.natAbs •
              ((F.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((μ i (j + 1) x) ((F.d j (j + 1)).hom y)))) ∧
      (∀ (j : ℤ) (y : ↥(F.X (j + 1))),
        (F.XIsoOfEq (by omega : 0 + (j + 1) = j + 1)).hom ((μ 0 (j + 1) e) y) - y =
          (F.d j (j + 1)).hom (H j y) + H (j + 1) ((F.d (j + 1) ((j + 1) + 1)).hom y)) := by
  let μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j)) :=
    fun i j => muOf F μT i j
  let H : ∀ j : ℤ, ↥(F.X (j + 1)) →ₗ[A] ↥(F.X j) := fun j => (hH.hom (j + 1) j).hom
  refine ⟨μ, H, ?_, ?_⟩
  · intro i j x y
    have hμ : μ i j x y = (μT.f (i + j)).hom ((TIncl F i j rfl) (x ⊗ₜ[A] y)) :=
      muOf_apply F μT i j x y
    have hμ1 : ((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y =
        (μT.f ((i + 1) + j)).hom ((TIncl F (i + 1) j rfl)
          (((F.d i (i + 1)).hom x) ⊗ₜ[A] y)) := muOf_apply F μT (i+1) j _ y
    have hμ2 : ((μ i (j + 1) x) ((F.d j (j + 1)).hom y)) =
        (μT.f (i + (j + 1))).hom ((TIncl F i (j + 1) rfl)
          (x ⊗ₜ[A] ((F.d j (j + 1)).hom y))) := muOf_apply F μT i (j+1) x _
    rw [hμ, muT_d, Td_apply_incl]
    rw [show TdComp F i j rfl (x ⊗ₜ[A] y) =
      TIncl F (i+1) j (by omega) (((F.d i (i+1)).hom x) ⊗ₜ[A] y)
        + (Int.negOnePow i : A) • TIncl F i (j+1) (by omega)
          (x ⊗ₜ[A] ((F.d j (j+1)).hom y)) from TdComp_tmul F i j rfl x y]
    rw [map_add, LinearMap.map_smul, negOnePow_eq_pow_natAbs, hμ1, hμ2]
    rw [XIsoOfEq_muT_TIncl F μT (i+1) j (by omega : (i+1)+j = i+j+1) rfl (by omega),
      XIsoOfEq_muT_TIncl F μT i (j+1) (by omega : i+(j+1) = i+j+1) rfl (by omega)]
  · intro j y
    have hc := hH.comm (j + 1)
    rw [dNext_eq hH.hom (show (ComplexShape.up ℤ).Rel (j + 1) ((j + 1) + 1) from rfl),
      prevD_eq hH.hom (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl)] at hc
    have hc' := congrArg (fun (f : F.X (j + 1) ⟶ F.X (j + 1)) => f.hom) hc
    simp only [ModuleCat.hom_comp, ModuleCat.hom_add, HomologicalComplex.id_f] at hc'
    have h2 : ((ι ≫ μT).f (j+1)).hom y =
        (F.d j (j+1)).hom (H j y) + H (j+1) ((F.d (j+1) ((j+1)+1)).hom y) + y := by
      have hh := congrFun (congrArg DFunLike.coe hc') y
      simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
        LinearMap.add_apply, H] at hh ⊢
      rw [hh]
      abel
    have h1 : (F.XIsoOfEq (by omega : 0 + (j+1) = j+1)).hom ((μ 0 (j+1) e) y) =
        ((ι ≫ μT).f (j+1)).hom y := by
      have hμ' : (μ 0 (j+1) e) y = (μT.f (0 + (j+1))).hom
          ((TIncl F 0 (j+1) rfl) (e ⊗ₜ[A] y)) := muOf_apply F μT 0 (j+1) e y
      rw [hμ', XIsoOfEq_muT_TIncl F μT 0 (j+1) (by omega : 0+(j+1) = j+1) rfl (by omega)]
      rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply, hι]
    rw [h1, h2]
    abel

end Work.DSEQ0.TensorCpx
