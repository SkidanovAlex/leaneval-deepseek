import Mathlib
import Submission.Work.Certificates.SDR
import Submission.Work.Certificates.SDR.check_implies
import Submission.Work.Certificates.SDR.check_implies_homotopy_zero
import Submission.Work.Certificates.SDR.retract_chainMap
import Submission.Work.Certificates.subsingleton_hom_of_subsingleton
import Submission.Work.Certificates.chainMapCheck_sound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Certificates.SDR

set_option linter.style.haveILetI false

open CategoryTheory

variable {C : FinChainCx}

/-- A matrix `M : Matrix (Fin m) (Fin n) ℤ` viewed as the morphism `ℤ^n ⟶ ℤ^m` of
`ModuleCat ℤ` that it represents. -/
noncomputable def ofMat {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) :
    (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin m → ℤ)) :=
  ModuleCat.ofHom (Matrix.toLin' M)

theorem ofMat_comp {n m l : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) (N : Matrix (Fin l) (Fin m) ℤ) :
    (ofMat M ≫ ofMat N : (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin l → ℤ)))
      = ofMat (N * M) := by
  rw [ofMat, ofMat, ofMat, ← ModuleCat.ofHom_comp, ← Matrix.toLin'_mul]

theorem ofMat_add {n m : ℕ} (M N : Matrix (Fin m) (Fin n) ℤ) :
    (ofMat M + ofMat N : (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin m → ℤ)))
      = ofMat (M + N) := by
  apply ModuleCat.hom_ext
  simp [ofMat, ModuleCat.hom_add]

theorem ofMat_sub {n m : ℕ} (M N : Matrix (Fin m) (Fin n) ℤ) :
    (ofMat M - ofMat N : (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin m → ℤ)))
      = ofMat (M - N) := by
  apply ModuleCat.hom_ext
  simp [ofMat, ModuleCat.hom_sub]

theorem ofMat_id (n : ℕ) :
    (ofMat (1 : Matrix (Fin n) (Fin n) ℤ)) = 𝟙 (ModuleCat.of ℤ (Fin n → ℤ)) := by
  rw [ofMat, Matrix.toLin'_one, ModuleCat.ofHom_id]

theorem ofMat_injective {n m : ℕ} {M N : Matrix (Fin m) (Fin n) ℤ}
    (h : (ofMat M : (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin m → ℤ))) = ofMat N) :
    M = N := by
  have h' : Matrix.toLin' M = Matrix.toLin' N := congrArg ModuleCat.Hom.hom h
  have h'' := congrArg LinearMap.toMatrix' h'
  simpa using h''

/-- `ofMat` is injective on matrices, as an `iff`. -/
theorem ofMat_eq_iff {n m : ℕ} {M N : Matrix (Fin m) (Fin n) ℤ} :
    ((ofMat M : (ModuleCat.of ℤ (Fin n → ℤ)) ⟶ (ModuleCat.of ℤ (Fin m → ℤ))) = ofMat N)
      ↔ M = N :=
  ⟨ofMat_injective, fun h => by rw [h]⟩

/-- The matrix identity behind the chain-homotopy equation `1 - Zρ = ∂h + h∂` in degree
`k + 1`: rearranged to exhibit `Zρ - 1` as the sum of the two boundary terms, with the
homotopy component negated. -/
theorem mat_homotopy_id {n m₁ m₂ k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℤ) (ρ : Matrix (Fin k) (Fin n) ℤ)
    (bd' : Matrix (Fin n) (Fin m₂) ℤ) (h' : Matrix (Fin m₂) (Fin n) ℤ)
    (bd : Matrix (Fin m₁) (Fin n) ℤ) (h : Matrix (Fin n) (Fin m₁) ℤ)
    (hchk : 1 - Z * ρ = bd' * h' + h * bd) :
    (-h) * bd + bd' * (-h') = Z * ρ - 1 := by
  rw [Matrix.neg_mul, Matrix.mul_neg, ← neg_add, add_comm, ← hchk]
  abel

/-- The matrix identity behind the chain-homotopy equation in degree `0`, where the lower
boundary term is absent. -/
theorem mat_homotopy_id_zero {n m k : ℕ}
    (Z : Matrix (Fin n) (Fin k) ℤ) (ρ : Matrix (Fin k) (Fin n) ℤ)
    (bd : Matrix (Fin n) (Fin m) ℤ) (h : Matrix (Fin m) (Fin n) ℤ)
    (hchk : 1 - Z * ρ = bd * h) :
    bd * (-h) = Z * ρ - 1 := by
  rw [Matrix.mul_neg, ← hchk]
  abel

/-- Subtraction of chain maps is computed degreewise (definitionally). -/
@[simp] theorem hom_sub_f' {K L : ChainComplex (ModuleCat ℤ) ℕ} (f g : K ⟶ L) (i : ℕ) :
    (f - g).f i = f.f i - g.f i := rfl

/-- The differential of the explicit complex `cxOf C` in terms of the sparse matrix `bd`. -/
theorem cxOf_d_eq_ofMat (k : ℕ) :
    (cxOf C).d (k+1) k = ofMat ((C.bd k).toMatrix) := by
  simp only [cxOf, ChainComplex.of_d, ofMat]

/-- The negated homotopy component `h k : C_k ⟶ C_{k+1}` of the certificate. -/
noncomputable def Hneg (S : SDR C) (k : ℕ) :
    (cxOf C).X k ⟶ (cxOf C).X (k+1) :=
  ofMat (-((S.h k).toMatrix))

@[simp] theorem Hneg_eq (S : SDR C) (k : ℕ) :
    Hneg S k = ofMat (-((S.h k).toMatrix)) := rfl

/-- The degreewise family underlying the chain homotopy: `hom i (i+1) = -h i` and zero
elsewhere. -/
noncomputable def homFam (S : SDR C) :
    ∀ i j, (cxOf C).X i ⟶ (cxOf C).X j :=
  fun i j => if h : j = i + 1 then Hneg S i ≫ eqToHom (by rw [h]) else 0

theorem homFam_succ (S : SDR C) (i : ℕ) : homFam S i (i+1) = Hneg S i := by
  rw [homFam]
  simp only [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

theorem homFam_eq_zero (S : SDR C) {i j : ℕ} (h : ¬ j = i + 1) : homFam S i j = 0 := by
  rw [homFam]
  exact dite_eq_right h

theorem homFam_rel_zero (S : SDR C) (i j : ℕ) (h : ¬ (ComplexShape.down ℕ).Rel j i) :
    homFam S i j = 0 := by
  refine homFam_eq_zero S (fun hji => h ?_)
  rw [ComplexShape.down_Rel]
  exact hji.symm

/-- The degreewise component of `Rc ≫ Zc - 𝟙` in terms of the certificate's matrices. -/
theorem comp_sub_id_apply (S : SDR C)
    (Zc : ChainHom (zeroCx S.b) (cxOf C))
    (hZc : ∀ k, Zc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix)))
    (Rc : ChainHom (cxOf C) (zeroCx S.b))
    (hRc : ∀ k, Rc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix))) (i : ℕ) :
    (chainComp Rc Zc - chainId (cxOf C)).f i
      = ofMat ((S.Z i).toMatrix * (S.ρ i).toMatrix - 1) := by
  rw [chainComp, chainId]
  rw [hom_sub_f', HomologicalComplex.comp_f, HomologicalComplex.id_f, hRc i, hZc i]
  rw [← ofMat, ← ofMat, ofMat_comp, ← ofMat_id, ofMat_sub]

theorem homotopy_exists (S : SDR C) (h : S.check = true)
    (Zc : ChainHom (FinChainCx.zeroDiff S.b).toChainComplex C.toChainComplex)
    (hZc : ∀ k, Zc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.Z k).toMatrix)))
    (Rc : ChainHom C.toChainComplex (FinChainCx.zeroDiff S.b).toChainComplex)
    (hRc : ∀ k, Rc.f k = ModuleCat.ofHom (Matrix.toLin' ((S.ρ k).toMatrix))) :
    Nonempty (ChainHomotopy (chainComp Rc Zc) (chainId C.toChainComplex)) := by
  have key : ∀ i, (Homotopy.nullHomotopicMap (homFam S)).f i
      = (chainComp (K := cxOf C) (L := zeroCx S.b) (M := cxOf C) Rc Zc
          - chainId (cxOf C)).f i := by
    intro i
    rcases Nat.lt_or_ge i S.N with hi | hi
    · rcases i with _ | i'
      · -- degree 0
        rw [Homotopy.nullHomotopicMap_f_of_not_rel_left (k₁ := 1) (k₀ := 0)
          (by simp [ComplexShape.down_Rel])
          (by intro l; rw [ComplexShape.down_Rel]; omega)]
        rw [homFam_succ S 0, Hneg_eq, cxOf_d_eq_ofMat (C := C) 0]
        rw [ofMat_comp, comp_sub_id_apply S Zc hZc Rc hRc 0, ofMat_eq_iff]
        exact mat_homotopy_id_zero _ _ _ _ (check_implies_homotopy_zero S h)
      · -- degree i'+1, with i' < S.N
        have hlt : i' < S.N := by omega
        rw [Homotopy.nullHomotopicMap_f (k₁ := i'+1) (k₀ := i') (k₂ := i'+2)
          (by rw [ComplexShape.down_Rel]; omega) (by rw [ComplexShape.down_Rel])]
        rw [homFam_succ S i', homFam_succ S (i'+1), Hneg_eq, Hneg_eq,
          cxOf_d_eq_ofMat (C := C) i', cxOf_d_eq_ofMat (C := C) (i'+1)]
        rw [ofMat_comp, ofMat_comp, comp_sub_id_apply S Zc hZc Rc hRc (i'+1)]
        rw [ofMat_add, ofMat_eq_iff]
        exact mat_homotopy_id _ _ _ _ _ _
          ((check_implies S h i' hlt).2.2.2)
    · -- degree i ≥ S.N: both objects are zero, so all morphisms agree
      haveI : Subsingleton ((cxOf C).X i) := subsingleton_X_of_dim_eq_zero C (S.dim_zero i hi)
      haveI : Subsingleton ((cxOf C).X i ⟶ (cxOf C).X i) := subsingleton_hom_of_subsingleton
      exact Subsingleton.elim _ _
  have hnull : Homotopy.nullHomotopicMap (homFam S)
      = chainComp (K := cxOf C) (L := zeroCx S.b) (M := cxOf C) Rc Zc
          - chainId (cxOf C) :=
    HomologicalComplex.Hom.ext (funext key)
  exact ⟨(Homotopy.equivSubZero
    (f := chainComp (K := cxOf C) (L := zeroCx S.b) (M := cxOf C) Rc Zc)
    (g := chainId (cxOf C))).symm
    (hnull ▸ Homotopy.nullHomotopy (homFam S) (homFam_rel_zero S))⟩

end Work.Certificates.SDR
