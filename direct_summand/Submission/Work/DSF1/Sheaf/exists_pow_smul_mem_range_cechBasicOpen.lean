import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.cech_map_clearing
import Submission.Work.DSF1.Sheaf.structPresheaf_isLocalization_map
import Submission.Work.DSF1.Sheaf.isAffineOpen_Eobj_of
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.CechSetup


set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

theorem exists_pow_smul_mem_range_cechBasicOpen {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsAffine X] {ι : Type} [Fintype ι]
    (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤))) (i : ι) (n : ℕ)
    (s : (Work.DSF1.Sheaf.cechBasicOpen X f).X (n + 1))
    (hs : ((Work.DSF1.Sheaf.cechBasicOpen X f).d (n + 1) (n + 2)).hom s = 0) :
    ∃ (k : ℕ) (t : (Work.DSF1.Sheaf.cechBasicOpen X f).X n),
      ((Work.DSF1.Sheaf.cechBasicOpen X f).d n (n + 1)).hom t = f i ^ k • s := by
  classical
  -- Each member `D (f j)` of the family is an affine open.
  have hUaff : ∀ j : ι, IsAffineOpen (X.basicOpen (f j)) :=
    fun j => (isAffineOpen_top X).basicOpen (f j)
  -- Clearing of denominators componentwise, from the "localization" statement over the
  -- affine open `Eobj U m x = ⨅ a, D (f (x a))`.
  have hcomp : ∀ (m : ℕ) (x : (Work.DSF1.Cech.E (basicOpenFamily X f)).obj
        (Opposite.op (SimplexCategory.mk m)) |>.I),
      (∀ z : (structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj
            (basicOpenFamily X f) m x ⊓ X.basicOpen (f i))),
        ∃ (k : ℕ) (t : (structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj
            (basicOpenFamily X f) m x))),
          ((structPresheaf X).map (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj
              (basicOpenFamily X f) m x ⊓ X.basicOpen (f i) ≤
              Work.DSF1.Cech.Eobj (basicOpenFamily X f) m x)).op).hom t = f i ^ k • z) ∧
      (∀ t : (structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj
            (basicOpenFamily X f) m x)),
        ((structPresheaf X).map (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj
            (basicOpenFamily X f) m x ⊓ X.basicOpen (f i) ≤
            Work.DSF1.Cech.Eobj (basicOpenFamily X f) m x)).op).hom t = 0 →
          ∃ k : ℕ, f i ^ k • t = 0) :=
    fun m x => structPresheaf_isLocalization_map
      (Work.DSF1.Cech.isAffineOpen_Eobj_of (basicOpenFamily X f) hUaff m x) (f i)
  -- Clearing of denominators for the comparison map of Čech complexes.
  obtain ⟨hclearS, hclearK⟩ :=
    cech_map_clearing (basicOpenFamily X f) (X.basicOpen (f i)) (f i)
      (fun m x => (hcomp m x).1) (fun m x => (hcomp m x).2)
  -- The complex localized at `D (f i)` is exact in positive degrees: it is contractible
  -- because the coefficient presheaf `Qo P V` inverts the cofaces inserting `i`.
  have hdel : Work.DSF1.Cech.IsIsoDeletion (basicOpenFamily X f)
      (Work.DSF1.Cech.Qo (structPresheaf X) (X.basicOpen (f i))) i :=
    Work.DSF1.Cech.isIsoDeletion_Qo (U := basicOpenFamily X f) (P := structPresheaf X)
      (i₀ := i) (V := X.basicOpen (f i)) le_rfl
  have hunit := (Work.DSF1.Cech.UnitCase (basicOpenFamily X f)
      (Work.DSF1.Cech.Qo (structPresheaf X) (X.basicOpen (f i))) i hdel).2.1
  -- Abbreviations for the two complexes and the comparison map.
  set K : CochainComplex (ModuleCat ↥(X.presheaf.obj (Opposite.op ⊤))) ℕ :=
    (cechComplexFunctor (basicOpenFamily X f)).obj (structPresheaf X) with hK
  set K' : CochainComplex (ModuleCat ↥(X.presheaf.obj (Opposite.op ⊤))) ℕ :=
    (cechComplexFunctor (basicOpenFamily X f)).obj
      (Work.DSF1.Cech.Qo (structPresheaf X) (X.basicOpen (f i))) with hK'
  set φ : K ⟶ K' := (cechComplexFunctor (basicOpenFamily X f)).map
      (Work.DSF1.Cech.etaO (structPresheaf X) (X.basicOpen (f i))) with hφ
  -- The image of the cocycle `s` in the localized complex is a cocycle.
  have hcocyc : (K'.d (n + 1) (n + 2)).hom ((φ.f (n + 1)).hom s) = 0 := by
    have hcomm := HomologicalComplex.Hom.comm' φ (n + 1) (n + 2)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from by simp)
    have h := congrArg (fun (g : K.X (n + 1) ⟶ K'.X (n + 2)) => g.hom s) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hs, map_zero] at h
    exact h
  -- A lift of `φ s` in the localized complex.
  obtain ⟨t', ht'⟩ := hunit n ((φ.f (n + 1)).hom s) hcocyc
  -- Clear denominators of `t'`.
  obtain ⟨k, t, ht⟩ := hclearS n t'
  -- The comparison map of `d t - f i ^ k • s` vanishes.
  have hφzero : (φ.f (n + 1)).hom ((K.d n (n + 1)).hom t - f i ^ k • s) = 0 := by
    have hcomm2 := HomologicalComplex.Hom.comm' φ n (n + 1)
      (show (ComplexShape.up ℕ).Rel n (n + 1) from by simp)
    have h2 := congrArg (fun (g : K.X n ⟶ K'.X (n + 1)) => g.hom t) hcomm2
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    have hsub : (φ.f (n + 1)).hom ((K.d n (n + 1)).hom t)
        = (φ.f (n + 1)).hom (f i ^ k • s) := by
      rw [h2.symm, ht, map_smul, ht', map_smul]
    rw [map_sub, hsub, sub_self]
  -- Clear denominators of `d t - f i ^ k • s`.
  obtain ⟨m, hm⟩ := hclearK (n + 1) ((K.d n (n + 1)).hom t - f i ^ k • s) hφzero
  refine ⟨m + k, f i ^ m • t, ?_⟩
  have hm' : f i ^ m • ((K.d n (n + 1)).hom t) = f i ^ m • (f i ^ k • s) := by
    rw [← sub_eq_zero, ← smul_sub]
    exact hm
  rw [map_smul, hm', smul_smul, ← pow_add]

end Work.DSF1.Sheaf
