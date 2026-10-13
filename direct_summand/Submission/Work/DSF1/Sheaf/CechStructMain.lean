import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.forgetCechIsoGeneral
import Submission.Work.DSF1.Sheaf.structPresheaf_isLocalization_map
import Submission.Work.DSF1.Sheaf.cech_map_clearing
import Submission.Work.DSF1.Sheaf.exists_pow_smul_mem_range_cechBasicOpen_u
import Submission.Work.DSF1.Sheaf.bijective_smul_cech_term_u
import Submission.Work.DSF1.Sheaf.exists_pow_smul_mem_of_forall_smul_pow_mem_u
import Submission.Work.DSF1.Sheaf.exists_d_eq_of_smul_pow_mem_range_u
import Submission.Work.DSF1.Sheaf.exists_pow_mem_span_of_basicOpen_cover_u
import Submission.Work.DSF1.Sheaf.cechTrivAt_iff_homology

/-!
# Čech exactness of the structure sheaf along a family of basic opens covering a basic open

Let `X` be an affine scheme, `f : ι → Γ(X,⊤)` a finite family of global sections and
`g : Γ(X,⊤)` a global section such that `D (f i) ⊆ D g` for all `i` and `D g ⊆ ⋃ D (f i)`.
Then the Čech complex of the structure sheaf of `X` along the family `D (f i)` is exact in
positive degrees.

The proof combines:

* the fact that the complex localized at `D (f i)` is exact in positive degrees (the "unit
  case", `Work.DSF1.Cech.UnitCase` and `Work.DSF1.Cech.isIsoDeletion_Qo`), so that a cocycle
  becomes a boundary after multiplication by a power of `f i`
  (`exists_pow_smul_mem_range_cechBasicOpen`);
* the descent from that statement to the statement that the cocycle itself is a boundary:
  since every Čech term lies inside the affine open `D g`, the section `g` acts invertibly on
  every term (`bijective_smul_cech_term`), while `g` lies in the radical of the ideal generated
  by the `f i` (`exists_pow_mem_span_of_basicOpen_cover`); hence a power of `g` times the
  cocycle is a boundary (`exists_pow_smul_mem_of_forall_smul_pow_mem`) and the invertibility
  of `g` removes the power (`exists_d_eq_of_smul_pow_mem_range`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

/-! ## Transport of elementwise exactness -/

/-- Elementwise exactness in positive degrees of a complex of `R`-modules implies the same
for the complex obtained by applying the forgetful functor to abelian groups. -/
theorem cechTrivAt_forgetMod {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : ∀ s : K.X (n + 1), K.d (n + 1) (n + 2) s = 0 →
      ∃ t : K.X n, K.d n (n + 1) t = s) :
    ∀ s : ((Functor.mapHomologicalComplex (forgetMod R) (ComplexShape.up ℕ)).obj K).X (n + 1),
      ((Functor.mapHomologicalComplex (forgetMod R) (ComplexShape.up ℕ)).obj K).d (n + 1) (n + 2) s
        = 0 →
      ∃ t : ((Functor.mapHomologicalComplex (forgetMod R) (ComplexShape.up ℕ)).obj K).X n,
        ((Functor.mapHomologicalComplex (forgetMod R) (ComplexShape.up ℕ)).obj K).d n (n + 1) t
          = s := by
  intro s hs
  exact h s hs

/-- Elementwise exactness in positive degrees transfers along an isomorphism of cochain
complexes of abelian groups. -/
theorem cechTrivAt_of_iso {K L : CochainComplex AddCommGrpCat.{u} ℕ} (e : K ≅ L) (n : ℕ)
    (h : ∀ s : K.X (n + 1), K.d (n + 1) (n + 2) s = 0 →
      ∃ t : K.X n, K.d n (n + 1) t = s) :
    ∀ s : L.X (n + 1), L.d (n + 1) (n + 2) s = 0 → ∃ t : L.X n, L.d n (n + 1) t = s := by
  intro s hs
  have hs' : K.d (n + 1) (n + 2) ((e.inv.f (n + 1)) s) = 0 := by
    have hcomm := (e.inv).comm' (n + 1) (n + 2) (by simp)
    have hh := congrArg (fun (f : L.X (n + 1) ⟶ K.X (n + 2)) => f s) hcomm
    simp only [ConcreteCategory.comp_apply] at hh
    rw [hh, hs, map_zero]
  obtain ⟨t', ht'⟩ := h _ hs'
  refine ⟨(e.hom.f n) t', ?_⟩
  have hcomm := (e.hom).comm' n (n + 1) (by simp)
  have hh := congrArg (fun (f : K.X n ⟶ L.X (n + 1)) => f t') hcomm
  simp only [ConcreteCategory.comp_apply] at hh
  rw [hh, ht']
  have hcomp : (e.inv.f (n + 1)) ≫ (e.hom.f (n + 1)) = 𝟙 (L.X (n + 1)) := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have h2 := congrArg (fun (f : L.X (n + 1) ⟶ L.X (n + 1)) => (ConcreteCategory.hom f) s) hcomp
  rw [CategoryTheory.id_apply] at h2
  exact h2

/-! ## Exactness in positive degrees -/

/-- **A cocycle of the Čech complex of the basic-open family is a boundary.** -/
theorem exists_d_eq_cechBasicOpen (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X]
    {ι : Type u} [Fintype ι] (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤)))
    (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g)
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) (n : ℕ)
    (s : (cechBasicOpen X f).X (n + 1))
    (hs : ((cechBasicOpen X f).d (n + 1) (n + 2)).hom s = 0) :
    ∃ t : (cechBasicOpen X f).X n, ((cechBasicOpen X f).d n (n + 1)).hom t = s := by
  -- Step 1: for every `i`, some power of `f i` times `s` is a boundary.
  have hinput : ∀ i : ι, ∃ (k : ℕ) (t : (cechBasicOpen X f).X n),
      ((cechBasicOpen X f).d n (n + 1)).hom t = f i ^ k • s :=
    fun i => exists_pow_smul_mem_range_cechBasicOpen_u (X := X) (ι := ι) f i n s hs
  choose k tk htk using hinput
  -- Step 2: some power of `g` times `s` is a boundary.
  obtain ⟨N, hN⟩ := exists_pow_mem_span_of_basicOpen_cover_u (X := X) (ι := ι) f g hcov
  obtain ⟨M', hM'⟩ := exists_pow_smul_mem_of_forall_smul_pow_mem_u
    (LinearMap.range ((cechBasicOpen X f).d n (n + 1)).hom) s f k g
    (fun i => by rw [← htk i]; exact LinearMap.mem_range_self _ _) ⟨N, hN⟩
  -- Step 3: `g` acts invertibly on every term of the complex, so `s` itself is a boundary.
  exact exists_d_eq_of_smul_pow_mem_range_u (cechBasicOpen X f) g
    (fun m => bijective_smul_cech_term_u (X := X) (ι := ι) f g hmem m) n s M' hM'

/-- **The Čech cocycles of the unit sheaf along the basic-open family trivialize.** -/
theorem cechTrivAt_cech_unit (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X]
    {ι : Type u} [Fintype ι] (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤)))
    (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g)
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) (n : ℕ) :
    CechTrivAt (cechComplex (basicOpenFamily X f) (SheafOfModules.unit X.ringCatSheaf)) n := by
  obtain ⟨e⟩ := forget_cech_iso_general (basicOpenFamily X f) (structPresheaf X)
  have hK : ∀ s : (cechBasicOpen X f).X (n + 1), (cechBasicOpen X f).d (n + 1) (n + 2) s = 0 →
      ∃ t : (cechBasicOpen X f).X n, (cechBasicOpen X f).d n (n + 1) t = s :=
    fun s hs => exists_d_eq_cechBasicOpen X f g hmem hcov n s hs
  exact cechTrivAt_of_iso e n (cechTrivAt_forgetMod (cechBasicOpen X f) n hK)

/-- **The main result.**  The homology of the Čech complex of the structure sheaf of an
affine scheme `X` along the basic-open family `D (f i)`, where `D (f i) ⊆ D g` for every `i`
and `D g ⊆ ⋃ D (f i)`, vanishes in positive degrees, for coefficients the unit sheaf. -/
theorem isZero_homology_cech_unit (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine X]
    {ι : Type u} [Fintype ι] (f : ι → ↥(X.presheaf.obj (Opposite.op ⊤)))
    (g : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g)
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) (n : ℕ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology
        (cechComplex (basicOpenFamily X f) (SheafOfModules.unit X.ringCatSheaf)) n) := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  exact (cechTrivAt_iff_homology _ n').mp (cechTrivAt_cech_unit X f g hmem hcov n')

end Work.DSF1.Sheaf
