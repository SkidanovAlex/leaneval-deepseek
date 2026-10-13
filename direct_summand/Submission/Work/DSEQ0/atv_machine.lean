import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.AcyclicToolkit
import Submission.Work.DSF1.Sheaf.syzSES_shortExact
import Submission.Work.DSF1.Sheaf.syz_zero_iso
import Submission.Work.DSF1.Sheaf.sections_lift_of_cechTriv
import Submission.Work.DSF1.Sheaf.cechHomology_quotient
import Submission.Work.DSF1.Sheaf.cechTrivAt_iff_homology
import Submission.Work.DSF1.Sheaf.epi_map_syzProj
import Submission.Work.DSF1.Sheaf.exists_basicOpen_cover_with_lifts
import Submission.Work.DSF1.Sheaf.rightDerived_isZero_of_acyclic_resolution
import Submission.Work.DSG1.injectiveIsFlasque
import Submission.Work.DSEQ0.atv_flasque

/-!
# Affine vanishing from Čech-triviality of the resolution

This module contains the machinery which derives the vanishing of the higher right derived
functors of `Γ(X, ⊤)` at a sheaf of modules `Z` on an **affine** scheme `X` from the
Čech-triviality of an injective resolution of `Z`:

* `Work.DSEQ0.CechTrivOnBasic X Z` : the Čech complex of any finite family of basic opens
  `D (f i)` which covers a basic open `D g` (with all `D (f i) ≤ D g`) has vanishing homology in
  positive degrees, with coefficients in `Z`;
* `Work.DSEQ0.cechTrivOnBasic_syz_and_lift` : the syzygy induction, which propagates
  Čech-triviality from `syz K 0` to all syzygies of a complex `K` which is exact in positive
  degrees and whose terms are injective (hence flasque), and produces the surjectivity
  statements `SectionsSurjOnBasic X (syzProj K k)`;
* `Work.DSEQ0.isZero_rightDerived_of_cechTrivOnBasic` : the conclusion
  `R^q Γ(X, ⊤) (Z) = 0` for `q > 0`.

These are copies of `Work.DSF1.Sheaf.CechTrivOnBasic`,
`Work.DSF1.Sheaf.cechTrivOnBasic_syz_and_lift` and
`Work.DSF1.Sheaf.isZero_rightDerived_unit_of_isAffine` (in
`Submission/Work/DSF1/Sheaf/AffineUnitAcyclic.lean`), with two changes: the last one is stated
for an arbitrary sheaf `Z` rather than for the structure sheaf, and the flasque-Čech input
`Work.DSF1.Sheaf.flasque_hasCechCohomology` is replaced by the private copy
`Work.DSEQ0.flasque_hasCechCohomology'` (the original file cannot be imported, since it depends
on the module `cechAugNat_exact` which does not compile).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators
open Work.DSF1.Sheaf

namespace Work.DSEQ0

universe u v w x

/-- `CechTrivOnBasic X Z` says that for every finite family of basic opens `D (f i)` which is
contained in and covers a basic open `D g`, the Čech complex of the family `D (f i)` with
coefficients `Z` has vanishing homology in positive degrees.  (For `Z` quasi-coherent on an
affine `X` this is Stacks 30.2.2; the base case used below is proved for `Z = unit` in
`Work.DSF1.Sheaf.cechTrivOnBasic_unit`.) -/
def CechTrivOnBasic (X : AlgebraicGeometry.Scheme.{u})
    (Z : SheafOfModules X.ringCatSheaf) : Prop :=
  ∀ {ι : Type u} [Finite ι] (f : ι → X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens))),
    (∀ i, X.basicOpen (f i) ≤ X.basicOpen g) → X.basicOpen g ≤ ⨆ i, X.basicOpen (f i) →
    ∀ n : ℕ, 0 < n → IsZero
      (HomologicalComplex.homology (cechComplex (fun i => X.basicOpen (f i)) Z) n)

/-- `SectionsSurjOnBasic X φ` says that `φ` induces a surjection on sections over every basic
open of `X`. -/
def SectionsSurjOnBasic (X : AlgebraicGeometry.Scheme.{u})
    {Z Z' : SheafOfModules X.ringCatSheaf} (φ : Z ⟶ Z') : Prop :=
  ∀ (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens))),
    ∀ y : sectionsAt Z' (X.basicOpen g),
      ∃ x : sectionsAt Z (X.basicOpen g), sectionsMap φ (X.basicOpen g) x = y

/-- `CechTrivOnBasic` transported along an isomorphism of the coefficients. -/
lemma CechTrivOnBasic.of_iso {X : AlgebraicGeometry.Scheme.{u}} {Z Z' : X.Modules} (e : Z ≅ Z')
    (h : CechTrivOnBasic X Z) : CechTrivOnBasic X Z' := by
  unfold CechTrivOnBasic
  intro ι _ f g hmem hcov n hn
  refine IsZero.of_iso (h f g hmem hcov n hn) ?_
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso
    ((cechComplexFunctor (fun i => X.basicOpen (f i))).mapIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.toTopCat).mapIso
        ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e.symm)))

/-- `CechTrivOnBasic X Z` gives in particular the vanishing of the first Čech cohomology, in the
`CechTrivAt` form used by the lifting lemma. -/
lemma cechTrivAt_of_cechTrivOnBasic {X : AlgebraicGeometry.Scheme.{u}} {Z : X.Modules}
    (h : CechTrivOnBasic X Z) {ι : Type u} [Finite ι]
    (f : ι → X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (g : X.presheaf.obj (Opposite.op (⊤ : X.Opens)))
    (hmem : ∀ i, X.basicOpen (f i) ≤ X.basicOpen g)
    (hcov : X.basicOpen g ≤ ⨆ i, X.basicOpen (f i)) :
    CechTrivAt (cechComplex (fun i => X.basicOpen (f i)) Z) 0 :=
  (cechTrivAt_iff_homology _ 0).mpr (h f g hmem hcov 1 (by norm_num))

/-- A complex quasi-isomorphic to the one-term complex `M[0]` is exact in every positive
degree. -/
lemma exactAt_of_quasiIso_single' {C : Type w} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] {M : C} {K : CochainComplex C ℕ}
    [∀ i, HomologicalComplex.HasHomology K i]
    (i : (CochainComplex.single₀ C).obj M ⟶ K) [QuasiIso i] :
    ∀ n : ℕ, 0 < n → K.ExactAt n := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact (exactAt_iff_of_quasiIsoAt i (m + 1)).1 (CochainComplex.exactAt_succ_single_obj M m)

/-- Splitting off the first term of an infimum over `Fin (r+1)`. -/
lemma iInf_fin_succ {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ} (g : Fin (r + 1) → X.Opens) :
    (⨅ i, g i) = g 0 ⊓ (⨅ i : Fin r, g i.succ) := by
  refine le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ))
    (le_iInf fun i => ?_)
  cases i using Fin.cases with
  | zero => exact inf_le_left
  | succ j => exact inf_le_right.trans (iInf_le _ j)

/-- The finite intersection of basic opens `D (f i)` is the basic open `D (∏ i, f i)`. -/
lemma iInf_basicOpen_eq_basicOpen_prod {X : AlgebraicGeometry.Scheme.{u}} (r : ℕ) :
    ∀ f : Fin r → X.presheaf.obj (Opposite.op (⊤ : X.Opens)),
      (⨅ i : Fin r, X.basicOpen (f i)) = X.basicOpen (∏ i : Fin r, f i) := by
  induction r with
  | zero => intro f; simp
  | succ r ih =>
      intro f
      rw [Fin.prod_univ_succ, Scheme.basicOpen_mul, ← ih (fun i => f i.succ)]
      exact iInf_fin_succ _

/-- **The induction invariant.**  For a complex `K` which is exact in positive degrees, all of
whose terms are injective, and whose `0`-th syzygy has Čech-trivial cocycles, every syzygy has
Čech-trivial cocycles and the projection `syzProj K k` is surjective on sections over every
basic open. -/
theorem cechTrivOnBasic_syz_and_lift (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsAffine X]
    (K : CochainComplex (SheafOfModules X.ringCatSheaf) ℕ)
    [∀ i, HomologicalComplex.HasHomology K i]
    (hex : ∀ n : ℕ, 0 < n → IsZero (K.homology n))
    (hKinj : ∀ n : ℕ, Injective (K.X n))
    (hbase : CechTrivOnBasic X (syz K 0)) :
    ∀ k : ℕ, CechTrivOnBasic X (syz K k) ∧ SectionsSurjOnBasic X (syzProj K k) := by
  have hlift_of_cech : ∀ k : ℕ, CechTrivOnBasic X (syz K k) →
      SectionsSurjOnBasic X (syzProj K k) := by
    intro k hcz
    unfold SectionsSurjOnBasic
    intro g y
    obtain ⟨r', f', hf', hcov', hlift'⟩ :=
      exists_basicOpen_cover_with_lifts (X := X) (syzSES K k)
        (syzSES_shortExact K k (hex (k + 1) (by omega))) g y
    have hVU : ∀ j : ULift.{u} (Fin r'), X.basicOpen (f' j.down) ≤ X.basicOpen g :=
      fun j => hf' j.down
    have hcov'' : iSup (fun j : ULift.{u} (Fin r') => X.basicOpen (f' j.down)) =
        X.basicOpen g := by
      refine le_antisymm (iSup_le hVU) ?_
      refine hcov'.trans (iSup_le fun i =>
        le_iSup (fun j : ULift.{u} (Fin r') => X.basicOpen (f' j.down)) (ULift.up i))
    have hmem'' : X.basicOpen g ≤
        ⨆ j : ULift.{u} (Fin r'), X.basicOpen (f' j.down) := hcov''.ge
    have htriv : CechTrivAt (cechComplex
        (fun j : ULift.{u} (Fin r') => X.basicOpen (f' j.down)) (syz K k)) 0 :=
      cechTrivAt_of_cechTrivOnBasic (X := X) hcz (fun j : ULift.{u} (Fin r') => f' j.down) g hVU
        hmem''
    refine sections_lift_of_cechTriv (X := X) (ι := ULift.{u} (Fin r'))
      (syzSES K k)
      (syzSES_shortExact K k (hex (k + 1) (by omega))) (X.basicOpen g)
      (fun j : ULift.{u} (Fin r') => X.basicOpen (f' j.down)) hVU hcov'' htriv y ?_
    intro j
    obtain ⟨x', hx'⟩ := hlift' j.down
    exact ⟨x', hx'⟩
  -- the Čech half of the invariant, by induction on `k`
  have hchain : ∀ k : ℕ, CechTrivOnBasic X (syz K k) := by
    intro k
    induction k with
    | zero => exact hbase
    | succ k ih =>
        unfold CechTrivOnBasic
        intro ι _ f g hmem hcov n hn
        refine cechHomology_quotient (X := X) (ι := ι)
          (syzSES K k)
          (syzSES_shortExact K k (hex (k + 1) (by omega)))
          (fun i => X.basicOpen (f i)) ?_ ?_ ?_ n hn
        · -- surjectivity over the finite intersections, from the lifting half of the invariant
          intro p x
          have heq : (⨅ a : Fin (p + 1), X.basicOpen (f (x a))) =
              X.basicOpen (∏ a : Fin (p + 1), f (x a)) :=
            iInf_basicOpen_eq_basicOpen_prod (p + 1) (fun a => f (x a))
          exact heq ▸ (hlift_of_cech k ih (∏ a : Fin (p + 1), f (x a)))
        · -- the middle term `K.X k` is injective, hence flasque, hence has acyclic Čech complexes
          intro m hm
          haveI : Injective (K.X k) := hKinj k
          have hfl : TopCat.Presheaf.IsFlasque
              ((SheafOfModules.toSheaf X.ringCatSheaf).obj (K.X k)).obj :=
            Work.DSG1.injectiveIsFlasque X (K.X k)
          have hcech : Work.DSF1.Sheaf.HasCechCohomology (K.X k) :=
            flasque_hasCechCohomology' (X := X) (K.X k) hfl
          have hn' : m = (m - 1) + 1 := by omega
          rw [hn']
          exact (cechTrivAt_iff_homology _ (m - 1)).mp
            (hcech (fun i => X.basicOpen (f i)) (m - 1))
        · -- the first term, in degrees `≥ 2`
          intro m hm
          exact ih f g hmem hcov m (by omega)
  intro k
  exact ⟨hchain k, hlift_of_cech k (hchain k)⟩

/-- Converse of `epi_map_syzProj`: if `F` of the projection onto the `(n+1)`-st syzygy is an
epimorphism, then the `F`-image of `K` is exact in degree `n+1`. -/
theorem isZero_homology_mapHomologicalComplex_of_epi_map_syzProj {C : Type w}
    [CategoryTheory.Category.{v, w} C] [CategoryTheory.Abelian C]
    {D : Type x} [CategoryTheory.Category.{u, x} D] [CategoryTheory.Abelian D]
    (K : CochainComplex C ℕ) [∀ i : ℕ, HomologicalComplex.HasHomology K i]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F] (n : ℕ)
    (h : CategoryTheory.Epi (F.map (syzProj K n))) :
    CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (n + 1)) := by
  have key : F.map (syzProj K n) ≫ kernelComparison (K.d (n + 1) (n + 2)) F =
      Limits.kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1)))
        (by rw [← F.map_comp, HomologicalComplex.d_comp_d, F.map_zero]) :=
    map_lift_kernelComparison (K.d (n + 1) (n + 2)) F
      (HomologicalComplex.d_comp_d K n (n + 1) (n + 2))
  have hIso : IsIso (kernelComparison (K.d (n + 1) (n + 2)) F) := by
    change IsIso (kernelComparison (K.d (n + 1) (n + 2)) F)
    infer_instance
  haveI : IsIso (kernelComparison (K.d (n + 1) (n + 2)) F) := hIso
  have h2 : CategoryTheory.Epi (F.map (syzProj K n) ≫ kernelComparison (K.d (n + 1) (n + 2)) F) :=
    (epi_comp_iff_of_isIso (F.map (syzProj K n))
      (kernelComparison (K.d (n + 1) (n + 2)) F)).mpr h
  have hlift : Epi (Limits.kernel.lift (F.map (K.d (n + 1) (n + 2))) (F.map (K.d n (n + 1)))
      (by rw [← F.map_comp, HomologicalComplex.d_comp_d, F.map_zero])) := key ▸ h2
  -- hence the short complex of the image complex in degrees `n, n+1, n+2` is exact
  have hS : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc' n (n + 1) (n + 2)).Exact :=
    (ShortComplex.exact_iff_epi_kernel_lift
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc' n (n + 1) (n + 2))).mpr hlift
  have hEx : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff'
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n (n + 1) (n + 2)
      (ComplexShape.prev_eq' _ (ComplexShape.up_mk n (n + 1) rfl))
      (ComplexShape.next_eq' _ (ComplexShape.up_mk (n + 1) (n + 2) rfl))).mpr hS
  exact hEx.isZero_homology

/-- **Affine vanishing from Čech-triviality.**  If `X` is affine and the sheaf of modules `Z`
has Čech-trivial cocycles for every finite family of basic opens covering a basic open
(`CechTrivOnBasic X Z`), then the higher right derived functors of the global sections functor
`Γ(X, ⊤)` at `Z` vanish. -/
theorem isZero_rightDerived_of_cechTrivOnBasic (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsAffine X]
    [CategoryTheory.EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    (Z : SheafOfModules X.ringCatSheaf) (hZ : CechTrivOnBasic X Z) :
    ∀ q : ℕ, 0 < q → CategoryTheory.Limits.IsZero
      (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerived q).obj
        Z) := by
  classical
  -- an injective resolution of `Z`
  let I : InjectiveResolution Z := injectiveResolution Z
  have hex : ∀ n : ℕ, 0 < n → IsZero (I.cocomplex.homology n) := by
    intro n hn
    exact (HomologicalComplex.exactAt_iff_isZero_homology I.cocomplex n).mp
      (exactAt_of_quasiIso_single' I.ι n hn)
  have hKinj : ∀ n : ℕ, Injective (I.cocomplex.X n) := fun n => I.injective n
  have hbase : CechTrivOnBasic X (syz I.cocomplex 0) :=
    CechTrivOnBasic.of_iso (X := X)
      (syz_zero_iso Z I.cocomplex I.ι).some hZ
  have hInv := cechTrivOnBasic_syz_and_lift X I.cocomplex hex hKinj hbase
  -- the surjectivity of `syzProj` over `⊤` gives the acyclicity of the resolution
  have hKH : ∀ k : ℕ, 0 < k → IsZero
      (HomologicalComplex.homology
        (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) k) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine isZero_homology_mapHomologicalComplex_of_epi_map_syzProj
      (D := ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens)))) I.cocomplex
      (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))) j ?_
    rw [ModuleCat.epi_iff_surjective]
    intro y
    have hone : X.basicOpen (1 : X.presheaf.obj (Opposite.op (⊤ : X.Opens))) = ⊤ :=
      Scheme.basicOpen_one (X := X) (U := ⊤)
    have hsurj := (hInv j).2 1
    have hsurj_top : ∀ y : sectionsAt (syz I.cocomplex (j + 1)) (⊤ : X.Opens),
        ∃ x : sectionsAt (I.cocomplex.X j) (⊤ : X.Opens),
          sectionsMap (syzProj I.cocomplex j) (⊤ : X.Opens) x = y := hone ▸ hsurj
    obtain ⟨x, hx⟩ := hsurj_top y
    exact ⟨x, hx⟩
  -- acyclicity of the terms
  have hK : ∀ n k : ℕ, 0 < k → IsZero
      (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerived k).obj
        (I.cocomplex.X n)) := by
    intro n k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    haveI : Injective (I.cocomplex.X n) := I.injective n
    exact Functor.isZero_rightDerived_obj_injective_succ
      (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))) m (I.cocomplex.X n)
  exact rightDerived_isZero_of_acyclic_resolution
    (D := ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))
    (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens)))
    Z I.cocomplex I.ι hK hKH

end Work.DSEQ0
