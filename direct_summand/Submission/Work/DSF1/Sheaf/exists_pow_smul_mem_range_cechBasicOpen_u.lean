import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.structPresheaf_isLocalization_map
import Submission.Work.DSF1.Sheaf.cech_map_clearing
import Submission.Work.DSF1.Sheaf.exists_pow_smul_mem_range_cechBasicOpen
import Submission.Work.DSF1.Sheaf.pi_map_clearing_surj
import Submission.Work.DSF1.Sheaf.pi_map_clearing_ker
import Submission.Work.DSF1.Cech.UnitCase
import Submission.Work.DSF1.Cech.isIsoDeletion_Qo
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Sheaf.isAffineOpen_Eobj_of

/-!
# Čech cocycles of the structure sheaf of an affine scheme are killed by a power of `f i`

This is the universe-polymorphic version of
`Work.DSF1.Sheaf.exists_pow_smul_mem_range_cechBasicOpen`: for an affine scheme `X` and a
finite family `f : ι → Γ(X, ⊤)`, every cocycle `s` in degree `n + 1` of the Čech complex of
the structure sheaf of `X` along the basic opens `D (f i)` becomes a coboundary after
multiplication by a power of `f i`.

The proof is the one of the monomorphic statement, with the two auxiliary results it needs
(the finite-product clearing lemma `Work.DSF1.Sheaf.cech_map_clearing` and the component
formula `cechMap_component`) restated at an arbitrary universe level, since the originals
were elaborated with the universe of `Scheme` pinned to `0`:

* `powSmulClearU_piSurj`, `powSmulClearU_piKer`: clearing denominators on a finite product,
* `powSmulClearU_cechMapComponent`: the degree-`n` component of the map of Čech complexes
  induced by `ηO` is the product of its components,
* `powSmulClearU_cechMapClearing`: assembling the componentwise clearing to the terms of
  the Čech complexes.

Everything else used below (`structPresheaf_isLocalization_map`,
`Work.DSF1.Cech.isIsoDeletion_Qo`, `Work.DSF1.Cech.UnitCase`,
`Work.DSF1.Cech.isAffineOpen_Eobj_of`) is already universe-polymorphic.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

/-! ### Clearing denominators on a finite product -/

/-- Universe-polymorphic form of `Work.DSF1.Sheaf.pi_map_clearing_surj`. -/
lemma powSmulClearU_piSurj {R : Type u} [CommRing R] {β : Type u} [Fintype β]
    (F F' : β → ModuleCat R) (φ : ∀ b, F b ⟶ F' b) (h : R)
    (hcomp : ∀ b (z : ↥(F' b)), ∃ (k : ℕ) (t : ↥(F b)), (φ b).hom t = h ^ k • z) :
    ∀ z : ↥(∏ᶜ F'), ∃ (k : ℕ) (t : ↥(∏ᶜ F)),
      (CategoryTheory.Limits.Pi.map φ).hom t = h ^ k • z := by
  classical
  intro z
  have hcomp' : ∀ b, ∃ (k : ℕ) (t : ↥(F b)),
      (φ b).hom t = h ^ k • (Pi.π F' b).hom z :=
    fun b => hcomp b ((Pi.π F' b).hom z)
  choose k s hs using hcomp'
  have hK : ∀ b, k b ≤ ∑ y, k y := fun b =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ b)
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi F).inv.hom
    (fun b => h ^ ((∑ y, k y) - k b) • s b), ?_⟩
  have hkey : ∀ b, (Pi.π F' b).hom
      ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
        (fun b => h ^ ((∑ y, k y) - k b) • s b)))
      = (Pi.π F' b).hom (h ^ (∑ y, k y) • z) := by
    intro b
    have hstep : (Pi.π F' b).hom
        ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
          (fun b => h ^ ((∑ y, k y) - k b) • s b)))
        = (φ b).hom ((Pi.π F b).hom ((ModuleCat.piIsoPi F).inv.hom
          (fun b => h ^ ((∑ y, k y) - k b) • s b))) := by
      have hh := LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom (Limits.Pi.map_π φ b))
        ((ModuleCat.piIsoPi F).inv.hom (fun b => h ^ ((∑ y, k y) - k b) • s b))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      exact hh
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hs b, smul_smul, ← pow_add, Nat.sub_add_cancel (hK b)]
    exact (map_smul (Pi.π F' b).hom (h ^ (∑ y, k y)) z).symm
  have h1 : (ModuleCat.piIsoPi F').hom.hom
      ((CategoryTheory.Limits.Pi.map φ).hom ((ModuleCat.piIsoPi F).inv.hom
        (fun b => h ^ ((∑ y, k y) - k b) • s b)))
      = (ModuleCat.piIsoPi F').hom.hom (h ^ (∑ y, k y) • z) := by
    funext b
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey b
  have h2 := congrArg (ModuleCat.piIsoPi F').inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

/-- Universe-polymorphic form of `Work.DSF1.Sheaf.pi_map_clearing_ker`. -/
lemma powSmulClearU_piKer {R : Type u} [CommRing R] {β : Type u} [Fintype β]
    (F F' : β → ModuleCat R) (φ : ∀ b, F b ⟶ F' b) (h : R)
    (hcomp : ∀ b (t : ↥(F b)), (φ b).hom t = 0 → ∃ k : ℕ, h ^ k • t = 0) :
    ∀ t : ↥(∏ᶜ F), (CategoryTheory.Limits.Pi.map φ).hom t = 0 →
      ∃ k : ℕ, h ^ k • t = 0 := by
  intro t ht
  have key : ∀ b, (φ b).hom ((CategoryTheory.Limits.Pi.π F b).hom t) = 0 := by
    intro b
    have h1 := CategoryTheory.Limits.Pi.map_π φ b
    have h2 := congrArg (fun (f : ∏ᶜ F ⟶ F' b) => f.hom t) h1
    simp only [ConcreteCategory.comp_apply] at h2
    rw [ht, map_zero] at h2
    exact h2.symm
  have ex : ∀ b, ∃ k : ℕ, h ^ k • ((CategoryTheory.Limits.Pi.π F b).hom t) = 0 :=
    fun b => hcomp b _ (key b)
  choose k hk using ex
  refine ⟨∑ b, k b, ?_⟩
  have hle : ∀ b, k b ≤ ∑ b, k b := by
    intro b
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ b)
  have hzero : ∀ b, (CategoryTheory.Limits.Pi.π F b).hom (h ^ (∑ b, k b) • t) = 0 := by
    intro b
    rw [LinearMap.map_smul]
    rw [← Nat.sub_add_cancel (hle b), pow_add, mul_smul, hk b, smul_zero]
  have hfinal : h ^ (∑ b, k b) • t = 0 := by
    apply CategoryTheory.Limits.Concrete.Pi.map_ext (F := 𝟭 (ModuleCat R)) (f := F)
    intro i
    simp only [Functor.id_map]
    change (CategoryTheory.Limits.Pi.π F i).hom ((h ^ ∑ b, k b) • t) =
      (CategoryTheory.Limits.Pi.π F i).hom (0 : ↥(∏ᶜ F))
    rw [hzero i, map_zero]
  exact hfinal

/-! ### Clearing denominators for the comparison map of Čech complexes -/

/-- Universe-polymorphic form of the component formula for the map of Čech complexes
induced by `ηO`. -/
lemma powSmulClearU_cechMapComponent {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    [Fintype ι] (U : ι → X.Opens) (V : X.Opens) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I)) :
    ((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n ≫
        CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x
      = CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Sheaf.structPresheaf X).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x ≫
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
          (Opposite.op (Work.DSF1.Cech.Eobj U n x)) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor, Functor.comp_map,
    AlgebraicTopology.alternatingCofaceMapComplex_map,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  rw [CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor_map_app]
  exact CategoryTheory.Limits.Pi.map_π _ x

/-- Universe-polymorphic form of `Work.DSF1.Sheaf.cech_map_clearing`: the comparison map of
Čech complexes `Č(ηO)` clears denominators, provided it does so componentwise on the opens
of the Čech nerve. -/
theorem powSmulClearU_cechMapClearing {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    [Fintype ι]
    (U : ι → X.Opens) (V : X.Opens) (h : ↥(X.presheaf.obj (Opposite.op ⊤)))
    (hsurj : ∀ (n : ℕ) (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I),
      ∀ z : (Work.DSF1.Sheaf.structPresheaf X).obj
          (Opposite.op (Work.DSF1.Cech.Eobj U n x ⊓ V)),
        ∃ (k : ℕ) (t : (Work.DSF1.Sheaf.structPresheaf X).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
          ((Work.DSF1.Sheaf.structPresheaf X).map (CategoryTheory.homOfLE (inf_le_left :
            Work.DSF1.Cech.Eobj U n x ⊓ V ≤ Work.DSF1.Cech.Eobj U n x)).op).hom t = h ^ k • z)
    (hker : ∀ (n : ℕ) (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I)
        (t : (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
      ((Work.DSF1.Sheaf.structPresheaf X).map (CategoryTheory.homOfLE (inf_le_left :
        Work.DSF1.Cech.Eobj U n x ⊓ V ≤ Work.DSF1.Cech.Eobj U n x)).op).hom t = 0 →
        ∃ k : ℕ, h ^ k • t = 0) :
    (∀ (n : ℕ) (z : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n),
      ∃ (k : ℕ) (t : ((CategoryTheory.cechComplexFunctor U).obj
          (Work.DSF1.Sheaf.structPresheaf X)).X n),
        (((CategoryTheory.cechComplexFunctor U).map
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n).hom t = h ^ k • z) ∧
    (∀ (n : ℕ) (t : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.structPresheaf X)).X n),
      (((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n).hom t = 0 →
        ∃ k : ℕ, h ^ k • t = 0) := by
  classical
  have key : ∀ (n : ℕ),
      ((CategoryTheory.cechComplexFunctor U).map
        (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V)).f n =
      CategoryTheory.Limits.Pi.map
        (fun x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) =>
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))) := by
    intro n
    apply CategoryTheory.Limits.Pi.hom_ext
    intro x
    have h2 : CategoryTheory.Limits.Pi.map
        (fun x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) =>
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))) ≫
        CategoryTheory.Limits.Pi.π
          (fun y => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x
        = CategoryTheory.Limits.Pi.π
            (fun y => (Work.DSF1.Sheaf.structPresheaf X).obj
              (Opposite.op (Work.DSF1.Cech.Eobj U n y))) x ≫
          (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
            (Opposite.op (Work.DSF1.Cech.Eobj U n x)) := by
      exact CategoryTheory.Limits.Pi.map_π _ x
    exact (powSmulClearU_cechMapComponent U V n x).trans h2.symm
  constructor
  · intro n z
    haveI : Fintype ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :=
      inferInstanceAs (Fintype (Fin (n + 1) → ι))
    obtain ⟨k, t, ht⟩ := powSmulClearU_piSurj
      (fun x => (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      h (fun x zx => hsurj n x zx) z
    refine ⟨k, t, ?_⟩
    exact (congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj
      (Work.DSF1.Sheaf.structPresheaf X)).X n ⟶ ((CategoryTheory.cechComplexFunctor U).obj
      (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n) => m.hom t) (key n)).trans ht
  · intro n t ht
    haveI : Fintype ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I) :=
      inferInstanceAs (Fintype (Fin (n + 1) → ι))
    exact powSmulClearU_piKer
      (fun x => (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      (fun x => (Work.DSF1.Cech.etaO (Work.DSF1.Sheaf.structPresheaf X) V).app
        (Opposite.op (Work.DSF1.Cech.Eobj U n x)))
      h (fun x tx => hker n x tx) t
      ((congrArg (fun (m : ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Sheaf.structPresheaf X)).X n ⟶ ((CategoryTheory.cechComplexFunctor U).obj
        (Work.DSF1.Cech.Qo (Work.DSF1.Sheaf.structPresheaf X) V)).X n) => m.hom t) (key n)).symm.trans ht)

/-! ### The main statement -/

theorem exists_pow_smul_mem_range_cechBasicOpen_u {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffine X] {ι : Type u} [Fintype ι]
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
    powSmulClearU_cechMapClearing (basicOpenFamily X f) (X.basicOpen (f i)) (f i)
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
  set K : CochainComplex (ModuleCat.{u} ↥(X.presheaf.obj (Opposite.op ⊤))) ℕ :=
    (cechComplexFunctor (basicOpenFamily X f)).obj (structPresheaf X) with hK
  set K' : CochainComplex (ModuleCat.{u} ↥(X.presheaf.obj (Opposite.op ⊤))) ℕ :=
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
