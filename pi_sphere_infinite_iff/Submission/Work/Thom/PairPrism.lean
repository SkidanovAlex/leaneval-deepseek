import Mathlib
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Thom.RelPairHomotopy
import Submission.Work.Thom.SSetChainHomotopyNaturality
import Submission.Work.Thom.ToSSetHomotopyRestriction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped unitInterval
open CategoryTheory MonoidalCategory Simplicial SimplicialObject Opposite

/-!
# The prism operator of a homotopy of pairs

For a homotopy `H` of continuous maps the prism operator on singular chains carries the chains of a
subspace into the chains of the subspace, and its transpose (the transposed prism operator) is a
cochain homotopy between the pullbacks of the two maps which preserves the relative cochains.  This
module develops these two facts, together with the descent of a homotopy of pairs to the relative
cochain complexes and the compatibility of the pair map with the inclusion of the relative complex.
-/

namespace Work.Thom

noncomputable section

/-- **The pair map is compatible with the inclusion of the relative cochain complex**. -/
lemma relIncl_dualChainMap {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h : ∀ x ∈ A₁, f x ∈ A₂) (R : Type) [CommRing R] :
    Work.Cohomology.relIncl R X₂ A₂ ≫ Work.Cohomology.dualChainMap R X₁ X₂ f
      = Work.Cohomology.relComplexMap R A₁ A₂ f h ≫ Work.Cohomology.relIncl R X₁ A₁ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Work.Cohomology.relComplexMap_f,
    Work.Cohomology.relIncl_f, Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact (Work.Cohomology.relMapLM_coe R A₁ A₂ f h n x).symm

/-- The componentwise compatibility of the pair map with the inclusion of the relative cochain
complex. -/
lemma relIncl_dualChainMap_apply {X Y : TopCat.{0}} (A : Set X) (B : Set Y) {f : X ⟶ Y}
    (hf : ∀ x ∈ A, f x ∈ B) (R : Type) [CommRing R] (i : ℕ) :
    (Work.Cohomology.relIncl R Y B).f i
        ≫ (Work.Cohomology.dualChainMap R X Y f).f i
      = (Work.Cohomology.relComplexMap R A B f hf).f i
        ≫ (Work.Cohomology.relIncl R X A).f i :=
  congrArg (fun m => m.f i) (relIncl_dualChainMap A B f hf R)

/-- **The prism operator of a homotopy carries chains of the subspace into the chains of the
subspace.** -/
lemma prism_preserves {X Y : TopCat} {A : Set X} {B : Set Y} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) (R : Type) [CommRing R] (m : ℕ) :
    ((restrHomotopyTop H hf hg hH).toSSet.chainComplexMap (ModuleCat.of R R)).hom m (m+1)
        ≫ (Work.Cohomology.chainMap R (TopCat.of ↥B) Y
            (Work.Cohomology.subtypeIncl Y B)).f (m+1)
      = (Work.Cohomology.chainMap R (TopCat.of ↥A) X
          (Work.Cohomology.subtypeIncl X A)).f m
        ≫ (H.toSSet.chainComplexMap (ModuleCat.of R R)).hom m (m+1) := by
  have hvu : (restrHomotopyTop H hf hg hH).toSSet.h
      ≫ TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y B)
      = (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A) ▷ Δ[1])
        ≫ H.toSSet.h :=
    ToSSetHomotopyRestriction H (restrHomotopyTop H hf hg hH)
      (Work.Cohomology.subtypeIncl X A) (Work.Cohomology.subtypeIncl Y B)
      (restrHomotopy_h H hf hg hH)
  exact SSetChainHomotopyNaturality (restrHomotopyTop H hf hg hH).toSSet H.toSSet
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
    (TopCat.toSSet.map (Work.Cohomology.subtypeIncl Y B)) R hvu m

/-- **The transposed prism operator preserves the relative cochains.** -/
lemma dualHom_prism_mem {R : Type} [CommRing R] {X Y : TopCat} {A : Set X} {B : Set Y}
    {f g : X ⟶ Y}
    {S : Homotopy (Work.Cohomology.chainMap R X Y f) (Work.Cohomology.chainMap R X Y g)}
    (hyp : ∀ (m : ℕ) (c : (Work.Cohomology.singularChains R (TopCat.of ↥A)).X m),
      ∃ y : (Work.Cohomology.singularChains R (TopCat.of ↥B)).X (m+1),
        S.hom m (m+1)
            ((Work.Cohomology.chainMap R (TopCat.of ↥A) X
              (Work.Cohomology.subtypeIncl X A)).f m c)
          = (Work.Cohomology.chainMap R (TopCat.of ↥B) Y
              (Work.Cohomology.subtypeIncl Y B)).f (m+1) y)
    (i j : ℕ) (φ : Work.Cohomology.relKern R Y B i) :
    (Work.Cohomology.dualHom R (S.hom j i)).hom φ.1 ∈ Work.Cohomology.relKern R X A j := by
  rw [Work.Cohomology.relKern, LinearMap.mem_ker]
  apply LinearMap.ext
  intro c
  change (show (Work.Cohomology.singularChains R (TopCat.of ↥A)).X j →ₗ[R] R from
        ((Work.Cohomology.restr R X A).f j).hom
          ((Work.Cohomology.dualHom R (S.hom j i)).hom φ.1)) c = 0
  have hL : (show (Work.Cohomology.singularChains R (TopCat.of ↥A)).X j →ₗ[R] R from
        ((Work.Cohomology.restr R X A).f j).hom
          ((Work.Cohomology.dualHom R (S.hom j i)).hom φ.1)) c
      = (show (Work.Cohomology.singularChains R (TopCat.of ↥Y)).X i →ₗ[R] R from φ.1)
        ((S.hom j i).hom
          (((Work.Cohomology.chainMap R (TopCat.of ↥A) X
            (Work.Cohomology.subtypeIncl X A)).f j).hom c)) := by
    rw [Work.Cohomology.restr, Work.Cohomology.dualChainMap_f_hom,
      Work.Cohomology.dualHom_hom_apply]
    erw [LinearMap.dualMap_apply]
  rw [hL]
  by_cases hij : j + 1 = i
  · obtain rfl : i = j + 1 := hij.symm
    obtain ⟨y, hy⟩ := hyp j c
    rw [hy]
    have h : ((Work.Cohomology.restr R Y B).f (j+1)).hom φ.1 = 0 :=
      LinearMap.mem_ker.mp φ.2
    have h2 := congrArg (fun l =>
      (show (Work.Cohomology.singularChains R (TopCat.of ↥B)).X (j+1) →ₗ[R] R from l) y) h
    rw [Work.Cohomology.restr, Work.Cohomology.dualChainMap_f_hom] at h2
    erw [LinearMap.dualMap_apply] at h2
    simpa using h2
  · have hzero : S.hom j i = 0 := S.zero j i (by
      rw [ComplexShape.down_Rel]; omega)
    rw [hzero]
    simp

/-- The existence form of the preservation of the subspace by the prism operator. -/
lemma prism_hyp {X Y : TopCat.{0}} (A : Set X) (B : Set Y) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) (R : Type) [CommRing R] (m : ℕ)
    (c : (Work.Cohomology.singularChains R (TopCat.of ↥A)).X m) :
    ∃ y : (Work.Cohomology.singularChains R (TopCat.of ↥B)).X (m+1),
      (H.toSSet.chainComplexMap (ModuleCat.of R R)).hom m (m+1)
          ((Work.Cohomology.chainMap R (TopCat.of ↥A) X
            (Work.Cohomology.subtypeIncl X A)).f m c)
        = (Work.Cohomology.chainMap R (TopCat.of ↥B) Y
            (Work.Cohomology.subtypeIncl Y B)).f (m+1) y := by
  have h := prism_preserves H hf hg hH R m
  refine ⟨((restrHomotopyTop H hf hg hH).toSSet.chainComplexMap
    (ModuleCat.of R R)).hom m (m+1) c, ?_⟩
  have h' := congrArg (fun (u : (Work.Cohomology.singularChains R (TopCat.of ↥A)).X m ⟶
      (Work.Cohomology.singularChains R Y).X (m+1)) => u.hom c) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  exact h'.symm

/-- **The transposed prism operator preserves the relative cochains.** -/
lemma relKern_prism_mem {X Y : TopCat.{0}} (A : Set X) (B : Set Y) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) (R : Type) [CommRing R]
    (i j : ℕ) (φ : Work.Cohomology.relKern R Y B i) :
    (Work.Cohomology.dualHom R
      ((H.toSSet.chainComplexMap (ModuleCat.of R R)).hom j i)).hom φ.1
      ∈ Work.Cohomology.relKern R X A j :=
  dualHom_prism_mem (X := X) (Y := Y) (f := f) (g := g)
    (S := H.toSSet.chainComplexMap (ModuleCat.of R R))
    (fun m c => prism_hyp A B H hf hg hH R m c) i j φ

/-- **The transposed prism operator** of a homotopy `H` of maps of pairs, as a cochain homotopy
between the duals of the induced maps on singular chains. -/
def transposed_prism {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (R : Type) [CommRing R] :
    Homotopy (Work.Cohomology.dualChainMap R X Y f) (Work.Cohomology.dualChainMap R X Y g) :=
  Work.Cohomology.dualHomotopy R (H.toSSet.chainComplexMap (ModuleCat.of R R)).symm

/-- The components of the transposed prism operator, evaluated: they are the transposes of the
components of the prism operator of `H`. -/
lemma transposed_prism_apply {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g)
    (R : Type) [CommRing R] (i j : ℕ) (ψ : Work.Cohomology.dualChains R Y i)
    (c : (Work.Cohomology.singularChains R X).X j) :
    (show (Work.Cohomology.singularChains R X).X j →ₗ[R] R from
        ((transposed_prism H R).hom i j).hom ψ) c
      = (show (Work.Cohomology.singularChains R Y).X i →ₗ[R] R from ψ)
          ((H.toSSet.chainComplexMap (ModuleCat.of R R)).hom j i c) := by
  rw [transposed_prism]
  simp only [Work.Cohomology.dualHomotopy, Work.Cohomology.dualHomotopyHom,
    Homotopy.symm_hom, Pi.neg_apply, Work.Cohomology.dualHom_neg, neg_neg,
    Work.Cohomology.dualHom_hom_apply, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  rfl

/-- **Descent of a homotopy to the relative cochains** (componentwise hypotheses). -/
theorem HomologyMapOfRestriction' {R : Type} [CommRing R]
    {C D C' D' : CochainComplex (ModuleCat R) ℕ} (ι : C ⟶ C') (κ : D ⟶ D')
    (hκ : ∀ n, Function.Injective (κ.f n).hom)
    {α β : C ⟶ D} {φ ψ : C' ⟶ D'}
    (hα : ∀ i, ι.f i ≫ φ.f i = α.f i ≫ κ.f i)
    (hβ : ∀ i, ι.f i ≫ ψ.f i = β.f i ≫ κ.f i)
    (H : Homotopy φ ψ) (k : ∀ i j, C.X i ⟶ D.X j)
    (hk : ∀ i j, ι.f i ≫ H.hom i j = k i j ≫ κ.f j) (n : ℕ) :
    HomologicalComplex.homologyMap α n = HomologicalComplex.homologyMap β n := by
  have key : Homotopy α β :=
    { hom := k
      zero := fun i j hij => by
        have hH : H.hom i j = 0 := H.zero i j hij
        have hkj : k i j ≫ κ.f j = 0 := by
          have hh := hk i j
          rw [hH] at hh
          simpa using hh.symm
        have : Mono (κ.f j) := (ModuleCat.mono_iff_injective _).mpr (hκ j)
        rw [← cancel_mono (κ.f j)]
        simpa using hkj
      comm := fun i => by
        have h1 : ι.f i ≫ φ.f i = α.f i ≫ κ.f i := hα i
        have hψ : ι.f i ≫ ψ.f i = β.f i ≫ κ.f i := hβ i
        have hfun : (fun i j => ι.f i ≫ H.hom i j) = (fun i j => k i j ≫ κ.f j) := by
          funext i j; exact hk i j
        have hA : ι.f i ≫ dNext i H.hom = dNext i k ≫ κ.f i := by
          rw [← dNext_comp_left ι H.hom i, hfun, dNext_comp_right k κ i]
        have hB : ι.f i ≫ prevD i H.hom = prevD i k ≫ κ.f i := by
          rw [← prevD_comp_left ι H.hom i, hfun, prevD_comp_right k κ i]
        have : Mono (κ.f i) := (ModuleCat.mono_iff_injective _).mpr (hκ i)
        rw [← cancel_mono (κ.f i)]
        rw [← h1, H.comm i]
        simp only [Preadditive.comp_add, Preadditive.add_comp, hA, hB, hψ] }
  exact Homotopy.homologyMap_eq key n

/-- the lift exists -/
lemma RelativeLiftExists {X Y : TopCat.{0}} (A : Set X) (B : Set Y) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x ∈ A, f x ∈ B) (hg : ∀ x ∈ A, g x ∈ B)
    (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) (R : Type) [CommRing R] :
    ∃ k : ∀ i j, (Work.Cohomology.relComplex R Y B).X i
        ⟶ (Work.Cohomology.relComplex R X A).X j,
      ∀ i j, (Work.Cohomology.relIncl R Y B).f i ≫ (transposed_prism H R).hom i j
        = k i j ≫ (Work.Cohomology.relIncl R X A).f j := by
  refine ⟨fun i j => ModuleCat.ofHom
      (((Work.Cohomology.dualHom R
          ((H.toSSet.chainComplexMap (ModuleCat.of R R)).hom j i)).hom.comp
          (Submodule.subtype (Work.Cohomology.relKern R Y B i))).codRestrict
        (Work.Cohomology.relKern R X A j)
        (fun φ => relKern_prism_mem A B H hf hg hH R i j φ)), ?_⟩
  intro i j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  have h1 : (show (Work.Cohomology.singularChains R X).X j →ₗ[R] R from
      (((Work.Cohomology.relIncl R Y B).f i ≫
        (transposed_prism H R).hom i j).hom φ)) c
      = (show (Work.Cohomology.singularChains R Y).X i →ₗ[R] R from φ.1)
          ((H.toSSet.chainComplexMap (ModuleCat.of R R)).hom j i c) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, Work.Cohomology.relIncl_f,
      ModuleCat.hom_ofHom]
    exact transposed_prism_apply H R i j φ.1 c
  rw [h1]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Work.Cohomology.relIncl_f,
    ModuleCat.hom_ofHom, Submodule.subtype_apply, LinearMap.codRestrict_apply,
    Work.Cohomology.dualHom_hom_apply]
  rfl

end

end Work.Thom
