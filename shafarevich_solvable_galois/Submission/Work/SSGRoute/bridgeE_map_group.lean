import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.mapExtAddHom_extMk_univ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory Limits SSGRoute.PTExt

noncomputable section

/-! ## 1. `bridgeE` unfolded -/

lemma bridgeE_apply {G : Type} [Group G] (A : Rep.{0, 0, 0} Coeff G) (n : ℕ)
    (x : groupCohomology A n) :
    bridgeE G A n x =
      Bridge.Psi n G A
        (HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x) :=
  rfl

/-! ## 2. `bridgeE` on the class of an inhomogeneous cocycle -/

set_option backward.isDefEq.respectTransparency false in
lemma bridgeE_cocyclesMk {G : Type} [Group G] (A : Rep.{0, 0, 0} Coeff G) (n : ℕ)
    (z : (Fin n → G) → A) (hz : (inhomogeneousCochains.d A n) z = 0) :
    bridgeE G A n (groupCohomology.π A n (groupCohomology.cocyclesMk z hz)) =
      (Rep.barResolution Coeff G).extMk (Rep.freeLift Coeff G A z) (n + 1) rfl
        (freeLift_cocycle G A n z hz) := by
  rw [bridgeE_apply]
  unfold groupCohomology groupCohomology.π groupCohomology.cocycles groupCohomology.cocyclesMk
  have hstep : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n
      (HomologicalComplex.homologyπ (groupCohomology.inhomogeneousCochains A) n
        (HomologicalComplex.cyclesMk (groupCohomology.inhomogeneousCochains A) z (n + 1) (by simp)
          (by
            rw [groupCohomology.inhomogeneousCochains.d_def]
            exact hz))) =
      HomologicalComplex.homologyπ
          (((Rep.barResolution Coeff G).complex).linearYonedaObj Coeff A) n
        (HomologicalComplex.cyclesMk (((Rep.barResolution Coeff G).complex).linearYonedaObj Coeff A)
          (Rep.freeLift Coeff G A z) (n + 1) (by simp) (freeLift_cocycle G A n z hz)) :=
    homologyMap_homologyπ_cyclesMk (groupCohomology.inhomogeneousCochainsIso A).hom n z
      (by rw [groupCohomology.inhomogeneousCochains.d_def]; exact hz)
      (freeLift_cocycle G A n z hz)
  rw [hstep]
  exact Bridge.Psi_spec n G A (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz)

/-! ## 3. The `Ext`-level group change of `extMk`, from the exact-functor naturality. -/

theorem barChange_extMk_derived {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0, 0, 0} Coeff G) (n : ℕ)
    (g : (Rep.barComplex Coeff G).X n ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0)
    (hg' : (Rep.barComplex Coeff H).d (n + 1) n ≫
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) = 0) :
    (Abelian.Ext.mk₀ (unitRes f)).comp
      (((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg).mapExactFunctor (Rep.resFunctor f))
      (zero_add n)
    = (Rep.barResolution Coeff H).extMk
        (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) (n + 1) rfl hg' :=
  mapExtAddHom_extMk_univ (F := Rep.resFunctor f) (X := unitRep G) (Y := A)
    (R := Rep.barResolution Coeff G) (g := g) (hg := hg)
    (X' := unitRep H) (R' := Rep.barResolution Coeff H) (g' := unitRes f)
    (φ := barHom Coeff G H f) (hφ := barHom_augmentation Coeff G H f) (hg' := hg')

/-! ## 4. The `Ext` half with the identity coefficient map -/

set_option backward.isDefEq.respectTransparency false in
lemma extHMap_extMk_bar_id {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0, 0, 0} Coeff G) (n : ℕ) (g : Rep.free Coeff G (Fin n → G) ⟶ A)
    (hg : (Rep.barComplex Coeff G).d (n + 1) n ≫ g = 0)
    (hg' : (Rep.barComplex Coeff H).d (n + 1) n ≫
      (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) = 0) :
    extHMap f (𝟙 (Rep.res f A)) ((Rep.barResolution Coeff G).extMk g (n + 1) rfl hg) =
      (Rep.barResolution Coeff H).extMk
        (barChange Coeff G H f n ≫ (Rep.resFunctor f).map g) (n + 1) rfl hg' := by
  have h1 := barChange_extMk_derived f A n g hg hg'
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes]
  rw [Abelian.Ext.comp_mk₀_id]
  exact h1

/-! ## 5. The main theorem -/

set_option backward.isDefEq.respectTransparency false in
theorem bridgeE_map_group {G H : Type} [Group G] [Group H] (f : H →* G)
    (A : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff G) (n : ℕ) (x : groupCohomology A n) :
    Work.SSGRoute.bridgeE H (Rep.res f A) n
        ((groupCohomology.map f (CategoryTheory.CategoryStruct.id (Rep.res f A)) n).hom x) =
      SSGRoute.PTExt.extHMap f (CategoryTheory.CategoryStruct.id (Rep.res f A))
        (Work.SSGRoute.bridgeE G A n x) := by
  refine groupCohomology_induction_on x fun c => ?_
  obtain ⟨z, hz, rfl⟩ := exists_cocyclesMk n G A c
  rw [map_cocyclesMk n G H f A (Rep.res f A) (𝟙 (Rep.res f A)) z hz]
  simp only [ConcreteCategory.id_apply]
  rw [bridgeE_cocyclesMk (A := A) n z hz]
  rw [extHMap_extMk_bar_id f A n (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz)
    (barChange_cocycle' G H f A n (Rep.freeLift Coeff G A z) (freeLift_cocycle G A n z hz))]
  rw [bridgeE_cocyclesMk (A := Rep.res f A) n (fun y : Fin n → H => z (f ∘ y))
    (cochainsMap_cocycle G H f A (Rep.res f A) (𝟙 (Rep.res f A)) n z hz)]
  refine extMk_congr _ (?_ : Rep.freeLift Coeff H (Rep.res f A) (fun y : Fin n → H => z (f ∘ y)) =
      barChange Coeff G H f n ≫ (Rep.resFunctor f).map (Rep.freeLift Coeff G A z)) _ _
  simpa using freeLift_barChange G H f A (Rep.res f A) (𝟙 (Rep.res f A)) n z

end

end Work.SSGRoute
