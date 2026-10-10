import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.cochainsMap_inhomogeneousCochainsIso_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary material for `Work.SSGRoute.eCoh_delta`

The isomorphism `SSGRoute.PTExt.eCoh n G A : Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)` is the composite of

* `theta n G A`: the isomorphism `Hⁿ(G, A) ≃+ Hⁿ(Hom(barResolution, A))` coming from
  `groupCohomologyIso` at the bar resolution, and
* `eCohPsi n G A`: the *chosen* isomorphism `Hⁿ(Hom(barResolution, A)) ≃+ Extⁿ_G(ℤ, A)` of
  `Work.SSGRoute.projRes_homologyAddEquiv_extMk`.

Here we record these two pieces, the specification of `eCohPsi` on the class of a cocycle, the
identification of `theta` with the map induced by the chain map `inhomogeneousCochainsIso`, and the
resulting evaluation of `eCoh` on the class of an inhomogeneous cocycle.
-/

namespace Work.SSGRoute

open CategoryTheory Limits SSGRoute.PTExt

noncomputable section

/-- The chosen `Ext`-side half of `SSGRoute.PTExt.eCoh`. -/
def eCohPsi (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).homology n ≃+ extH A n :=
  Classical.choose (Work.SSGRoute.projRes_homologyAddEquiv_extMk (X := unitRep G) (Y := A)
      (Rep.barResolution Coeff G) n)

/-- **The specification of `eCohPsi`**: on the class of a cocycle `f` it is
`ProjectiveResolution.extMk f`. -/
lemma eCohPsi_spec (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (f : (Rep.barResolution Coeff G).complex.X n ⟶ A)
    (hf : (Rep.barResolution Coeff G).complex.d (n + 1) n ≫ f = 0) :
    eCohPsi n G A
        (((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).homologyπ n
          (((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).cyclesMk f (n + 1) (by simp)
            (by
              change (Rep.barResolution Coeff G).complex.d (n + 1) n ≫ f = 0
              exact hf))) =
      (Rep.barResolution Coeff G).extMk f (n + 1) rfl hf :=
  Classical.choose_spec (Work.SSGRoute.projRes_homologyAddEquiv_extMk (X := unitRep G) (Y := A)
      (Rep.barResolution Coeff G) n) f hf

/-- The `Hⁿ(G, -)`-side half of `SSGRoute.PTExt.eCoh`. -/
def theta (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    groupCohomology A n ≃+
      ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).homology n :=
  (groupCohomologyIso A n (Rep.barResolution Coeff G)).toLinearEquiv.toAddEquiv

/-- `eCoh` is the composite of `theta` and `eCohPsi`. -/
lemma eCoh_eq (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    eCoh n G A = (theta n G A).trans (eCohPsi n G A) := rfl

/-- The same map `Hⁿ(G, A) ≃+ Hⁿ(Hom(barComplex, A))`, written directly through the chain map
`inhomogeneousCochainsIso`. -/
def thetaHom_eda (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    groupCohomology A n ≃+
      ((Rep.barResolution Coeff G).complex.linearYonedaObj Coeff A).homology n :=
  ((HomologicalComplex.homologyMapIso (groupCohomology.inhomogeneousCochainsIso A) n).toLinearEquiv).toAddEquiv

set_option backward.isDefEq.respectTransparency false in
/-- `groupCohomologyIso` at the bar resolution is the map induced by the chain iso
`inhomogeneousCochainsIso`. -/
lemma groupCohomologyIso_hom_eq (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    (groupCohomologyIso A n (Rep.barResolution Coeff G)).hom =
      (HomologicalComplex.homologyMapIso (groupCohomology.inhomogeneousCochainsIso A) n).hom := by
  rw [groupCohomologyIso, groupCohomologyIsoExt, Rep.barResolution.extIso,
    ProjectiveResolution.isoExt]
  simp only [HomologicalComplex.homologyMapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- `theta` is the map induced by the chain map `inhomogeneousCochainsIso`. -/
lemma theta_eq_thetaHom (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    theta n G A = thetaHom_eda n G A := by
  apply AddEquiv.ext
  intro x
  exact ConcreteCategory.congr_hom (groupCohomologyIso_hom_eq n G A) x

/-- `thetaHom_eda` evaluated through `homologyMap`. -/
lemma thetaHom_apply (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (x : groupCohomology A n) :
    thetaHom_eda n G A x =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n x := rfl

/-- The morphism `(barComplex).X n ⟶ A` associated to an inhomogeneous `n`-cochain. -/
def cochainToHom (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) (z : (Fin n → G) → A) :
    (Rep.barComplex Coeff G).X n ⟶ A :=
  Rep.freeLift Coeff G A z

/-- A cocycle `z` gives a cocycle `cochainToHom z` for the bar resolution. -/
lemma cochainToHom_cocycle (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : (Fin n → G) → A)
    (hz : ConcreteCategory.hom (inhomogeneousCochains.d A n) z = 0) :
    (Rep.barComplex Coeff G).d (n + 1) n ≫ cochainToHom n G A z = 0 := by
  change (Rep.barComplex Coeff G).d (n + 1) n ≫
    (groupCohomology.inhomogeneousCochainsIso A).hom.f n z = 0
  have hcomm := (groupCohomology.inhomogeneousCochainsIso A).hom.comm n (n + 1)
  have h := ConcreteCategory.congr_hom hcomm z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  have hz' : (groupCohomology.inhomogeneousCochains A).d n (n + 1) z = 0 := by
    rw [groupCohomology.inhomogeneousCochains.d_def]
    exact hz
  rw [hz', map_zero] at h
  rw [linearYonedaObj_d_apply (Rep.barComplex Coeff G) A (by simp)
    ((groupCohomology.inhomogeneousCochainsIso A).hom.f n z)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **Evaluation of `eCoh` on the class of an inhomogeneous cocycle.** -/
lemma eCoh_cocycle (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : (Fin n → G) → A)
    (hz : ConcreteCategory.hom (inhomogeneousCochains.d A n) z = 0) :
    eCoh n G A (groupCohomology.π A n (groupCohomology.cocyclesMk z hz)) =
      (Rep.barResolution Coeff G).extMk (cochainToHom n G A z) (n + 1) rfl
        (cochainToHom_cocycle n G A z hz) := by
  rw [eCoh_eq, AddEquiv.trans_apply, theta_eq_thetaHom, thetaHom_apply]
  have hnat := HomologicalComplex.homologyπ_naturality
    (groupCohomology.inhomogeneousCochainsIso A).hom n
  have hval : HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).hom n
      (groupCohomology.π A n (groupCohomology.cocyclesMk z hz)) =
      ((Rep.barComplex Coeff G).linearYonedaObj Coeff A).homologyπ n
        (HomologicalComplex.cyclesMap (groupCohomology.inhomogeneousCochainsIso A).hom n
          (groupCohomology.cocyclesMk z hz)) := by
    have h := ConcreteCategory.congr_hom hnat (groupCohomology.cocyclesMk z hz)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  rw [hval]
  have hcyc : HomologicalComplex.cyclesMap (groupCohomology.inhomogeneousCochainsIso A).hom n
      (groupCohomology.cocyclesMk z hz) =
      (((Rep.barComplex Coeff G).linearYonedaObj Coeff A).cyclesMk (cochainToHom n G A z) (n + 1)
        (by simp) (by
          change (Rep.barComplex Coeff G).d (n + 1) n ≫ cochainToHom n G A z = 0
          exact cochainToHom_cocycle n G A z hz)) := by
    apply (ModuleCat.mono_iff_injective
      (((Rep.barComplex Coeff G).linearYonedaObj Coeff A).iCycles n)).1 inferInstance
    have h1 : (ConcreteCategory.hom
          (((Rep.barComplex Coeff G).linearYonedaObj Coeff A).iCycles n))
          ((ConcreteCategory.hom (HomologicalComplex.cyclesMap
            (groupCohomology.inhomogeneousCochainsIso A).hom n))
            (groupCohomology.cocyclesMk z hz))
        = (ConcreteCategory.hom ((groupCohomology.inhomogeneousCochainsIso A).hom.f n))
            ((ConcreteCategory.hom
              (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains A) n))
              (groupCohomology.cocyclesMk z hz)) := by
      have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
        (groupCohomology.inhomogeneousCochainsIso A).hom n) (groupCohomology.cocyclesMk z hz)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
      exact h
    rw [h1]
    have h2 : (ConcreteCategory.hom
        (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains A) n))
        (groupCohomology.cocyclesMk z hz) = z :=
      HomologicalComplex.i_cyclesMk (groupCohomology.inhomogeneousCochains A) z (n + 1) (by simp)
        (by simp [hz])
    rw [h2]
    have h3 : (ConcreteCategory.hom
        (HomologicalComplex.iCycles ((Rep.barComplex Coeff G).linearYonedaObj Coeff A) n))
        ((((Rep.barComplex Coeff G).linearYonedaObj Coeff A).cyclesMk (cochainToHom n G A z)
          (n + 1) (by simp) (by
            change (Rep.barComplex Coeff G).d (n + 1) n ≫ cochainToHom n G A z = 0
            exact cochainToHom_cocycle n G A z hz))) = cochainToHom n G A z :=
      HomologicalComplex.i_cyclesMk ((Rep.barComplex Coeff G).linearYonedaObj Coeff A)
        (cochainToHom n G A z) (n + 1) (by simp)
        (by
          change (Rep.barComplex Coeff G).d (n + 1) n ≫ cochainToHom n G A z = 0
          exact cochainToHom_cocycle n G A z hz)
    rw [h3]
    rfl
  rw [hcyc]
  exact eCohPsi_spec n G A (cochainToHom n G A z) (cochainToHom_cocycle n G A z hz)

/-- The value of `cochainToHom z` on the standard basis element. -/
lemma cochainToHom_apply (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : (Fin n → G) → A) (i : Fin n → G) :
    (cochainToHom n G A z).hom
        (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : Coeff))) = z i := by
  change ((Rep.freeLiftLEquiv Coeff G (Fin n → G) A).symm z).hom
      (Finsupp.single i (MonoidAlgebra.single (1 : G) (1 : Coeff))) = z i
  rw [Commons.RepresentationTheory.GroupCohomology.freeLiftLEquiv_symm_eq_freeLift]
  simp only [Rep.freeLift, Rep.hom_ofHom,
    Commons.RepresentationTheory.GroupCohomology.freeLift_apply_single_one]

/-- Naturality of `cochainToHom` in the coefficient module. -/
lemma cochainToHom_naturality (n : ℕ) (G : Type) [Group G] {A B : Rep.{0} Coeff G} (φ : A ⟶ B)
    (z : (Fin n → G) → A) :
    cochainToHom n G A z ≫ φ = cochainToHom n G B (fun g => φ (z g)) := by
  apply Rep.free_ext
  intro i
  rw [Rep.comp_apply]
  rw [cochainToHom_apply, cochainToHom_apply]

/-- `cochainToHom` commutes with the differentials. -/
lemma cochainToHom_d (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : (Fin n → G) → A) :
    (Rep.barComplex Coeff G).d (n + 1) n ≫ cochainToHom n G A z =
      cochainToHom (n + 1) G A ((groupCohomology.inhomogeneousCochains A).d n (n + 1) z) := by
  rw [← linearYonedaObj_d_apply (k := Coeff) (Rep.barComplex Coeff G) A (by simp) (cochainToHom n G A z)]
  have h := ConcreteCategory.congr_hom
    ((groupCohomology.inhomogeneousCochainsIso A).hom.comm n (n + 1)) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact h

/-- The `n`-cocycles of `A` are `cocyclesMk` of the underlying cochain. -/
lemma cocyclesMk_iCocycles (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (z : groupCohomology.cocycles A n) :
    ∃ h : ConcreteCategory.hom (inhomogeneousCochains.d A n)
        (⇑(groupCohomology.iCocycles A n) z) = 0,
      groupCohomology.cocyclesMk (⇑(groupCohomology.iCocycles A n) z) h = z := by
  have hker : ConcreteCategory.hom (inhomogeneousCochains.d A n)
      (⇑(groupCohomology.iCocycles A n) z) = 0 := by
    have h := ConcreteCategory.congr_hom
      (HomologicalComplex.iCycles_d (groupCohomology.inhomogeneousCochains A) n (n + 1)) z
    rw [ConcreteCategory.comp_apply] at h
    change (ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains A).d n (n + 1)))
      ((ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains A).iCycles n)) z) = 0 at h
    rw [groupCohomology.inhomogeneousCochains.d_def] at h
    exact h
  refine ⟨hker, ?_⟩
  apply (ModuleCat.mono_iff_injective
    ((groupCohomology.inhomogeneousCochains A).iCycles n)).1 inferInstance
  have h2 : (ConcreteCategory.hom
      (HomologicalComplex.iCycles (groupCohomology.inhomogeneousCochains A) n))
      (groupCohomology.cocyclesMk (⇑(groupCohomology.iCocycles A n) z) hker)
      = ⇑(groupCohomology.iCocycles A n) z :=
    HomologicalComplex.i_cyclesMk (groupCohomology.inhomogeneousCochains A) _ (n + 1) (by simp)
      (by simp [hker])
  rw [h2]

set_option backward.isDefEq.respectTransparency false in
/-- **Evaluation of `eCoh` on the connecting map** `δ` **of a short exact sequence.** -/
lemma eCoh_delta_cocycle (n : ℕ) (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact)
    (z : (Fin n → G) → S.X₃)
    (hz : ConcreteCategory.hom (inhomogeneousCochains.d S.X₃ n) z = 0)
    (y₂ : (Fin n → G) → S.X₂)
    (hy₂ : ConcreteCategory.hom ((groupCohomology.cochainsMap (MonoidHom.id G) S.g).f n) y₂ = z)
    (x : (Fin (n + 1) → G) → S.X₁)
    (hx : ⇑(Rep.Hom.hom S.f) ∘ x =
      ConcreteCategory.hom ((groupCohomology.inhomogeneousCochains S.X₂).d n (n + 1)) y₂)
    (hxc : ConcreteCategory.hom (inhomogeneousCochains.d S.X₁ (n + 1)) x = 0) :
    eCoh (n + 1) G S.X₁ (groupCohomology.δ hS n (n + 1) rfl
        (groupCohomology.π S.X₃ n (groupCohomology.cocyclesMk z hz))) =
      (Rep.barResolution Coeff G).extMk (cochainToHom (n + 1) G S.X₁ x) (n + 2) rfl
        (cochainToHom_cocycle (n + 1) G S.X₁ x hxc) := by
  rw [groupCohomology.δ_apply hS rfl z
    (by rw [groupCohomology.inhomogeneousCochains.d_def]; exact hz) y₂ hy₂ x hx]
  rw [eCoh_cocycle]

end

end Work.SSGRoute
