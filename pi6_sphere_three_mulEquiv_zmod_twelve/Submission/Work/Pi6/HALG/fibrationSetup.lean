import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Serre.MapPathDefs
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.FGThm.mpathHomotopyEquiv
import Submission.Work.RatHurewicz.ConnectivityBridge
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# HALG: setting up the two Serre range sequences of the killing tower

This file contains the glue that the two "stage" arguments of area HALG need: the Serre range exact
sequences of the mapping-path-space fibrations `mpathQ g₄ : mpath g₄ → P₄` and
`mpathQ g₅ : mpath g₅ → P₅` of the Postnikov sections of the tower, transported back to the
homotopy fibres `Y = hofib g₄`, `Z = hofib g₅` and to the total spaces `E`, `Y` (the maps
`mpathFst g₄`, `mpathFst g₅` are homotopy equivalences, `Work.FGThm.mpathHomotopyEquiv`).

The resulting exact sequences are

`H_{i+1}(Y;R) → H_{i+1}(E;R) → H_{i+1}(P₄;R) → H_i(Y;R) → H_i(E;R)`   for `i + 1 < 9`, and
`H_{i+1}(Z;R) → H_{i+1}(Y;R) → H_{i+1}(P₅;R) → H_i(Z;R) → H_i(Y;R)`   for `i + 1 < 11`,

with middle maps `hmap R g₄ _` and `hmap R g₅ _`.  This is the point of the transport: on the
mapping path space the middle map is `hmap R (mpathQ g) _`, and `Work.Serre.mpath_homotopic`
together with functoriality identifies it with `hmap R (mpathFst g) _ ≫ hmap R g _`, whose first
factor is an isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

open Work.Pi6

/-! ## Functoriality of `hmap` -/

/-- `hmap R` sends identities to identities. -/
theorem hmap_id (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (i : ℕ) :
    hmap R (ContinuousMap.id X) i = 𝟙 (HR R X i) := by
  rw [Work.Pi6.hmap, Work.Cohomology.chainMap]
  rw [show (TopCat.ofHom (ContinuousMap.id X) : TopCat.of X ⟶ TopCat.of X) = 𝟙 (TopCat.of X)
    from rfl]
  simp

/-- `hmap R` is functorial. -/
theorem hmap_comp (R : Type) [CommRing R] {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (i : ℕ) :
    hmap R (g.comp f) i = hmap R f i ≫ hmap R g i := by
  rw [Work.Pi6.hmap, Work.Pi6.hmap, Work.Pi6.hmap]
  rw [show (TopCat.ofHom (g.comp f) : TopCat.of X ⟶ TopCat.of Z) =
      (TopCat.ofHom f ≫ TopCat.ofHom g) from rfl, Work.Cohomology.chainMap,
    Work.Cohomology.chainMap, Work.Cohomology.chainMap, Functor.map_comp,
    HomologicalComplex.homologyMap_comp]

/-- Homotopic maps induce the same map on singular homology, in any coefficient ring. -/
theorem hmap_homotopic (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {f g : C(X, Y)} (H : f.Homotopy g) (i : ℕ) :
    hmap R f i = hmap R g i :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (C := ModuleCat R) (X := TopCat.of X) (Y := TopCat.of Y)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of R R) i

/-! ## Isomorphisms on homology induced by equivalences of spaces -/

/-- A homotopy equivalence induces an isomorphism on singular homology. -/
theorem isIso_hmap_of_homotopyEquiv (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (i : ℕ) :
    IsIso (hmap R e.toFun i) := by
  have h1 : TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun))
      (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun))
      (𝟙 (TopCat.of Y)) := e.right_inv.some
  exact Work.Cohomology.homologyEquiv R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)
    (TopCat.ofHom e.invFun) h1 h2 i

/-- A homeomorphism induces an isomorphism on singular homology. -/
theorem isIso_hmap_of_homeomorph (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (i : ℕ) :
    IsIso (hmap R (e : C(X, Y)) i) :=
  isIso_hmap_of_homotopyEquiv R e.toHomotopyEquiv i

/-- Vanishing of singular homology is transported along a homeomorphism. -/
theorem isZero_homology_of_homeomorph {R : Type} [CommRing R] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (i : ℕ) (h : IsZero (HR R X i)) :
    IsZero (HR R Y i) := by
  haveI := isIso_hmap_of_homeomorph R e.symm i
  exact IsZero.of_iso h (asIso (hmap R (e.symm : C(Y, X)) i))

/-- Path connectedness is transported along a homeomorphism. -/
theorem pathConnectedSpace_of_homeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : PathConnectedSpace Y) : PathConnectedSpace X where
  nonempty := ⟨e.symm (Classical.choice hY.nonempty)⟩
  joined x y := by
    have h : Joined (e x) (e y) := hY.joined (e x) (e y)
    have h' : Joined (e.symm (e x)) (e.symm (e y)) := h.map e.symm.continuous
    simpa using h'

/-! ## The mapping path space is homotopy equivalent to the total space -/

/-- The projection `mpathFst p : mpath p → E` as an explicit homotopy equivalence (the witness
provided by `Work.FGThm.mpathHomotopyEquiv`, with forward map definitionally `mpathFst p`). -/
def mpathFstHomotopyEquiv {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) :
    ContinuousMap.HomotopyEquiv (Work.Serre.mpath p) E where
  toFun := Work.Serre.mpathFst p
  invFun := Work.Serre.mpathOf p
  left_inv := Work.FGThm.mpathOf_comp_mpathFst_homotopic p
  right_inv := by
    have h : (Work.Serre.mpathFst p).comp (Work.Serre.mpathOf p) = ContinuousMap.id E := by
      ext e
      rfl
    rw [h]

/-- `mpathFst p : mpath p → E` is an isomorphism on homology in every degree. -/
theorem isIso_hmap_mpathFst (R : Type) [CommRing R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (i : ℕ) :
    IsIso (hmap R (Work.Serre.mpathFst p) i) :=
  isIso_hmap_of_homotopyEquiv R (mpathFstHomotopyEquiv p) i

/-- **The projection `mpathQ p` induces `p_*` up to the homotopy equivalence `mpathFst p`.** -/
theorem hmap_mpathQ_eq (R : Type) [CommRing R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (i : ℕ) :
    hmap R (Work.Serre.mpathQ p) i
      = hmap R (Work.Serre.mpathFst p) i ≫ hmap R p i := by
  rw [← hmap_comp R (Work.Serre.mpathFst p) p i]
  exact hmap_homotopic R (Work.Serre.mpath_homotopic p).some.symm i

/-! ## Transport of exactness along isomorphisms -/

/-- An isomorphism of `ModuleCat R` objects, as an equivalence of the underlying types. -/
def isoEquiv {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) : ↥M ≃ ↥N :=
  Equiv.ofBijective (⇑(e.hom)) (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom)

@[simp] theorem isoEquiv_apply {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) (x : ↥M) :
    isoEquiv e x = e.hom.hom x := rfl

@[simp] theorem isoEquiv_zero_iff {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N)
    (x : ↥M) : isoEquiv e x = 0 ↔ x = 0 := by
  rw [isoEquiv_apply]
  exact ⟨fun h => (CategoryTheory.ConcreteCategory.bijective_of_isIso e.hom).1 (by
    rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- The inverse of an isomorphism of modules, evaluated. -/
@[simp] theorem iso_inv_apply {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) (x : ↥M) :
    e.inv.hom (e.hom.hom x) = x :=
  ModuleCat.inv_hom_apply e x

/-- An isomorphism of modules followed by its inverse, evaluated. -/
@[simp] theorem iso_hom_apply {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) (y : ↥N) :
    e.hom.hom (e.inv.hom y) = y :=
  ModuleCat.hom_inv_apply e y

@[simp] theorem iso_symm_hom {R : Type} [Ring R] {M N : ModuleCat R} (e : M ≅ N) :
    e.symm.hom = e.inv := Iso.symm_hom e

/-- **Exactness of a pair of maps is transported along equivalences of the three terms.** -/
theorem Function.Exact.congr {A B C A' B' C' : Type*} [Zero C] [Zero C'] {f : A → B} {g : B → C}
    (h : Function.Exact f g) {f' : A' → B'} {g' : B' → C'}
    (α : A' ≃ A) (γ : B' ≃ B) (δ : C' ≃ C) (hδ : ∀ z : C', δ z = 0 ↔ z = 0)
    (hf : ∀ x, γ (f' x) = f (α x)) (hg : ∀ y, δ (g' y) = g (γ y)) :
    Function.Exact f' g' := by
  intro y
  have h1 : g' y = 0 ↔ γ y ∈ Set.range f :=
    ((hδ (g' y)).symm).trans (by rw [hg y]; exact h (γ y))
  rw [h1]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨α.symm a, γ.injective (by rw [hf, Equiv.apply_symm_apply, ha])⟩
  · rintro ⟨x, rfl⟩
    exact ⟨α x, (hf x).symm⟩

/-! ## The Serre range exact sequences of `mpathQ g₄` and `mpathQ g₅` -/

set_option maxHeartbeats 1600000 in
/-- **The Serre range exact sequence of `mpathQ g₄`, transported to `Y`, `E`, `P₄`.** -/
theorem rangeLES_four (R : Type) [CommRing R] (hR : SerreRangeLES)
    {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))
    {P4 : Type} [TopologicalSpace P4] (g4 : C(Ecov g3, P4))
    (hB : ∀ i : ℕ, i < 4 → Subsingleton (HomotopyGroup (Fin i) P4 (g4 (e0 g3))))
    (hF0 : Subsingleton (HomotopyGroup (Fin 0) (Ycov g3 g4) (y0 g3 g4)))
    (hF : ∀ j : ℕ, 0 < j → j < 5 → IsZero (HR ℤ (Ycov g3 g4) j)) :
    ∃ (incl : ∀ i, HR R (Ycov g3 g4) i ⟶ HR R (Ecov g3) i)
      (bd : ∀ i, HR R P4 (i + 1) ⟶ HR R (Ycov g3 g4) i),
      ∀ i : ℕ, i + 1 < 9 →
        Function.Exact (incl (i + 1)).hom (hmap R g4 (i + 1)).hom ∧
        Function.Exact (hmap R g4 (i + 1)).hom (bd i).hom ∧
        Function.Exact (bd i).hom (incl i).hom := by
  obtain ⟨Φ⟩ := Work.Serre.mpathQ_fibreHomeo g4 (e0 g3)
  have hfib : Subsingleton (HomotopyGroup (Fin 0)
      (Work.StemsB.fibre (Work.Serre.mpathQ g4) (g4 (e0 g3)))
      (⟨Work.Serre.mpathOf g4 (e0 g3), rfl⟩ :
        {x : Work.Serre.mpath g4 // Work.Serre.mpathQ g4 x = g4 (e0 g3)})) := by
    have hc : PathConnectedSpace (Ycov g3 g4) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (y0 g3 g4) hF0
    have hc' : PathConnectedSpace (Work.StemsB.fibre (Work.Serre.mpathQ g4) (g4 (e0 g3))) :=
      pathConnectedSpace_of_homeomorph Φ hc
    have hZ : Subsingleton (ZerothHomotopy
        (Work.StemsB.fibre (Work.Serre.mpathQ g4) (g4 (e0 g3)))) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hc').2
    refine ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x :=
      (⟨Work.Serre.mpathOf g4 (e0 g3), rfl⟩ :
        {x : Work.Serre.mpath g4 // Work.Serre.mpathQ g4 x = g4 (e0 g3)}))).injective ?_⟩
    exact hZ.elim _ _
  have hF' : ∀ j : ℕ, 0 < j → j < 5 → IsZero (HR ℤ
      (Work.StemsB.fibre (Work.Serre.mpathQ g4) (g4 (e0 g3))) j) := by
    intro j hj hj5
    exact isZero_homology_of_homeomorph Φ.symm j (hF j hj hj5)
  obtain ⟨bd, hbd⟩ := hR R (Work.Serre.mpath g4) P4 (Work.Serre.mpathQ g4)
    (Work.Serre.mpathOf g4 (e0 g3)) 4 5
    (Work.Serre.mpathQ_isSerreFibration g4) (by norm_num)
    (fun i hi => hB i hi) hfib hF'
  let Φc : Work.StemsB.fibre (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3))) ≃ₜ Ycov g3 g4 :=
    { toFun := fun x => Φ x
      invFun := fun y => Φ.symm y
      left_inv := fun x => Φ.left_inv x
      right_inv := fun y => Φ.right_inv y
      continuous_toFun := Φ.continuous_toFun
      continuous_invFun := Φ.continuous_invFun }
  let μc : C(Work.Serre.mpath g4, Ecov g3) := Work.Serre.mpathFst g4
  let fc : C(Work.StemsB.fibre (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3))), Work.Serre.mpath g4) :=
    Work.StemsB.fibreIncl (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3)))
  have hΦi : ∀ i : ℕ, IsIso (hmap R (Φc : C(Work.StemsB.fibre (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3))), Ycov g3 g4)) i) :=
    fun i => isIso_hmap_of_homeomorph R Φc i
  have hμi : ∀ i : ℕ, IsIso (hmap R μc i) := fun i => isIso_hmap_mpathFst R g4 i
  let Ph : ∀ i, HR R (Work.StemsB.fibre (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3)))) i ≅ HR R (Ycov g3 g4) i := fun i => by
    haveI := hΦi i
    exact asIso (hmap R (Φc : C(Work.StemsB.fibre (Work.Serre.mpathQ g4) (Work.Serre.mpathQ g4 (Work.Serre.mpathOf g4 (e0 g3))), Ycov g3 g4)) i)
  let Mu : ∀ i, HR R (Work.Serre.mpath g4) i ≅ HR R (Ecov g3) i := fun i => by
    haveI := hμi i
    exact asIso (hmap R μc i)
  let incl : ∀ i, HR R (Ycov g3 g4) i ⟶ HR R (Ecov g3) i := fun i =>
    (Ph i).inv ≫ hmap R fc i ≫ (Mu i).hom
  let bd' : ∀ i, HR R P4 (i + 1) ⟶ HR R (Ycov g3 g4) i := fun i => bd i ≫ (Ph i).hom
  refine ⟨incl, bd', ?_⟩
  intro i hi
  obtain ⟨h1, h2, h3⟩ := hbd i hi
  have key : hmap R (Work.Serre.mpathQ g4) (i + 1)
      = hmap R μc (i + 1) ≫ hmap R g4 (i + 1) :=
    hmap_mpathQ_eq R g4 (i + 1)
  have key2 : ∀ x : ↥(HR R (Ecov g3) (i + 1)),
      (hmap R (Work.Serre.mpathQ g4) (i + 1)).hom ((Mu (i + 1)).inv.hom x)
        = (hmap R g4 (i + 1)).hom x := by
    intro x
    rw [key, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact congrArg (fun z => (hmap R g4 (i + 1)).hom z)
      (ModuleCat.hom_inv_apply (asIso (hmap R μc (i + 1))) x)
  have hf1 : ∀ x, (isoEquiv (Mu (i + 1)).symm) (incl (i + 1) x)
      = (hmap R fc (i + 1)).hom ((isoEquiv (Ph (i + 1)).symm) x) := by
    intro x
    dsimp only [incl, Ph, Mu]
    simp only [isoEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ConcreteCategory.comp_apply, Iso.symm_hom, iso_inv_apply, iso_hom_apply]
  have hg1 : ∀ y, (hmap R g4 (i + 1)).hom y
      = (hmap R (Work.Serre.mpathQ g4) (i + 1)).hom ((isoEquiv (Mu (i + 1)).symm) y) := by
    intro y
    rw [isoEquiv_apply, Iso.symm_hom]
    exact (key2 y).symm
  have hf3 : ∀ x, (isoEquiv (Ph i).symm) (bd' i x) = (bd i).hom x := by
    intro x
    show (Ph i).inv.hom ((bd i ≫ (Ph i).hom).hom x) = (bd i).hom x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, iso_inv_apply]
  have hg3 : ∀ y, (isoEquiv (Mu i).symm) (incl i y)
      = (hmap R fc i).hom ((isoEquiv (Ph i).symm) y) := by
    intro y
    dsimp only [incl, Ph, Mu]
    simp only [isoEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ConcreteCategory.comp_apply, Iso.symm_hom, iso_inv_apply, iso_hom_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Function.Exact.congr h1 (isoEquiv (Ph (i + 1)).symm) (isoEquiv (Mu (i + 1)).symm)
      (Equiv.refl _) (fun z => Iff.rfl) hf1 (fun y => hg1 y)
  · exact Function.Exact.congr h2 (isoEquiv (Mu (i + 1)).symm) (Equiv.refl _)
      (isoEquiv (Ph i).symm) (fun z => isoEquiv_zero_iff (Ph i).symm z)
      (fun x => hg1 x) (fun y => hf3 y)
  · exact Function.Exact.congr h3 (Equiv.refl _) (isoEquiv (Ph i).symm)
      (isoEquiv (Mu i).symm) (fun z => isoEquiv_zero_iff (Mu i).symm z)
      (fun x => hf3 x) hg3


set_option maxHeartbeats 1600000 in
/-- **The Serre range exact sequence of `mpathQ g₅`, transported to `Z`, `Y`, `P₅`.** -/
theorem rangeLES_five (R : Type) [CommRing R] (hR : SerreRangeLES)
    {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))
    {P4 : Type} [TopologicalSpace P4] (g4 : C(Ecov g3, P4))
    {P5 : Type} [TopologicalSpace P5] (g5 : C(Ycov g3 g4, P5))
    (hB : ∀ i : ℕ, i < 5 → Subsingleton (HomotopyGroup (Fin i) P5 (g5 (y0 g3 g4))))
    (hF0 : Subsingleton (HomotopyGroup (Fin 0) (Zcov g3 g4 g5)
      (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4))))
    (hF : ∀ j : ℕ, 0 < j → j < 6 → IsZero (HR ℤ (Zcov g3 g4 g5) j)) :
    ∃ (incl : ∀ i, HR R (Zcov g3 g4 g5) i ⟶ HR R (Ycov g3 g4) i)
      (bd : ∀ i, HR R P5 (i + 1) ⟶ HR R (Zcov g3 g4 g5) i),
      ∀ i : ℕ, i + 1 < 11 →
        Function.Exact (incl (i + 1)).hom (hmap R g5 (i + 1)).hom ∧
        Function.Exact (hmap R g5 (i + 1)).hom (bd i).hom ∧
        Function.Exact (bd i).hom (incl i).hom := by
  obtain ⟨Φ⟩ := Work.Serre.mpathQ_fibreHomeo g5 (y0 g3 g4)
  have hfib : Subsingleton (HomotopyGroup (Fin 0)
      (Work.StemsB.fibre (Work.Serre.mpathQ g5) (g5 (y0 g3 g4)))
      (⟨Work.Serre.mpathOf g5 (y0 g3 g4), rfl⟩ :
        {x : Work.Serre.mpath g5 // Work.Serre.mpathQ g5 x = g5 (y0 g3 g4)})) := by
    have hc : PathConnectedSpace (Zcov g3 g4 g5) :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero
        (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4)) hF0
    have hc' : PathConnectedSpace (Work.StemsB.fibre (Work.Serre.mpathQ g5) (g5 (y0 g3 g4))) :=
      pathConnectedSpace_of_homeomorph Φ hc
    have hZ : Subsingleton (ZerothHomotopy
        (Work.StemsB.fibre (Work.Serre.mpathQ g5) (g5 (y0 g3 g4)))) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hc').2
    refine ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (x :=
      (⟨Work.Serre.mpathOf g5 (y0 g3 g4), rfl⟩ :
        {x : Work.Serre.mpath g5 // Work.Serre.mpathQ g5 x = g5 (y0 g3 g4)}))).injective ?_⟩
    exact hZ.elim _ _
  have hF' : ∀ j : ℕ, 0 < j → j < 6 → IsZero (HR ℤ
      (Work.StemsB.fibre (Work.Serre.mpathQ g5) (g5 (y0 g3 g4))) j) := by
    intro j hj hj5
    exact isZero_homology_of_homeomorph Φ.symm j (hF j hj hj5)
  obtain ⟨bd, hbd⟩ := hR R (Work.Serre.mpath g5) P5 (Work.Serre.mpathQ g5)
    (Work.Serre.mpathOf g5 (y0 g3 g4)) 5 6
    (Work.Serre.mpathQ_isSerreFibration g5) (by norm_num)
    (fun i hi => hB i hi) hfib hF'
  let Φc : Work.StemsB.fibre (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4))) ≃ₜ Zcov g3 g4 g5 :=
    { toFun := fun x => Φ x
      invFun := fun y => Φ.symm y
      left_inv := fun x => Φ.left_inv x
      right_inv := fun y => Φ.right_inv y
      continuous_toFun := Φ.continuous_toFun
      continuous_invFun := Φ.continuous_invFun }
  let μc : C(Work.Serre.mpath g5, Ycov g3 g4) := Work.Serre.mpathFst g5
  let fc : C(Work.StemsB.fibre (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4))), Work.Serre.mpath g5) :=
    Work.StemsB.fibreIncl (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4)))
  have hΦi : ∀ i : ℕ, IsIso (hmap R (Φc : C(Work.StemsB.fibre (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4))), Zcov g3 g4 g5)) i) :=
    fun i => isIso_hmap_of_homeomorph R Φc i
  have hμi : ∀ i : ℕ, IsIso (hmap R μc i) := fun i => isIso_hmap_mpathFst R g5 i
  let Ph : ∀ i, HR R (Work.StemsB.fibre (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4)))) i ≅ HR R (Zcov g3 g4 g5) i := fun i => by
    haveI := hΦi i
    exact asIso (hmap R (Φc : C(Work.StemsB.fibre (Work.Serre.mpathQ g5) (Work.Serre.mpathQ g5 (Work.Serre.mpathOf g5 (y0 g3 g4))), Zcov g3 g4 g5)) i)
  let Mu : ∀ i, HR R (Work.Serre.mpath g5) i ≅ HR R (Ycov g3 g4) i := fun i => by
    haveI := hμi i
    exact asIso (hmap R μc i)
  let incl : ∀ i, HR R (Zcov g3 g4 g5) i ⟶ HR R (Ycov g3 g4) i := fun i =>
    (Ph i).inv ≫ hmap R fc i ≫ (Mu i).hom
  let bd' : ∀ i, HR R P5 (i + 1) ⟶ HR R (Zcov g3 g4 g5) i := fun i => bd i ≫ (Ph i).hom
  refine ⟨incl, bd', ?_⟩
  intro i hi
  obtain ⟨h1, h2, h3⟩ := hbd i hi
  have key : hmap R (Work.Serre.mpathQ g5) (i + 1)
      = hmap R μc (i + 1) ≫ hmap R g5 (i + 1) :=
    hmap_mpathQ_eq R g5 (i + 1)
  have key2 : ∀ x : ↥(HR R (Ycov g3 g4) (i + 1)),
      (hmap R (Work.Serre.mpathQ g5) (i + 1)).hom ((Mu (i + 1)).inv.hom x)
        = (hmap R g5 (i + 1)).hom x := by
    intro x
    rw [key, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact congrArg (fun z => (hmap R g5 (i + 1)).hom z)
      (ModuleCat.hom_inv_apply (asIso (hmap R μc (i + 1))) x)
  have hf1 : ∀ x, (isoEquiv (Mu (i + 1)).symm) (incl (i + 1) x)
      = (hmap R fc (i + 1)).hom ((isoEquiv (Ph (i + 1)).symm) x) := by
    intro x
    dsimp only [incl, Ph, Mu]
    simp only [isoEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ConcreteCategory.comp_apply, Iso.symm_hom, iso_inv_apply, iso_hom_apply]
  have hg1 : ∀ y, (hmap R g5 (i + 1)).hom y
      = (hmap R (Work.Serre.mpathQ g5) (i + 1)).hom ((isoEquiv (Mu (i + 1)).symm) y) := by
    intro y
    rw [isoEquiv_apply, Iso.symm_hom]
    exact (key2 y).symm
  have hf3 : ∀ x, (isoEquiv (Ph i).symm) (bd' i x) = (bd i).hom x := by
    intro x
    show (Ph i).inv.hom ((bd i ≫ (Ph i).hom).hom x) = (bd i).hom x
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, iso_inv_apply]
  have hg3 : ∀ y, (isoEquiv (Mu i).symm) (incl i y)
      = (hmap R fc i).hom ((isoEquiv (Ph i).symm) y) := by
    intro y
    dsimp only [incl, Ph, Mu]
    simp only [isoEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      ConcreteCategory.comp_apply, Iso.symm_hom, iso_inv_apply, iso_hom_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Function.Exact.congr h1 (isoEquiv (Ph (i + 1)).symm) (isoEquiv (Mu (i + 1)).symm)
      (Equiv.refl _) (fun z => Iff.rfl) hf1 (fun y => hg1 y)
  · exact Function.Exact.congr h2 (isoEquiv (Mu (i + 1)).symm) (Equiv.refl _)
      (isoEquiv (Ph i).symm) (fun z => isoEquiv_zero_iff (Ph i).symm z)
      (fun x => hg1 x) (fun y => hf3 y)
  · exact Function.Exact.congr h3 (Equiv.refl _) (isoEquiv (Ph i).symm)
      (isoEquiv (Mu i).symm) (fun z => isoEquiv_zero_iff (Mu i).symm z)
      (fun x => hf3 x) hg3

end

end Work.Pi6.HALG
