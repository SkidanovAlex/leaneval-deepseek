import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Submission.Commons.RepresentationTheory.GroupCohomology.barComplex_res_comp_pi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 2000000

namespace NK.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

/-- The `n`-th component of the canonical chain map `barComplex k S ⟶ Res(barComplex k G)`
induced by the inclusion `S ⊆ G`: it sends the generator `x : Fin n → S` to the generator
`S.subtype ∘ x`. -/
noncomputable def barResMap (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G) (n : ℕ) :
    (Rep.barComplex k S).X n ⟶ Rep.res S.subtype (Rep.free k G (Fin n → G)) :=
  Rep.freeLift k S (Rep.res S.subtype (Rep.free k G (Fin n → G)))
    (fun x : Fin n → S => Finsupp.single (S.subtype ∘ x) (1 : MonoidAlgebra k G))

lemma barResMap_apply (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G) (n : ℕ)
    (x : Fin n → S) (g : S) (r : k) :
    (barResMap k G S n).hom (Finsupp.single x (MonoidAlgebra.single g r)) =
      Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (S.subtype g) r) := by
  show (Representation.freeLift (MonoidHom.comp (Rep.free k G (Fin n → G)).ρ S.subtype)
      (fun x : Fin n → S => Finsupp.single (S.subtype ∘ x) (1 : MonoidAlgebra k G)))
      (Finsupp.single x (MonoidAlgebra.single g r)) = _
  rw [Representation.freeLift_single_single]
  have h1 : (1 : MonoidAlgebra k G) = MonoidAlgebra.single (1 : G) (1 : k) := rfl
  rw [h1, MonoidHom.comp_apply, Representation.free_single_single]
  simp

lemma barResMap_comp (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G) (n : ℕ) :
    barResMap k G S (n+1) ≫ Rep.resMap S.subtype ((Rep.barComplex k G).d (n+1) n) =
      (Rep.barComplex k S).d (n+1) n ≫ barResMap k G S n := by
  apply Rep.free_ext
  intro x
  rw [Rep.comp_apply, Rep.comp_apply]
  rw [Rep.barComplex.d_def, Rep.barComplex.d_def]
  rw [barResMap_apply k G S (n+1) x 1 1]
  rw [Rep.resMap_hom_apply]
  simp only [map_one]
  rw [Rep.barComplex.d_single, Rep.barComplex.d_single]
  rw [map_add, map_sum]
  congr 1
  · rw [barResMap_apply k G S n (fun i => x i.succ) (x 0) 1]
    congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [barResMap_apply k G S n (j.contractNth (· * ·) x) 1 ((-1:k)^(j.val+1))]
    congr 2
    exact (Fin.comp_contractNth (fun a b => a * b) (fun a b => a * b)
      (fun a b => map_mul S.subtype a b) j x).symm

/-- The canonical resolution of the trivial `S`-representation obtained by restricting the bar
resolution of `G`. -/
noncomputable abbrev barResResolution (k : Type) [CommRing k] (G : Type) [Group G]
    (S : Subgroup G) : ProjectiveResolution (Rep.trivial k S k) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution k G)

/-- The canonical chain map `barComplex k S ⟶ Res(barComplex k G)` as a morphism of resolutions. -/
noncomputable def barResChain (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G) :
    Rep.barComplex k S ⟶ (barResResolution k G S).complex :=
  { f := fun n => barResMap k G S n
    comm' := by rintro i j (rfl : j + 1 = i); exact barResMap_comp k G S j }

set_option backward.isDefEq.respectTransparency false in
lemma barResChain_π (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G) :
    barResChain k G S ≫ (barResResolution k G S).π = (Rep.barResolution k S).π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      simp only [barResChain, barResResolution, barResMap, Functor.mapProjectiveResolution_π,
        HomologicalComplex.comp_f]
      exact Commons.RepresentationTheory.GroupCohomology.barComplex_res_comp_pi S
  | succ n =>
      rw [HomologicalComplex.comp_f, ProjectiveResolution.π_f_succ, ProjectiveResolution.π_f_succ]
      simp

set_option backward.isDefEq.respectTransparency false in
lemma barResChain_f_apply (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (i : ℕ) (x : Fin i → S) :
    ((barResChain k G S).f i).hom (Finsupp.single x (MonoidAlgebra.single (1:S) (1:k))) =
      Finsupp.single (S.subtype ∘ x) (MonoidAlgebra.single (1:G) (1:k)) := by
  rw [barResChain]
  exact barResMap_apply k G S i x 1 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison morphism `Hom(Res(bar_G), A) ⟶ Hom(bar_S, A)` induced by the canonical chain
map `barResChain k G S`. -/
noncomputable def psiMap (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (A : Rep.{0,0,0} k S) :
    letI : Linear k (Rep.{0,0,0} k S) := Rep.instLinear
    ((((Rep.resFunctor S.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex).linearYonedaObj k A) ⟶
      (((Rep.barComplex k S).linearYonedaObj k A)) :=
  letI : Linear k (Rep.{0,0,0} k S) := Rep.instLinear
  (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)).map
    (((Functor.mapHomologicalComplex ((linearYoneda k (Rep.{0,0,0} k S)).obj A).rightOp
      (ComplexShape.down ℕ)).map (barResChain k G S)).op)

set_option backward.isDefEq.respectTransparency false in
lemma psiMap_apply (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (A : Rep.{0,0,0} k S) (i : ℕ)
    (h : (barResResolution k G S).complex.X i ⟶ A)
    (z : (Rep.barComplex k S).X i) :
    (((psiMap k G S A).f i).hom h).hom z = h.hom (((barResChain k G S).f i).hom z) := by
  rw [psiMap, HomologicalComplex.unopFunctor_map_f]
  simp only [Quiver.Hom.op_unop]
  rfl

/-- The comparison isomorphism of complexes underlying Shapiro's lemma. -/
noncomputable abbrev lambdaIso (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (A : Rep.{0,0,0} k S) :
    letI : Linear k (Rep.{0,0,0} k S) := Rep.instLinear
    letI : Linear k (Rep.{0,0,0} k G) := Rep.instLinear
    ((((Rep.resFunctor S.subtype).mapProjectiveResolution
        (Rep.barResolution k G)).complex).linearYonedaObj k A) ≅
      (((Rep.barResolution k G).complex).linearYonedaObj k (Rep.coind S.subtype A)) :=
  groupCohomology.linearYonedaObjResProjectiveResolutionIso (Rep.barResolution k G) A

set_option backward.isDefEq.respectTransparency false in
lemma lambdaIso_symm_apply (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (A : Rep.{0,0,0} k S) (i : ℕ)
    (g : (Rep.barComplex k G).X i ⟶ Rep.coind S.subtype A)
    (u : (barResResolution k G S).complex.X i) :
    letI : Module k ↥A := A.hV2
    (((lambdaIso k G S A).symm.hom.f i).hom g).hom u =
      ((Representation.coindV S.subtype A.ρ).subtype (g.hom u)) 1 := by
  simp only [lambdaIso, groupCohomology.linearYonedaObjResProjectiveResolutionIso, Iso.symm_hom,
    HomologicalComplex.Hom.isoOfComponents_inv_f, LinearEquiv.toModuleIso_inv,
    ModuleCat.ofHom_hom, Rep.resCoindHomEquiv_symm_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a `k`-linear `G`-representation `A`, the isomorphism `inhomogeneousCochains A ≅ Hom(bar, A)`
evaluated at the basis element `single x (single 1 1)` is evaluation at `x`. -/
lemma inhomogeneousCochainsIso_apply (k : Type) [CommRing k] (G : Type) [Group G]
    (A : Rep k G) (i : ℕ) (z : (Fin i → G) → A.V) (x : Fin i → G) :
    (((groupCohomology.inhomogeneousCochainsIso A).hom.f i).hom z).hom
      (Finsupp.single x (MonoidAlgebra.single (1:G) (1:k))) = z x := by
  change (((Rep.freeLiftLEquiv k G (Fin i → G) A).symm z).hom
      (Finsupp.single x (MonoidAlgebra.single (1:G) (1:k))) = z x)
  rw [show (Rep.freeLiftLEquiv k G (Fin i → G) A).symm z =
      Rep.freeLift k G A z from rfl]
  rw [show Rep.freeLift k G A z = Rep.ofHom (Representation.freeLift A.ρ z) from rfl]
  simp [Representation.freeLift_single_single]

/-- The counit of the restriction–coind adjunction is evaluation at `1`. -/
lemma counit_app_apply (k : Type) [CommRing k] (G : Type) [Group G] (S : Subgroup G)
    (A : Rep.{0,0,0} k S) (z : ↥(Rep.res S.subtype (Rep.coind S.subtype A))) :
    ((Rep.resCoindAdjunction k S.subtype).counit.app A).hom z =
      (Representation.coindV S.subtype A.ρ).subtype z 1 := by
  rw [show (Rep.resCoindAdjunction k S.subtype).counit.app A
      = (Rep.resCoindHomEquiv S.subtype (Rep.coind S.subtype A) A).symm
          (𝟙 (Rep.coind S.subtype A)) from rfl]
  rw [Rep.resCoindHomEquiv_symm_apply]
  rfl

end NK.RepresentationTheory.GroupCohomology
