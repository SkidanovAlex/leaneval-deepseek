import Mathlib
import Submission.Work.DSEQP.AcDefs

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

namespace Work.DSEQP

universe u

/-! ## Auxiliary lemmas for `AcDiff`

The level-`e` map `S.ofLvl U n e` from the ordinary Čech complex of `𝒪_X` (as a complex of
`A`-modules) to the perfected Čech complex `S.K U` (a complex of `W = Γ(X,⊤)^{1/p^∞}`-modules)
is componentwise given by the perfection maps `Perf.of _ p _ e`.  Since the Čech differential
is the alternating sum of the restriction maps of the relevant presheaves, and `Perf.of _ p _ e`
commutes with restrictions (`Perf.map_of`), it commutes with the differential.

The lemmas below record:
* the component formula for the Čech differential, both in morphism form and in element form
  (`cech_d_pi`, `cech_d_apply`), proved directly from Mathlib's construction of the Čech complex
  (in the universe configuration needed here, which `Work.DSF1.Cech.cechComplexFunctor_d_π` does
  not cover);
* the element form of that formula for the ordinary and the perfected Čech complexes
  (`PerfSetup.cobj_d_apply`, `PerfSetup.K_d_apply`);
* the componentwise description of `ofLvl` (`PerfSetup.π_ofLvl`) and its compatibility with the
  restriction maps of the perfected structure presheaf (`PerfSetup.perfPresheaf_map_of`);
* the fact that `Perf.of _ p _ e` is additive and commutes with integer multiples
  (`Perf.of_sum_zsmul`) so that it commutes with the alternating sum forming the differential.
-/

/-- Two elements of a product of modules over a ring agree as soon as all their components do. -/
theorem pi_elem_ext {R : Type u} [Ring R] {β : Type u} (Z : β → ModuleCat.{u} R)
    [HasProduct Z] {x y : (∏ᶜ Z : ModuleCat.{u} R)}
    (h : ∀ i, (Pi.π Z i).hom x = (Pi.π Z i).hom y) : x = y := by
  have hhom : (ModuleCat.piIsoPi Z).hom x = (ModuleCat.piIsoPi Z).hom y := by
    funext i
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact h i
  exact (Iso.hom_inv_id_apply (ModuleCat.piIsoPi Z) x).symm.trans
    ((congrArg (ModuleCat.piIsoPi Z).inv hhom).trans
      (Iso.hom_inv_id_apply (ModuleCat.piIsoPi Z) y))

namespace Perf

/-- The level-`e` perfection map is additive and commutes with integer multiples, hence with an
alternating sum: `∑ z b • of (r b) = of (∑ z b • r b)`. -/
theorem of_sum_zsmul {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp : (p : R) = 0)
    {β : Type*} (s : Finset β) (e : ℕ) (z : β → ℤ) (r : β → R) :
    (∑ b ∈ s, z b • of R p hp e (r b)) = of R p hp e (∑ b ∈ s, z b • r b) := by
  rw [map_sum (of R p hp e)]
  exact Finset.sum_congr rfl (fun b _ => (map_zsmul (of R p hp e) (z b) (r b)).symm)

end Perf

section CechComponent

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}

/-- **Component formula for the Čech differential** (morphism form): the `a`-th component of the
differential of the Čech complex of a presheaf `P` of modules is the alternating sum of the
components of the individual cofaces.  This is
`Work.DSF1.Cech.cechComplexFunctor_d_π` re-proved in the universe configuration
`R : Type u`, `X : Scheme.{u}`, `ι : Type u` needed here (the original statement forces the
universe of the index type to be that of the *objects* of `ModuleCat R`). -/
theorem cech_d_pi (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (a : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).I) :
    (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).obj y))) a)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)) ≫
            P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

/-- **Component formula for the Čech differential** (element form). -/
theorem cech_d_apply (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (y : ((cechComplexFunctor U).obj P).X n)
    (a : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).I) :
    (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).obj y))) a).hom
        ((((cechComplexFunctor U).obj P).d n (n + 1)).hom y)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
            ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom y) := by
  have h := cech_d_pi U P n a
  have h2 := congrArg (fun g => (ModuleCat.Hom.hom g) y) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] at h2
  exact h2

end CechComponent

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- **Component formula for the differential of the perfected Čech complex** (element form). -/
theorem K_d_apply (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (y : (S.K U).X n) (a : (CechIdx U (n + 1)).I) :
    (Pi.π (S.Kobj U (n + 1)) a).hom (((S.K U).d n (n + 1)).hom y)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (S.perfPresheaf.map
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
            ((Pi.π (S.Kobj U n)
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom y) :=
  cech_d_apply U S.perfPresheaf n y a

/-- **Component formula for the differential of the ordinary Čech complex** of `𝒪_X`
(element form). -/
theorem cobj_d_apply (U : ι → X.Opens) (n : ℕ) (y : (DSMap.cech A X f U).X n)
    (a : (CechIdx U (n + 1)).I) :
    (Pi.π (cobj (A := A) (X := X) (f := f) U (n + 1)) a).hom
        (((DSMap.cech A X f U).d n (n + 1)).hom y)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (((DSMap.cechPresheaf A X f).map
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op)).hom
            ((Pi.π (cobj (A := A) (X := X) (f := f) U n)
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom y) :=
  cech_d_apply U (DSMap.cechPresheaf A X f) n y a

/-- The component of `S.ofLvl U n e x` at the Čech index `a` is the level-`e` perfection of the
corresponding component of `x`. -/
theorem π_ofLvl (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) (a : (CechIdx U n).I) :
    (Pi.π (S.kobj U n) a).hom (S.ofLvl U n e x) =
      Perf.of (Γ(X, CechOp U n a)) p (S.hpU _) e
        ((Pi.π (cobj (A := A) (X := X) (f := f) U n) a).hom x) := by
  simp only [ofLvl, kpack_apply, cunpack_apply]

/-- The restriction maps of the perfected structure presheaf commute with the level-`e`
perfection maps. -/
theorem perfPresheaf_map_of (S : PerfSetup A p X f) {W₁ W₂ : X.Opens} (g : W₁ ⟶ W₂) (e : ℕ)
    (z : Γ(X, W₂)) :
    (S.perfPresheaf.map g.op).hom (Perf.of (Γ(X, W₂)) p (S.hpU W₂) e z) =
      Perf.of (Γ(X, W₁)) p (S.hpU W₁) e ((X.presheaf.map g.op).hom z) := by
  change Perf.map (S.hpU W₂) (S.hpU W₁) ((X.presheaf.map g.op).hom)
      (Perf.of (Γ(X, W₂)) p (S.hpU W₂) e z) = _
  rw [Perf.map_of]

/-- **`ofLvl` is a chain map, componentwise**: the `a`-th component of the differential applied
to `ofLvl U n e x` is the level-`e` perfection of the `a`-th component of the differential
applied to `x`. -/
theorem π_K_d (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) (a : (CechIdx U (n + 1)).I) :
    (Pi.π (S.kobj U (n + 1)) a).hom (((S.K U).d n (n + 1)).hom (S.ofLvl U n e x))
      = Perf.of (Γ(X, CechOp U (n + 1) a)) p (S.hpU (CechOp U (n + 1) a)) e
          ((Pi.π (cobj (A := A) (X := X) (f := f) U (n + 1)) a).hom
            (((DSMap.cech A X f U).d n (n + 1)).hom x)) := by
  calc (Pi.π (S.kobj U (n + 1)) a).hom (((S.K U).d n (n + 1)).hom (S.ofLvl U n e x))
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (S.perfPresheaf.map
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
            ((Pi.π (S.Kobj U n)
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom
              (S.ofLvl U n e x)) :=
        S.K_d_apply U n (S.ofLvl U n e x) a
    _ = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (S.perfPresheaf.map
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
            (Perf.of
              (Γ(X, CechOp U n
                (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)))
              p (S.hpU (CechOp U n
                (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a))) e
              ((Pi.π (cobj (A := A) (X := X) (f := f) U n)
                (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom x)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        refine congrArg (fun w => (-1 : ℤ) ^ (c : ℕ) • w) ?_
        exact congrArg (fun w => (S.perfPresheaf.map
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom w)
          (π_ofLvl S U n e x
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a))
    _ = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          Perf.of (Γ(X, CechOp U (n + 1) a)) p (S.hpU (CechOp U (n + 1) a)) e
            (((DSMap.cechPresheaf A X f).map
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
              ((Pi.π (cobj (A := A) (X := X) (f := f) U n)
                (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom x)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        refine congrArg (fun w => (-1 : ℤ) ^ (c : ℕ) • w) ?_
        exact perfPresheaf_map_of S
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a) e
          ((Pi.π (cobj (A := A) (X := X) (f := f) U n)
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom x)
    _ = Perf.of (Γ(X, CechOp U (n + 1) a)) p (S.hpU (CechOp U (n + 1) a)) e
          (∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
            (((DSMap.cechPresheaf A X f).map
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
              ((Pi.π (cobj (A := A) (X := X) (f := f) U n)
                (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom x))) :=
        Perf.of_sum_zsmul _ _ _ _ _
    _ = Perf.of (Γ(X, CechOp U (n + 1) a)) p (S.hpU (CechOp U (n + 1) a)) e
          ((Pi.π (cobj (A := A) (X := X) (f := f) U (n + 1)) a).hom
            (((DSMap.cech A X f U).d n (n + 1)).hom x)) := by
        rw [cobj_d_apply U n x a]

end PerfSetup

open PerfSetup

theorem AcDiff {A : Type} [CommRing A] {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsIntegral X] {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {ι : Type} [Finite ι] (S : Work.DSEQP.PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) :
    (S.K U).d n (n + 1) (S.ofLvl U n e x) =
      S.ofLvl U (n + 1) e ((DSMap.cech A X f U).d n (n + 1) x) := by
  classical
  refine pi_elem_ext (β := (CechIdx U (n + 1)).I) (S.kobj U (n + 1)) (fun a => ?_)
  exact (π_K_d S U n e x a).trans
    (π_ofLvl S U (n + 1) e ((DSMap.cech A X f U).d n (n + 1) x) a).symm

end Work.DSEQP
