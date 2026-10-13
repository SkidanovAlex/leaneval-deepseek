import Mathlib
import Submission.Work.DSM5b.CechIsoDefs

namespace Work.DSG4a

open CategoryTheory Limits Opposite
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.power

noncomputable abbrev cechIx {C : Type*} [Category C] [HasFiniteProducts C] {ι : Type*}
    (U : ι → C) (n : ℕ) :=
  ((FormalCoproduct.mk ι U).cech.obj (Opposite.op (SimplexCategory.mk n))).I

noncomputable abbrev cechOb {C : Type*} [Category C] [HasFiniteProducts C] {ι : Type*}
    (U : ι → C) (n : ℕ) (x : cechIx U n) : C :=
  ((FormalCoproduct.mk ι U).cech.obj (Opposite.op (SimplexCategory.mk n))).obj x

/-- Componentwise chain-map computation for the Čech complex in a completely general setting:
if a family of maps `Φ n x : F (P (E n x)) ⟶ Q (E' n x)` is compatible with the cofaces, then the
`Pi.lift`ed family commutes with the Čech differentials. -/
theorem cech_d_comm_pi {C : Type*} [Category C] [HasFiniteProducts C]
    {C' : Type*} [Category C'] [HasFiniteProducts C']
    {D : Type*} [Category D] [Preadditive D] [HasProducts D]
    {D' : Type*} [Category D'] [Preadditive D'] [HasProducts D']
    (F : D ⥤ D') [F.Additive] {ι : Type*} (U : ι → C) (U' : ι → C')
    (P : Cᵒᵖ ⥤ D) (Q : C'ᵒᵖ ⥤ D')
    (Φ : ∀ (n : ℕ) (x : cechIx U n),
      F.obj (P.obj (Opposite.op (cechOb U n x))) ⟶ Q.obj (Opposite.op (cechOb U' n x)))
    (hΦ : ∀ (n : ℕ) (a : Fin (n + 2)) (x : cechIx U (n + 1)),
      F.map (P.map (((FormalCoproduct.mk ι U).cech.map
            (SimplexCategory.δ a).op).φ x).op) ≫ Φ (n + 1) x =
        Φ n (((FormalCoproduct.mk ι U).cech.map
            (SimplexCategory.δ a).op).f x) ≫
          Q.map (((FormalCoproduct.mk ι U').cech.map
            (SimplexCategory.δ a).op).φ x).op)
    (n : ℕ) (x : cechIx U' (n + 1)) :
    (F.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb U (n + 1) z))) y) ≫ Φ (n + 1) y)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb U' (n + 1) y))) x =
    (Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb U n z))) y) ≫ Φ n y) ≫
        ((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb U' (n + 1) y))) x := by
  have hL : (F.map (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb U (n + 1) z))) y) ≫ Φ (n + 1) y)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb U' (n + 1) y))) x =
      F.map (((cechComplexFunctor U).obj P).d n (n + 1) ≫
        Pi.π (fun z => P.obj (Opposite.op (cechOb U (n + 1) z))) x) ≫ Φ (n + 1) x := by
    erw [Category.assoc, Pi.lift_comp_π, ← Category.assoc, ← Functor.map_comp]
  have hR : (Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb U n z))) y) ≫ Φ n y) ≫
        ((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
      Pi.π (fun y => Q.obj (Opposite.op (cechOb U' (n + 1) y))) x =
      Pi.lift (fun y => F.map (Pi.π
          (fun z => P.obj (Opposite.op (cechOb U n z))) y) ≫ Φ n y) ≫
        ((((cechComplexFunctor U').obj Q).d n (n + 1)) ≫
          Pi.π (fun y => Q.obj (Opposite.op (cechOb U' (n + 1) y))) x) := by
    erw [Category.assoc]
  erw [hL, hR]
  erw [Work.DSM5b.cech_d_comp_π_gen U P n x]
  simp only [Functor.map_sum, Functor.map_zsmul, Functor.map_comp]
  erw [Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp]
  erw [Work.DSM5b.cech_d_comp_π_gen U' Q n x]
  erw [Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs => erw [Category.assoc]
  conv_rhs => erw [← Category.assoc]
  erw [hΦ n a x]
  erw [Pi.lift_comp_π]
  erw [Category.assoc]
  rfl

end Work.DSG4a
