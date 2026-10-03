import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORHomAlg.JL52.middleIso

namespace Work.ORHomAlg.JL52

open CategoryTheory
open scoped TensorProduct

universe u

/-- The flip of the three factors of a triple tensor product over a field is `K[G]`-linear for the
diagonal `K[G]`-actions, stated for the `ModuleCat (K[G])`-objects built by `diagTensor`: the flip
`a ⊗ (b ⊗ c) ↦ c ⊗ (b ⊗ a)` is an isomorphism
`(diagTensor A).obj (ModuleCat.of K[G] (B ⊗[K] C)) ≅ (diagTensor C).obj (ModuleCat.of K[G] (B ⊗[K] A))`.
This is the "middle isomorphism" in the proof of Jaikin-Zapirain--Linton,
Lemma 5.2 (2) (the identification `L* ⊗_K (M ⊗_K N) ≅ N ⊗_K (M ⊗_K L*)`). -/
theorem middleIsoCat (K G : Type u) [Field K] [Group G] (A B C : Type u)
    [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup B] [Module K B] [Module (MonoidAlgebra K G) B]
    [SMulCommClass K (MonoidAlgebra K G) B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) C]
    [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B C)]
    [SMulCommClass K (MonoidAlgebra K G) (TensorProduct K B A)] :
    Nonempty (CategoryTheory.Iso
      ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) A).obj
        (ModuleCat.of (MonoidAlgebra K G) (TensorProduct K B C)))
      ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) C).obj
        (ModuleCat.of (MonoidAlgebra K G) (TensorProduct K B A)))) := by
  let X0 : ModuleCat (MonoidAlgebra K G) := ModuleCat.of (MonoidAlgebra K G) (TensorProduct K B C)
  let Y0 : ModuleCat (MonoidAlgebra K G) := ModuleCat.of (MonoidAlgebra K G) (TensorProduct K B A)
  let L : ModuleCat (MonoidAlgebra K G) := (diagTensor (K := K) (G := G) A).obj X0
  let R : ModuleCat (MonoidAlgebra K G) := (diagTensor (K := K) (G := G) C).obj Y0
  change Nonempty (CategoryTheory.Iso L R)
  let iX : Module K ↥X0 := instModuleCatK X0
  let nX : Module K ↥X0 := TensorProduct.instModule
  let smcXi := @IsScalarTower.to_smulCommClass K _ (MonoidAlgebra K G) _ _
      ↥X0 (ModuleCat.isAddCommGroup X0).toAddCommMonoid (ModuleCat.isModule X0) iX
      (instIsScalarTowerCatK X0)
  have hsmulX : ∀ (c : K) (m : ↥X0), iX.smul c m = nX.smul c m := by
    intro c m
    have h1 : iX.smul c m = (algebraMap K (MonoidAlgebra K G) c) • m := rfl
    have h2 : (algebraMap K (MonoidAlgebra K G) c) • m
        = diagRingHom B C (algebraMap K (MonoidAlgebra K G) c) m := rfl
    have h3 : diagRingHom B C (algebraMap K (MonoidAlgebra K G) c) m = c • m := by
      rw [Algebra.algebraMap_eq_smul_one, diagRingHom_smul, map_one]
      rw [LinearMap.smul_apply, Module.End.one_apply]
    rw [h1, h2, h3]
    rfl
  have hX : iX = nX := by
    apply Module.ext'
    intro c m
    exact hsmulX c m
  let γX : @LinearEquiv K K _ _ (RingHom.id K) (RingHom.id K) _ _ ↥X0 ↥X0 _ _ iX nX :=
    @LinearEquiv.mk K K _ _ (RingHom.id K) (RingHom.id K) _ _ ↥X0 ↥X0 _ _ iX nX
      (@LinearMap.mk K K _ _ (RingHom.id K) ↥X0 ↥X0 _ _ iX nX
        (AddHom.mk (fun m => m) (fun _ _ => rfl)) (fun c m => hsmulX c m))
      (fun m => m) (fun _ => rfl) (fun _ => rfl)
  have hγX : ∀ m : ↥X0, γX m = m := fun m => rfl
  let T1 : Type u := @TensorProduct K _ A ↥X0 _ _ _ iX
  let T2 : Type u := @TensorProduct K _ A ↥X0 _ _ _ nX
  let tm1 : A → ↥X0 → T1 := fun a x => @TensorProduct.tmul K _ A ↥X0 _ _ _ iX a x
  let tm2 : A → ↥X0 → T2 := fun a x => @TensorProduct.tmul K _ A ↥X0 _ _ _ nX a x
  let dT1 : Module (MonoidAlgebra K G) T1 :=
    @instDiagModule K _ G _ A ↥X0 _ _ _ _ _ iX (ModuleCat.isModule X0) smcXi
  let dT2 : Module (MonoidAlgebra K G) T2 := instDiagModule A (TensorProduct K B C)
  have hcomp1 : ∀ (r : MonoidAlgebra K G) (z : T1),
      dT1.smul r z
        = (@diagRingHom K _ G _ A ↥X0 _ _ _ _ _ iX (ModuleCat.isModule X0) smcXi) r z :=
    fun r z => rfl
  have hcomp2 : ∀ (r : MonoidAlgebra K G) (z : T2),
      dT2.smul r z = diagRingHom A (TensorProduct K B C) r z := fun r z => rfl
  let cnv : @LinearEquiv K K _ _ (RingHom.id K) (RingHom.id K) _ _ T1 T2 _ _ _ _ :=
    @TensorProduct.congr K K _ _ (RingHom.id K) A ↥X0 A ↥X0 _ _ _ _ _ iX _ nX (RingHom.id K) _ _
      (LinearEquiv.refl K A) γX
  have hcnv : (cnv : T1 → T2)
      = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) A ↥X0 A ↥X0 _ _ _ _ _ iX _ nX
          (RingHom.id K) _ _ (LinearEquiv.refl K A) γX) := rfl
  have hct : ∀ (a : A) (x : ↥X0),
      (@TensorProduct.congr K K _ _ (RingHom.id K) A ↥X0 A ↥X0 _ _ _ _ _ iX _ nX
          (RingHom.id K) _ _ (LinearEquiv.refl K A) γX) (tm1 a x) = tm2 a x := by
    intro a x
    rw [@TensorProduct.congr_tmul K K _ _ (RingHom.id K) A ↥X0 A ↥X0 _ _ _ _ _ iX _ nX
        (RingHom.id K) _ _ (LinearEquiv.refl K A) γX a x, LinearEquiv.refl_apply, hγX]
  let de1 : G → T1 →ₗ[K] T1 :=
    fun m => @diagElem K _ G _ A ↥X0 _ _ _ _ _ iX (ModuleCat.isModule X0) smcXi m
  have hgen : ∀ (m : G) (z : T1), cnv ((de1 m) z)
      = (diagElem A (TensorProduct K B C) m) (cnv z) := by
    intro m z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        rw [show (cnv : T1 → T2) = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) A ↥X0 A ↥X0
            _ _ _ _ _ iX _ nX (RingHom.id K) _ _ (LinearEquiv.refl K A) γX) from hcnv]
        rw [hct]
        rw [diagElem_tmul]
        rw [hct]
        rw [diagElem_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hβX : ∀ (r : MonoidAlgebra K G) (z : T1), cnv (dT1.smul r z) = dT2.smul r (cnv z) := by
    intro r z
    induction r using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply]
        rw [show dT1.smul (MonoidAlgebra.single m 1) z = (de1 m) z from by
              rw [hcomp1, diagRingHom_single]
              rfl,
            show dT2.smul (MonoidAlgebra.single m 1) (cnv z)
                = (diagElem A (TensorProduct K B C) m) (cnv z) from by
              rw [hcomp2, diagRingHom_single]
              rfl]
        exact hgen m z
    | add r s hr hs =>
        have hsplit1 : dT1.smul (r + s) z = dT1.smul r z + dT1.smul s z := by
          rw [hcomp1, hcomp1, hcomp1, map_add, LinearMap.add_apply]
        have hsplit2 : dT2.smul (r + s) (cnv z) = dT2.smul r (cnv z) + dT2.smul s (cnv z) := by
          rw [hcomp2, hcomp2, hcomp2, map_add, LinearMap.add_apply]
        rw [hsplit1, hsplit2, cnv.map_add, hr, hs]
    | smul c r hr =>
        have hsplit1 : dT1.smul (c • r) z = c • (dT1.smul r z) := by
          rw [hcomp1, hcomp1, diagRingHom_smul, LinearMap.smul_apply]
        have hsplit2 : dT2.smul (c • r) (cnv z) = c • (dT2.smul r (cnv z)) := by
          rw [hcomp2, hcomp2, diagRingHom_smul, LinearMap.smul_apply]
        rw [hsplit1, hsplit2, cnv.map_smul, hr]
  let iY : Module K ↥Y0 := instModuleCatK Y0
  let nY : Module K ↥Y0 := TensorProduct.instModule
  let smcYi := @IsScalarTower.to_smulCommClass K _ (MonoidAlgebra K G) _ _
      ↥Y0 (ModuleCat.isAddCommGroup Y0).toAddCommMonoid (ModuleCat.isModule Y0) iY
      (instIsScalarTowerCatK Y0)
  have hsmulY : ∀ (c : K) (m : ↥Y0), iY.smul c m = nY.smul c m := by
    intro c m
    have h1 : iY.smul c m = (algebraMap K (MonoidAlgebra K G) c) • m := rfl
    have h2 : (algebraMap K (MonoidAlgebra K G) c) • m
        = diagRingHom B A (algebraMap K (MonoidAlgebra K G) c) m := rfl
    have h3 : diagRingHom B A (algebraMap K (MonoidAlgebra K G) c) m = c • m := by
      rw [Algebra.algebraMap_eq_smul_one, diagRingHom_smul, map_one]
      rw [LinearMap.smul_apply, Module.End.one_apply]
    rw [h1, h2, h3]
    rfl
  have hY : iY = nY := by
    apply Module.ext'
    intro c m
    exact hsmulY c m
  let γY : @LinearEquiv K K _ _ (RingHom.id K) (RingHom.id K) _ _ ↥Y0 ↥Y0 _ _ iY nY :=
    @LinearEquiv.mk K K _ _ (RingHom.id K) (RingHom.id K) _ _ ↥Y0 ↥Y0 _ _ iY nY
      (@LinearMap.mk K K _ _ (RingHom.id K) ↥Y0 ↥Y0 _ _ iY nY
        (AddHom.mk (fun m => m) (fun _ _ => rfl)) (fun c m => hsmulY c m))
      (fun m => m) (fun _ => rfl) (fun _ => rfl)
  have hγY : ∀ m : ↥Y0, γY m = m := fun m => rfl
  let T3 : Type u := @TensorProduct K _ C ↥Y0 _ _ _ iY
  let T4 : Type u := @TensorProduct K _ C ↥Y0 _ _ _ nY
  let tm3 : C → ↥Y0 → T3 := fun a x => @TensorProduct.tmul K _ C ↥Y0 _ _ _ iY a x
  let tm4 : C → ↥Y0 → T4 := fun a x => @TensorProduct.tmul K _ C ↥Y0 _ _ _ nY a x
  let dT3 : Module (MonoidAlgebra K G) T3 :=
    @instDiagModule K _ G _ C ↥Y0 _ _ _ _ _ iY (ModuleCat.isModule Y0) smcYi
  let dT4 : Module (MonoidAlgebra K G) T4 := instDiagModule C (TensorProduct K B A)
  have hcomp3 : ∀ (r : MonoidAlgebra K G) (z : T3),
      dT3.smul r z
        = (@diagRingHom K _ G _ C ↥Y0 _ _ _ _ _ iY (ModuleCat.isModule Y0) smcYi) r z :=
    fun r z => rfl
  have hcomp4 : ∀ (r : MonoidAlgebra K G) (z : T4),
      dT4.smul r z = diagRingHom C (TensorProduct K B A) r z := fun r z => rfl
  let cnvY : @LinearEquiv K K _ _ (RingHom.id K) (RingHom.id K) _ _ T3 T4 _ _ _ _ :=
    @TensorProduct.congr K K _ _ (RingHom.id K) C ↥Y0 C ↥Y0 _ _ _ _ _ iY _ nY (RingHom.id K) _ _
      (LinearEquiv.refl K C) γY
  have hcnvY : (cnvY : T3 → T4)
      = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) C ↥Y0 C ↥Y0 _ _ _ _ _ iY _ nY
          (RingHom.id K) _ _ (LinearEquiv.refl K C) γY) := rfl
  have hctY : ∀ (a : C) (x : ↥Y0),
      (@TensorProduct.congr K K _ _ (RingHom.id K) C ↥Y0 C ↥Y0 _ _ _ _ _ iY _ nY
          (RingHom.id K) _ _ (LinearEquiv.refl K C) γY) (tm3 a x) = tm4 a x := by
    intro a x
    rw [@TensorProduct.congr_tmul K K _ _ (RingHom.id K) C ↥Y0 C ↥Y0 _ _ _ _ _ iY _ nY
        (RingHom.id K) _ _ (LinearEquiv.refl K C) γY a x, LinearEquiv.refl_apply, hγY]
  let de3 : G → T3 →ₗ[K] T3 :=
    fun m => @diagElem K _ G _ C ↥Y0 _ _ _ _ _ iY (ModuleCat.isModule Y0) smcYi m
  have hgenY : ∀ (m : G) (z : T3), cnvY ((de3 m) z)
      = (diagElem C (TensorProduct K B A) m) (cnvY z) := by
    intro m z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
        rw [show (cnvY : T3 → T4) = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) C ↥Y0 C ↥Y0
            _ _ _ _ _ iY _ nY (RingHom.id K) _ _ (LinearEquiv.refl K C) γY) from hcnvY]
        rw [hctY]
        rw [diagElem_tmul]
        rw [hctY]
        rw [diagElem_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hβY : ∀ (r : MonoidAlgebra K G) (z : T3), cnvY (dT3.smul r z) = dT4.smul r (cnvY z) := by
    intro r z
    induction r using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply]
        rw [show dT3.smul (MonoidAlgebra.single m 1) z = (de3 m) z from by
              rw [hcomp3, diagRingHom_single]
              rfl,
            show dT4.smul (MonoidAlgebra.single m 1) (cnvY z)
                = (diagElem C (TensorProduct K B A) m) (cnvY z) from by
              rw [hcomp4, diagRingHom_single]
              rfl]
        exact hgenY m z
    | add r s hr hs =>
        have hsplit1 : dT3.smul (r + s) z = dT3.smul r z + dT3.smul s z := by
          rw [hcomp3, hcomp3, hcomp3, map_add, LinearMap.add_apply]
        have hsplit2 : dT4.smul (r + s) (cnvY z) = dT4.smul r (cnvY z) + dT4.smul s (cnvY z) := by
          rw [hcomp4, hcomp4, hcomp4, map_add, LinearMap.add_apply]
        rw [hsplit1, hsplit2, cnvY.map_add, hr, hs]
    | smul c r hr =>
        have hsplit1 : dT3.smul (c • r) z = c • (dT3.smul r z) := by
          rw [hcomp3, hcomp3, diagRingHom_smul, LinearMap.smul_apply]
        have hsplit2 : dT4.smul (c • r) (cnvY z) = c • (dT4.smul r (cnvY z)) := by
          rw [hcomp4, hcomp4, diagRingHom_smul, LinearMap.smul_apply]
        rw [hsplit1, hsplit2, cnvY.map_smul, hr]
  let βX' : @LinearEquiv (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T1 T2 _ _ dT1 dT2 :=
    @LinearEquiv.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T1 T2 _ _ dT1 dT2
      (@LinearMap.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) T1 T2 _ _ dT1 dT2
        (AddHom.mk (⇑cnv) (fun x y => cnv.map_add x y)) (fun r z => hβX r z))
      (⇑cnv.symm) (fun z => cnv.left_inv z) (fun z => cnv.right_inv z)
  let βY' : @LinearEquiv (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T3 T4 _ _ dT3 dT4 :=
    @LinearEquiv.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T3 T4 _ _ dT3 dT4
      (@LinearMap.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) T3 T4 _ _ dT3 dT4
        (AddHom.mk (⇑cnvY) (fun x y => cnvY.map_add x y)) (fun r z => hβY r z))
      (⇑cnvY.symm) (fun z => cnvY.left_inv z) (fun z => cnvY.right_inv z)
  obtain ⟨e⟩ := middleIso K G A B C
  have hdT1 : dT1 = @instDiagModule K _ G _ A ↥X0 _ _ _ _ _ iX (ModuleCat.isModule X0)
      (diagTensor._proof_1 X0) :=
    congrArg (fun s => @instDiagModule K _ G _ A ↥X0 _ _ _ _ _ iX (ModuleCat.isModule X0) s)
      (Subsingleton.elim smcXi _)
  have hdT3 : dT3 = @instDiagModule K _ G _ C ↥Y0 _ _ _ _ _ iY (ModuleCat.isModule Y0)
      (diagTensor._proof_1 Y0) :=
    congrArg (fun s => @instDiagModule K _ G _ C ↥Y0 _ _ _ _ _ iY (ModuleCat.isModule Y0) s)
      (Subsingleton.elim smcYi _)
  have hL : @ModuleCat.of (MonoidAlgebra K G) _ T1 _ dT1 = L := by
    rw [hdT1]
    rfl
  have hR : @ModuleCat.of (MonoidAlgebra K G) _ T3 _ dT3 = R := by
    rw [hdT3]
    rfl
  exact ⟨(eqToIso hL.symm).trans
    (((βX'.trans (e.trans βY'.symm)).toModuleIso).trans (eqToIso hR))⟩
