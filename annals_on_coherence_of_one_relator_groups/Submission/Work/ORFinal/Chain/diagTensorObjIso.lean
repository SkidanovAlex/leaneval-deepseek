import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORHomAlg.JL52.middleIsoCat

namespace Work.ORFinal.Chain

open CategoryTheory
open scoped TensorProduct

universe u

/-- **The object of `diagTensor M` at a `K[G]`-module `N`, with `N` carrying the `K`-structure
induced by its `K[G]`-structure, agrees with the diagonal tensor product `M ⊗_K N`.**

Concretely: the functor `diagTensor M` sends `X ↦ M ⊗_K X` where the `K`-module structure on
`↥X` is `algebraMap K K[G] c • x` (the canonical one carried by an object of `ModuleCat (K[G])`),
while `ModuleCat.of (K[G]) (M ⊗_K N)` uses the given `K`-module structure on `N`.  The two agree
because the given structures satisfy `IsScalarTower K K[G] N`; the required `K[G]`-linear
isomorphism is `id_M ⊗ γ` with `γ` the identity linear equivalence between the two `K`-module
structures on `N`. -/
theorem diagTensorObjIso (K : Type u) [Field K] (G : Type u) [Group G]
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [SMulCommClass K (MonoidAlgebra K G) M]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] [SMulCommClass K (MonoidAlgebra K G) N] :
    Nonempty ((Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).obj
        (ModuleCat.of (MonoidAlgebra K G) N)
      ≅ ModuleCat.of (MonoidAlgebra K G) (TensorProduct K M N)) := by
  -- The `K[G]`-module `N` as an object of `ModuleCat (K[G])`, and the two objects compared.
  let X : ModuleCat (MonoidAlgebra K G) := ModuleCat.of (MonoidAlgebra K G) N
  let L : ModuleCat (MonoidAlgebra K G) :=
    (Work.ORHomAlg.JL52.diagTensor (K := K) (G := G) M).obj X
  let Rl : ModuleCat (MonoidAlgebra K G) :=
    ModuleCat.of (MonoidAlgebra K G) (TensorProduct K M N)
  change Nonempty (L ≅ Rl)
  -- The `K`-module structure on `N` given by the hypothesis, and the `K[G]`-module structure.
  let nX : Module K N := (inferInstance : Module K N)
  let gR : Module (MonoidAlgebra K G) N := (inferInstance : Module (MonoidAlgebra K G) N)
  -- The `K`-module structure `x ↦ algebraMap K K[G] c • x` (the one carried by `ModuleCat`)
  -- agrees with the given one, by `IsScalarTower K K[G] N`.
  have hmap : ∀ (c : K) (m : N),
      (Work.ORHomAlg.JL52.instModuleCatK X).smul c m = c • m := by
    intro c m
    rw [show (Work.ORHomAlg.JL52.instModuleCatK X).smul c m
        = (algebraMap K (MonoidAlgebra K G) c) • m from rfl]
    rw [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc, one_smul]
  -- `SMulCommClass` for the two `K`-structures.
  let smcXi : @SMulCommClass K (MonoidAlgebra K G) N
      (Work.ORHomAlg.JL52.instModuleCatK X).toSMul gR.toSMul :=
    @IsScalarTower.to_smulCommClass K _ (MonoidAlgebra K G) _ _ N _ gR
      (Work.ORHomAlg.JL52.instModuleCatK X) (Work.ORHomAlg.JL52.instIsScalarTowerCatK X)
  let smcN : @SMulCommClass K (MonoidAlgebra K G) N nX.toSMul gR.toSMul :=
    (inferInstance : SMulCommClass K (MonoidAlgebra K G) N)
  -- The two tensor products, over the two `K`-structures on `N`.
  let T1 : Type u := @TensorProduct K _ M N _ _ _ (Work.ORHomAlg.JL52.instModuleCatK X)
  let T2 : Type u := @TensorProduct K _ M N _ _ _ nX
  -- The two diagonal `K[G]`-module structures.
  let dT1 : Module (MonoidAlgebra K G) T1 :=
    @Work.ORHomAlg.JL52.instDiagModule K _ G _ M N _ _ _ _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi
  let dT2 : Module (MonoidAlgebra K G) T2 :=
    @Work.ORHomAlg.JL52.instDiagModule K _ G _ M N _ _ _ _ _ nX gR smcN
  have hcomp1 : ∀ (r : MonoidAlgebra K G) (z : T1),
      dT1.smul r z
        = (@Work.ORHomAlg.JL52.diagRingHom K _ G _ M N _ _ _ _ _
            (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi) r z := fun r z => rfl
  have hcomp2 : ∀ (r : MonoidAlgebra K G) (z : T2),
      dT2.smul r z
        = (@Work.ORHomAlg.JL52.diagRingHom K _ G _ M N _ _ _ _ _ nX gR smcN) r z :=
    fun r z => rfl
  -- The identity linear equivalence between the two `K`-module structures on `N`.
  let γX : @LinearEquiv K K _ _ (RingHom.id K) (RingHom.id K) _ _ N N _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) nX :=
    @LinearEquiv.mk K K _ _ (RingHom.id K) (RingHom.id K) _ _ N N _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) nX
      (@LinearMap.mk K K _ _ (RingHom.id K) N N _ _
        (Work.ORHomAlg.JL52.instModuleCatK X) nX
        (AddHom.mk (fun m => m) (fun _ _ => rfl)) (fun c m => hmap c m))
      (fun m => m) (fun _ => rfl) (fun _ => rfl)
  have hγX : ∀ m : N, γX m = m := fun m => rfl
  -- `id_M ⊗ γ`, an isomorphism of `K`-modules `T1 ≃ₗ[K] T2`.
  let cnv := @TensorProduct.congr K K _ _ (RingHom.id K) M N M N _ _ _ _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) _ nX (RingHom.id K) _ _
      (LinearEquiv.refl K M) γX
  have hcnv : (cnv : T1 → T2)
      = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) M N M N _ _ _ _ _
          (Work.ORHomAlg.JL52.instModuleCatK X) _ nX (RingHom.id K) _ _
          (LinearEquiv.refl K M) γX) := rfl
  have hct : ∀ (a : M) (x : N),
      (@TensorProduct.congr K K _ _ (RingHom.id K) M N M N _ _ _ _ _
          (Work.ORHomAlg.JL52.instModuleCatK X) _ nX (RingHom.id K) _ _
          (LinearEquiv.refl K M) γX)
          (@TensorProduct.tmul K _ M N _ _ _ (Work.ORHomAlg.JL52.instModuleCatK X) a x)
        = @TensorProduct.tmul K _ M N _ _ _ nX a x := by
    intro a x
    rw [@TensorProduct.congr_tmul K K _ _ (RingHom.id K) M N M N _ _ _ _ _
        (Work.ORHomAlg.JL52.instModuleCatK X) _ nX (RingHom.id K) _ _
        (LinearEquiv.refl K M) γX a x, LinearEquiv.refl_apply, hγX]
  -- `id_M ⊗ γ` respects the diagonal actions of `G`.
  have hgen : ∀ (m : G) (z : T1),
      cnv ((@Work.ORHomAlg.JL52.diagElem K _ G _ M N _ _ _ _ _
            (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi m) z)
      = (@Work.ORHomAlg.JL52.diagElem K _ G _ M N _ _ _ _ _ nX gR smcN m) (cnv z) := by
    intro m z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
        rw [show (cnv : T1 → T2) = ⇑(@TensorProduct.congr K K _ _ (RingHom.id K) M N M N
            _ _ _ _ _ (Work.ORHomAlg.JL52.instModuleCatK X) _ nX (RingHom.id K) _ _
            (LinearEquiv.refl K M) γX) from hcnv]
        rw [@Work.ORHomAlg.JL52.diagElem_tmul K _ G _ M N _ _ _ _ _
          (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi m a x]
        simp only [hct]
        rw [@Work.ORHomAlg.JL52.diagElem_tmul K _ G _ M N _ _ _ _ _ nX gR smcN m a x]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- `id_M ⊗ γ` is `K[G]`-linear for the diagonal structures.
  have hβX : ∀ (r : MonoidAlgebra K G) (z : T1), cnv (dT1.smul r z) = dT2.smul r (cnv z) := by
    intro r z
    induction r using MonoidAlgebra.induction_on with
    | of m =>
        rw [MonoidAlgebra.of_apply]
        rw [show dT1.smul (MonoidAlgebra.single m 1) z
              = (@Work.ORHomAlg.JL52.diagElem K _ G _ M N _ _ _ _ _
                  (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi m) z from by
              rw [hcomp1, @Work.ORHomAlg.JL52.diagRingHom_single K _ G _ M N _ _ _ _ _
                  (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi m]
              rfl,
            show dT2.smul (MonoidAlgebra.single m 1) (cnv z)
              = (@Work.ORHomAlg.JL52.diagElem K _ G _ M N _ _ _ _ _ nX gR smcN m) (cnv z) from by
              rw [hcomp2, @Work.ORHomAlg.JL52.diagRingHom_single K _ G _ M N _ _ _ _ _
                  nX gR smcN m]
              rfl]
        exact hgen m z
    | add r s hr hs =>
        have hsplit1 : dT1.smul (r + s) z = dT1.smul r z + dT1.smul s z := by
          rw [hcomp1, hcomp1, hcomp1, map_add, LinearMap.add_apply]
        have hsplit2 : dT2.smul (r + s) (cnv z) = dT2.smul r (cnv z) + dT2.smul s (cnv z) := by
          rw [hcomp2, hcomp2, hcomp2, map_add, LinearMap.add_apply]
        rw [hsplit1, hsplit2, map_add, hr, hs]
    | smul c r hr =>
        have hsplit1 : dT1.smul (c • r) z = c • (dT1.smul r z) := by
          rw [hcomp1, hcomp1, @Work.ORHomAlg.JL52.diagRingHom_smul K _ G _ M N _ _ _ _ _
              (Work.ORHomAlg.JL52.instModuleCatK X) gR smcXi c r, LinearMap.smul_apply]
        have hsplit2 : dT2.smul (c • r) (cnv z) = c • (dT2.smul r (cnv z)) := by
          rw [hcomp2, hcomp2, @Work.ORHomAlg.JL52.diagRingHom_smul K _ G _ M N _ _ _ _ _
              nX gR smcN c r, LinearMap.smul_apply]
        rw [hsplit1, hsplit2, cnv.map_smul, hr]
  -- Package `id_M ⊗ γ` as a `K[G]`-linear equivalence `T1 ≃ₗ[K[G]] T2`.
  let βX' : @LinearEquiv (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T1 T2 _ _ dT1 dT2 :=
    @LinearEquiv.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) (RingHom.id _) _ _
      T1 T2 _ _ dT1 dT2
      (@LinearMap.mk (MonoidAlgebra K G) (MonoidAlgebra K G) _ _ (RingHom.id _) T1 T2 _ _ dT1 dT2
        (AddHom.mk (⇑cnv) (fun x y => cnv.map_add x y)) (fun r z => hβX r z))
      (⇑cnv.symm) (fun z => cnv.left_inv z) (fun z => cnv.right_inv z)
  -- `dT1` is the module structure of the object `L` (the `SMulCommClass` witness is a proof
  -- of a proposition, so it may be replaced by the one used by `diagTensor`).
  have hdT1 : dT1 = @Work.ORHomAlg.JL52.instDiagModule K _ G _ M N _ _ _ _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) gR (Work.ORHomAlg.JL52.diagTensor._proof_1 X) :=
    congrArg (fun s => @Work.ORHomAlg.JL52.instDiagModule K _ G _ M N _ _ _ _ _
      (Work.ORHomAlg.JL52.instModuleCatK X) gR s) (Subsingleton.elim smcXi _)
  have hL : @ModuleCat.of (MonoidAlgebra K G) _ T1 _ dT1 = L := by
    rw [hdT1]
    rfl
  have hR : @ModuleCat.of (MonoidAlgebra K G) _ T2 _ dT2 = Rl := by
    rfl
  exact ⟨(eqToIso hL.symm).trans (βX'.toModuleIso.trans (eqToIso hR))⟩

end Work.ORFinal.Chain
