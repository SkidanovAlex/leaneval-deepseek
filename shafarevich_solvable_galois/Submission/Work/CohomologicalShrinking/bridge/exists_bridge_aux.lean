import Mathlib
import Submission.Work.CohomologicalShrinking.Bridge.Final
import Submission.Work.CohomologicalShrinking.Bridge.Psi
import Submission.Work.CohomologicalShrinking.tate.Hm1Map_comp
import Submission.Work.CohomologicalShrinking.bridge.Psi_ker
import Submission.Work.CohomologicalShrinking.bridge.Psi_surjective
import Submission.Work.CohomologicalShrinking.bridge.exists_eps
import Submission.Work.CohomologicalShrinking.bridge.ThetaOn_surjective
import Submission.Work.CohomologicalShrinking.bridge.ThetaOn_augmentation_of_mem_boundaries
import Submission.Work.CohomologicalShrinking.bridge.augmentation_le_ThetaOn_boundaries
import Submission.Work.CohomologicalShrinking.bridge.ThetaOn_eq_zero_mem_boundaries

set_option linter.unusedSectionVars false
open scoped TensorProduct
namespace Work.CohomologicalShrinking.bridge

open Work.CohomologicalShrinking
open Work.Bridge
open Work.Tate

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

lemma assoc_smul {A B C : Type} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B] [SMulCommClass G (ZMod p) C]
    (γ : G) (x : (A ⊗[ZMod p] B) ⊗[ZMod p] C) :
    TensorProduct.assoc (ZMod p) A B C (γ • x) = γ • TensorProduct.assoc (ZMod p) A B C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul ab c =>
    rw [Work.Shrinking.diagTensor_smul_tmul]
    induction ab using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.assoc_tmul]
    | add x y hx hy =>
        rw [smul_add, TensorProduct.add_tmul, map_add, hx, hy]
        rw [TensorProduct.add_tmul, map_add, smul_add]
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

lemma assoc_rTensor {A A' B C : Type} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup A'] [Module (ZMod p) A'] [AddCommGroup B] [Module (ZMod p) B]
    [AddCommGroup C] [Module (ZMod p) C] (φ : A →ₗ[ZMod p] A') :
    ((TensorProduct.assoc (ZMod p) A' B C).toLinearMap).comp ((φ.rTensor B).rTensor C)
      = (φ.rTensor (B ⊗[ZMod p] C)).comp ((TensorProduct.assoc (ZMod p) A B C).toLinearMap) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul ab c =>
    induction ab using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [TensorProduct.assoc_tmul]
    | add x y hx hy =>
        rw [TensorProduct.add_tmul, map_add, hx, hy]
        rw [map_add]
  | add x y hx hy => rw [map_add, hx, hy, map_add]

noncomputable def assocHom (A B C : Type) [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C] :
    (A ⊗[ZMod p] B) ⊗[ZMod p] C →+ A ⊗[ZMod p] (B ⊗[ZMod p] C) :=
  ((TensorProduct.assoc (ZMod p) A B C).toLinearMap).toAddMonoidHom

theorem assocHom_apply {A B C : Type} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    (x : (A ⊗[ZMod p] B) ⊗[ZMod p] C) :
    assocHom (p:=p) A B C x = TensorProduct.assoc (ZMod p) A B C x := rfl

theorem assocHom_smul {A B C : Type} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B] [SMulCommClass G (ZMod p) C]
    (γ : G) (x : (A ⊗[ZMod p] B) ⊗[ZMod p] C) :
    assocHom (p:=p) A B C (γ • x) = γ • assocHom (p:=p) A B C x :=
  assoc_smul (p:=p) (G:=G) (A:=A) (B:=B) (C:=C) γ x

theorem assocHom_bijective {A B C : Type} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C] :
    Function.Bijective (assocHom (p:=p) A B C) := by
  constructor
  · intro x y h
    exact (TensorProduct.assoc (ZMod p) A B C).injective h
  · intro y
    obtain ⟨x, hx⟩ := (TensorProduct.assoc (ZMod p) A B C).surjective y
    exact ⟨x, hx⟩

noncomputable def assocHm1Equiv (A B C : Type) [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup C] [Module (ZMod p) C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [SMulCommClass G (ZMod p) A] [SMulCommClass G (ZMod p) B] [SMulCommClass G (ZMod p) C] :
    Work.Tate.Hm1 G ((A ⊗[ZMod p] B) ⊗[ZMod p] C) ≃+ Work.Tate.Hm1 G (A ⊗[ZMod p] (B ⊗[ZMod p] C)) :=
  Work.Tate.Hm1Equiv (assocHom (p:=p) A B C)
    (assocHom_smul (p:=p) (G:=G) (A:=A) (B:=B) (C:=C))
    (assocHom_bijective (p:=p) (A:=A) (B:=B) (C:=C))

lemma Hm1Map_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A]
    [DistribMulAction G B] {f g : A →+ B} (hf : ∀ γ a, f (γ•a) = γ•f a)
    (hg : ∀ γ a, g (γ•a) = γ•g a) (h : f = g) :
    Hm1Map G A B f hf = Hm1Map G A B g hg := by
  subst h
  rfl

noncomputable def GAMMA (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j m : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) ≃+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)) := by
  classical
  exact (Work.Bridge.h1Hm1Equiv (k := ZMod p) (G := G) (M := E p G m i j ⊗[ZMod p] T)
      (ThetaOn_augmentation_of_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (augmentation_le_ThetaOn_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_eq_zero_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_surjective (ZMod p) G (E p G m i j ⊗[ZMod p] T))).trans
    ((Work.Bridge.tr1 (p := p) (G := G) (E p G m i j ⊗[ZMod p] T)).trans
      (assocHm1Equiv (p:=p) (G:=G) (E p G m i j) T (augIdeal p G)))



lemma Hm1Equiv_square {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B'] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G A'] [DistribMulAction G B']
    (eA : A →+ A') (heA : ∀ g a, eA (g•a) = g•eA a) (hbeA : Function.Bijective eA)
    (eB : B →+ B') (heB : ∀ g b, eB (g•b) = g•eB b) (hbeB : Function.Bijective eB)
    (f : A →+ B) (hf : ∀ g a, f (g•a) = g•f a)
    (f' : A' →+ B') (hf' : ∀ g a', f' (g•a') = g•f' a')
    (hcomm : ∀ a, f' (eA a) = eB (f a)) (w : Hm1 G A) :
    Hm1Map G A' B' f' hf' (Hm1Equiv eA heA hbeA w)
      = Hm1Equiv eB heB hbeB (Hm1Map G A B f hf w) := by
  rw [Hm1Equiv_apply, Hm1Equiv_apply]
  change (Hm1Map G A' B' f' hf').comp (Hm1Map G A A' eA heA) w
      = (Hm1Map G B B' eB heB).comp (Hm1Map G A B f hf) w
  have hfe1 : ∀ g a, (f'.comp eA) (g•a) = g • (f'.comp eA) a := fun g a => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, heA g a, hf' g (eA a)]
  have hfe2 : ∀ g a, (eB.comp f) (g•a) = g • (eB.comp f) a := fun g a => by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hf g a, heB g (f a)]
  rw [← Work.CohomologicalShrinking.tate.Hm1Map_comp eA heA f' hf' hfe1,
      ← Work.CohomologicalShrinking.tate.Hm1Map_comp f hf eB heB hfe2]
  rw [Hm1Map_congr hfe1 hfe2 (AddMonoidHom.ext hcomm)]

theorem GAMMA_natural (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] {m n : ℕ} (Φ : OperatorMap G m n)
    (z : (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type)) :
    GAMMA p G i j n T (Work.Bridge.indH1 Φ z)
      = (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)) (GAMMA p G i j m T z) := by
  classical
  have hφ : ∀ g x, (gradedMapLin p Φ.toHom Φ.surjective i j) (g • x)
      = g • (gradedMapLin p Φ.toHom Φ.surjective i j) x :=
    fun g x => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g x
  have hφT : ∀ g x, ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (g • x)
      = g • ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) x :=
    fun g x => rTensor_equiv p (G:=G) (f:=gradedMapLin p Φ.toHom Φ.surjective i j) hφ g x
  have hnat := Work.Bridge.h1Hm1Equiv_natural (k := ZMod p) (G := G)
      (M := E p G m i j ⊗[ZMod p] T) (N := E p G n i j ⊗[ZMod p] T)
      (ThetaOn_augmentation_of_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (augmentation_le_ThetaOn_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_eq_zero_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_surjective (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_augmentation_of_mem_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (augmentation_le_ThetaOn_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (ThetaOn_eq_zero_mem_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (ThetaOn_surjective (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT z
  have hind : Work.Bridge.indH1 Φ z = (groupHomology.map (MonoidHom.id G)
      (repMor (k:=ZMod p) (G:=G) ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT) 1).hom z :=
    rfl
  have hcomm1 : ∀ a : ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
      (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
          ((Work.Bridge.cEq (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T)) a)
        = (Work.Bridge.cEq (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T))
            (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom
              hφT a) := by
    intro a
    exact (DFunLike.congr_fun (Work.Bridge.cEq_natural (p:=p) (G:=G)
        (A := E p G m i j ⊗[ZMod p] T) (B := E p G n i j ⊗[ZMod p] T)
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT) a).symm
  have hsq1 : ∀ w : Work.Tate.Hm1 G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)),
      Work.Bridge.tr1 (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T)
          (Work.Tate.Hm1Map G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
            ↥(Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
            (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom hφT)
            (Work.Tate.coindUpMap_equiv _ hφT) w)
        = Work.Tate.Hm1Map G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
            ((E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
            (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
            (fun g z => rTensor_equiv p (G:=G) (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
              hφT g z)
            (Work.Bridge.tr1 (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T) w) := by
    intro w
    exact (Hm1Equiv_square
      (eA := (Work.Bridge.cEq (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T)).toAddMonoidHom)
      (heA := Work.Bridge.cEq_equiv (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T))
      (hbeA := (Work.Bridge.cEq (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T)).bijective)
      (eB := (Work.Bridge.cEq (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T)).toAddMonoidHom)
      (heB := Work.Bridge.cEq_equiv (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T))
      (hbeB := (Work.Bridge.cEq (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T)).bijective)
      (f := Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom hφT)
      (hf := Work.Tate.coindUpMap_equiv _ hφT)
      (f' := ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
      (hf' := fun g z => rTensor_equiv p (G:=G)
        (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT g z)
      (hcomm := hcomm1) w).symm
  have hcomm2 : ∀ u : (E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G,
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
          (assocHom (p:=p) (E p G m i j) T (augIdeal p G) u)
        = assocHom (p:=p) (E p G n i j) T (augIdeal p G)
            ((((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G)) u) := by
    intro u
    rw [assocHom_apply]
    exact (congrArg (fun h => h u)
      (assoc_rTensor (p:=p) (A:=E p G m i j) (A':=E p G n i j) (B:=T)
        (C:=augIdeal p G) (gradedMapLin p Φ.toHom Φ.surjective i j))).symm
  have hsq2 : ∀ u : Work.Tate.Hm1 G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G),
      (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
          (Work.Tate.Hm1Map G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
            ((E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
            (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
            (fun g z => rTensor_equiv p (G:=G)
              (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT g z) u)
        = Work.Tate.Hm1Map G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
            (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
            ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
            (fun g z => rTensor_equiv p (G:=G)
              (f:=gradedMapLin p Φ.toHom Φ.surjective i j) hφ g z)
            ((assocHm1Equiv (p:=p) (G:=G) (E p G m i j) T (augIdeal p G)) u) := by
    intro u
    exact (Hm1Equiv_square
      (eA := assocHom (p:=p) (E p G m i j) T (augIdeal p G))
      (heA := assocHom_smul (p:=p) (G:=G) (A:=E p G m i j) (B:=T) (C:=augIdeal p G))
      (hbeA := assocHom_bijective (p:=p) (A:=E p G m i j) (B:=T) (C:=augIdeal p G))
      (eB := assocHom (p:=p) (E p G n i j) T (augIdeal p G))
      (heB := assocHom_smul (p:=p) (G:=G) (A:=E p G n i j) (B:=T) (C:=augIdeal p G))
      (hbeB := assocHom_bijective (p:=p) (A:=E p G n i j) (B:=T) (C:=augIdeal p G))
      (f := (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G)))
      (hf := fun g z => rTensor_equiv p (G:=G)
        (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT g z)
      (f' := (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
      (hf' := fun g z => rTensor_equiv p (G:=G)
        (f:=gradedMapLin p Φ.toHom Φ.surjective i j) hφ g z)
      (hcomm := hcomm2) u).symm
  let hEqM : (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) ≃+
      Work.Tate.Hm1 G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T)) :=
    Work.Bridge.h1Hm1Equiv (k:=ZMod p) (G:=G) (M := E p G m i j ⊗[ZMod p] T)
      (ThetaOn_augmentation_of_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (augmentation_le_ThetaOn_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_eq_zero_mem_boundaries (ZMod p) G (E p G m i j ⊗[ZMod p] T))
      (ThetaOn_surjective (ZMod p) G (E p G m i j ⊗[ZMod p] T))
  let hEqN : (↑(groupHomology.H1 (flowRepG p G n i j T)) : Type) ≃+
      Work.Tate.Hm1 G ↥(Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T)) :=
    Work.Bridge.h1Hm1Equiv (k:=ZMod p) (G:=G) (M := E p G n i j ⊗[ZMod p] T)
      (ThetaOn_augmentation_of_mem_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (augmentation_le_ThetaOn_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (ThetaOn_eq_zero_mem_boundaries (ZMod p) G (E p G n i j ⊗[ZMod p] T))
      (ThetaOn_surjective (ZMod p) G (E p G n i j ⊗[ZMod p] T))
  have hstep : hEqN (Work.Bridge.indH1 Φ z)
      = Work.Tate.Hm1Map G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
        ↥(Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
        (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom hφT)
        (Work.Tate.coindUpMap_equiv _ hφT) (hEqM z) :=
    (congrArg (fun w => hEqN w) hind).trans hnat.symm
  have e1 : (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
        (Work.Bridge.tr1 (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T) (hEqN (Work.Bridge.indH1 Φ z)))
      = (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
        (Work.Bridge.tr1 (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T)
          (Work.Tate.Hm1Map G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
            ↥(Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
            (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom hφT)
            (Work.Tate.coindUpMap_equiv _ hφT) (hEqM z))) :=
    congrArg (fun x => (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
      (Work.Bridge.tr1 (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T) x)) hstep
  have e2 : (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
        (Work.Bridge.tr1 (p:=p) (G:=G) (E p G n i j ⊗[ZMod p] T)
          (Work.Tate.Hm1Map G ↥(Work.Tate.coindUp G (E p G m i j ⊗[ZMod p] T))
            ↥(Work.Tate.coindUp G (E p G n i j ⊗[ZMod p] T))
            (Work.Tate.coindUpMap ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).toAddMonoidHom hφT)
            (Work.Tate.coindUpMap_equiv _ hφT) (hEqM z)))
      = (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
        (Work.Tate.Hm1Map G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
          ((E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
          (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
          (fun g zz => rTensor_equiv p (G:=G)
            (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT g zz)
          (Work.Bridge.tr1 (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T) (hEqM z))) :=
    congrArg (fun x => (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G)) x)
      (hsq1 (hEqM z))
  have e3 : (assocHm1Equiv (p:=p) (G:=G) (E p G n i j) T (augIdeal p G))
        (Work.Tate.Hm1Map G ((E p G m i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
          ((E p G n i j ⊗[ZMod p] T) ⊗[ZMod p] augIdeal p G)
          (((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T).rTensor (augIdeal p G))
          (fun g zz => rTensor_equiv p (G:=G)
            (f:=(gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) hφT g zz)
          (Work.Bridge.tr1 (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T) (hEqM z)))
      = Work.Tate.Hm1Map G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          (E p G n i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
          ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor (T ⊗[ZMod p] augIdeal p G))
          (fun g zz => rTensor_equiv p (G:=G)
            (f:=gradedMapLin p Φ.toHom Φ.surjective i j) hφ g zz)
          ((assocHm1Equiv (p:=p) (G:=G) (E p G m i j) T (augIdeal p G))
            (Work.Bridge.tr1 (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T) (hEqM z))) :=
    hsq2 (Work.Bridge.tr1 (p:=p) (G:=G) (E p G m i j ⊗[ZMod p] T) (hEqM z))
  exact e1.trans (e2.trans e3)

theorem exists_bridge_aux (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ γ : ∀ m : ℕ, (↑(groupHomology.H1 (Work.CohomologicalShrinking.flowRepG p G m i j T)) : Type) →+
      Work.Tate.Hm1 G (TensorProduct (ZMod p) (Work.CohomologicalShrinking.E p G m i j)
        (TensorProduct (ZMod p) T (Work.CohomologicalShrinking.augIdeal p G))),
      (∀ m, Function.Injective (γ m)) ∧ (∀ m, Function.Surjective (γ m)) ∧
      (∀ ⦃m n : ℕ⦄ (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
        (y : (↑(groupHomology.H1 (Work.CohomologicalShrinking.flowRep p G m i j T)) : Type)),
        (Φ.hm1Map p G (TensorProduct (ZMod p) T (Work.CohomologicalShrinking.augIdeal p G)))
            (γ m (Work.CohomologicalShrinking.flowHSβ p G i j T m y))
          = γ n (Work.CohomologicalShrinking.flowHSβ p G i j T n
              (Work.CohomologicalShrinking.flowZMap (p := p) G i j Φ T y))) := by
  classical
  choose eps heps using fun m => exists_eps p G i j T m
  refine Work.Bridge.exists_bridge_of_data (p := p) (G := G) (i := i) (j := j) (T := T)
    (fun m => GAMMA p G i j m T) ?_ eps ?_
  · intro m n Φ z
    exact GAMMA_natural p G i j T Φ z
  · intro m x
    exact heps m x

end Work.CohomologicalShrinking.bridge
