import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Submission.Work.CohomologicalShrinking.Models
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.shiftTensor

open scoped TensorProduct

universe uG uM uA

set_option maxHeartbeats 800000

variable {p : ℕ}

/-! ## Auxiliary: `TensorPower.mulEquiv` on pure tensors

`TensorPower.mulEquiv : ⨂^n M ⊗ ⨂^m M ≃ₗ ⨂^(n+m) M` is the concatenation equivalence;
we record its value on pure tensors in both directions. -/

lemma mulEquiv_tprod {M : Type uM} [AddCommGroup M] [Module (ZMod p) M]
    {n m : ℕ} (a : Fin n → M) (b : Fin m → M) :
    TensorPower.mulEquiv ((PiTensorProduct.tprod (ZMod p) a) ⊗ₜ[ZMod p]
        (PiTensorProduct.tprod (ZMod p) b)) =
      PiTensorProduct.tprod (ZMod p) (fun i => Sum.elim a b (finSumFinEquiv.symm i)) := by
  simp only [TensorPower.mulEquiv, LinearEquiv.trans_apply, PiTensorProduct.tmulEquiv_apply,
    PiTensorProduct.reindex_tprod]

lemma mulEquiv_symm_tprod {M : Type uM} [AddCommGroup M] [Module (ZMod p) M]
    {n m : ℕ} (c : Fin (n + m) → M) :
    (TensorPower.mulEquiv (R := ZMod p) (M := M) (n := n) (m := m)).symm
        (PiTensorProduct.tprod (ZMod p) c) =
      (PiTensorProduct.tprod (ZMod p) (fun i : Fin n => c (finSumFinEquiv (Sum.inl i)))) ⊗ₜ[ZMod p]
        (PiTensorProduct.tprod (ZMod p) (fun i : Fin m => c (finSumFinEquiv (Sum.inr i)))) := by
  rw [TensorPower.mulEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_symm, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquiv_symm_apply, Equiv.symm_symm]

/-! ## The `G`-equivariant identification `(M ⊗ M) ⊗ M ≃ ⨂^3 M` -/

/-- `M ≃ₗ ⨂^1 M`, the canonical identification. -/
noncomputable def tp1 (p : ℕ) (M : Type uM) [AddCommGroup M] [Module (ZMod p) M] :
    M ≃ₗ[ZMod p] TensorPower (ZMod p) 1 M :=
  (PiTensorProduct.subsingletonEquiv (R := ZMod p) (s := fun _ : Fin 1 => M) 0).symm

/-- `M ⊗ M ≃ₗ ⨂^2 M`. -/
noncomputable def tp2 (p : ℕ) (M : Type uM) [AddCommGroup M] [Module (ZMod p) M] :
    M ⊗[ZMod p] M ≃ₗ[ZMod p] TensorPower (ZMod p) 2 M :=
  (TensorProduct.congr (tp1 p M) (tp1 p M)).trans
    (TensorPower.mulEquiv (R := ZMod p) (M := M) (n := 1) (m := 1))

/-- `(M ⊗ M) ⊗ M ≃ₗ ⨂^3 M`, the associator to the third tensor power. -/
noncomputable def kappa (p : ℕ) (M : Type uM) [AddCommGroup M] [Module (ZMod p) M] :
    (M ⊗[ZMod p] M) ⊗[ZMod p] M ≃ₗ[ZMod p] TensorPower (ZMod p) 3 M :=
  (TensorProduct.congr (tp2 p M) (tp1 p M)).trans
    (TensorPower.mulEquiv (R := ZMod p) (M := M) (n := 2) (m := 1))

/-! ## Equivariance of the ingredients -/

section Equivariance

variable {G : Type uG} [Group G]

/-- If `e.symm` commutes with the `G`-actions, so does `e`. -/
lemma equivariant_of_symm {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module (ZMod p) X]
    [Module (ZMod p) Y] [DistribMulAction G X] [DistribMulAction G Y]
    (e : X ≃ₗ[ZMod p] Y) (h : ∀ (γ : G) (y : Y), e.symm (γ • y) = γ • e.symm y)
    (γ : G) (x : X) : e (γ • x) = γ • e x := by
  have hx : γ • x = e.symm (γ • e x) := by
    rw [h γ (e x), LinearEquiv.symm_apply_apply]
  rw [hx, LinearEquiv.apply_symm_apply]

/-- `TensorProduct.map` of two `G`-equivariant maps is `G`-equivariant for the diagonal actions. -/
lemma map_equivariant {X X' Y Y' : Type*} [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
    [AddCommGroup X'] [Module (ZMod p) X'] [DistribMulAction G X'] [SMulCommClass G (ZMod p) X']
    [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y] [SMulCommClass G (ZMod p) Y]
    [AddCommGroup Y'] [Module (ZMod p) Y'] [DistribMulAction G Y'] [SMulCommClass G (ZMod p) Y']
    (f : X →ₗ[ZMod p] X') (g : Y →ₗ[ZMod p] Y')
    (hf : ∀ (γ : G) (x : X), f (γ • x) = γ • f x)
    (hg : ∀ (γ : G) (y : Y), g (γ • y) = γ • g y)
    (γ : G) (x : X ⊗[ZMod p] Y) :
    TensorProduct.map f g (γ • x) = γ • TensorProduct.map f g x := by
  rw [Work.Shrinking.diagTensor_smul_def (p := p) (x := x),
      Work.Shrinking.diagTensor_smul_def (p := p) (x := TensorProduct.map f g x)]
  have h1 : f.comp (Work.Shrinking.actLinear (p := p) (G := G) γ) =
      (Work.Shrinking.actLinear (p := p) (G := G) γ).comp f := LinearMap.ext (hf γ)
  have h2 : g.comp (Work.Shrinking.actLinear (p := p) (G := G) γ) =
      (Work.Shrinking.actLinear (p := p) (G := G) γ).comp g := LinearMap.ext (hg γ)
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, h1, h2, TensorProduct.map_comp,
    LinearMap.comp_apply]

/-- `LinearEquiv.rTensor` of a `G`-equivariant equivalence is `G`-equivariant. -/
lemma rTensor_equivariant {N P W : Type*} [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [AddCommGroup P] [Module (ZMod p) P] [DistribMulAction G P] [SMulCommClass G (ZMod p) P]
    [AddCommGroup W] [Module (ZMod p) W] [DistribMulAction G W] [SMulCommClass G (ZMod p) W]
    (e : N ≃ₗ[ZMod p] P) (he : ∀ (γ : G) (n : N), e (γ • n) = γ • e n)
    (γ : G) (z : N ⊗[ZMod p] W) :
    LinearEquiv.rTensor W e (γ • z) = γ • LinearEquiv.rTensor W e z :=
  map_equivariant (e : N →ₗ[ZMod p] P) (LinearMap.id : W →ₗ[ZMod p] W) he (fun γ z => rfl) γ z

/-- The associator `(X ⊗ Y) ⊗ Z ≃ X ⊗ (Y ⊗ Z)` is `G`-equivariant. -/
lemma assoc_equivariant {X Y Z : Type*}
    [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y] [SMulCommClass G (ZMod p) Y]
    [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z] [SMulCommClass G (ZMod p) Z]
    (γ : G) (x : (X ⊗[ZMod p] Y) ⊗[ZMod p] Z) :
    TensorProduct.assoc (ZMod p) X Y Z (γ • x) = γ • TensorProduct.assoc (ZMod p) X Y Z x := by
  rw [Work.Shrinking.diagTensor_smul_def (p := p) (x := x),
      Work.Shrinking.diagTensor_smul_def (p := p) (x := TensorProduct.assoc (ZMod p) X Y Z x)]
  exact (LinearMap.congr_fun (TensorProduct.map_map_comp_assoc_eq
    (Work.Shrinking.actLinear (p := p) (G := G) γ)
    (Work.Shrinking.actLinear (p := p) (G := G) γ)
    (Work.Shrinking.actLinear (p := p) (G := G) γ)) x).symm

/-- `TensorProduct.congr` of two `G`-equivariant equivalences is `G`-equivariant. -/
lemma congr_equivariant {X X' Y Y' : Type*} [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
    [AddCommGroup X'] [Module (ZMod p) X'] [DistribMulAction G X'] [SMulCommClass G (ZMod p) X']
    [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y] [SMulCommClass G (ZMod p) Y]
    [AddCommGroup Y'] [Module (ZMod p) Y'] [DistribMulAction G Y'] [SMulCommClass G (ZMod p) Y']
    (f : X ≃ₗ[ZMod p] X') (g : Y ≃ₗ[ZMod p] Y')
    (hf : ∀ (γ : G) (x : X), f (γ • x) = γ • f x)
    (hg : ∀ (γ : G) (y : Y), g (γ • y) = γ • g y)
    (γ : G) (x : X ⊗[ZMod p] Y) :
    TensorProduct.congr f g (γ • x) = γ • TensorProduct.congr f g x :=
  map_equivariant (f : X →ₗ[ZMod p] X') (g : Y →ₗ[ZMod p] Y') hf hg γ x

/-- Composition of two `G`-equivariant equivalences. -/
lemma trans_equivariant {X Y Z : Type*} [AddCommGroup X] [Module (ZMod p) X]
    [DistribMulAction G X] [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y]
    [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    (e : X ≃ₗ[ZMod p] Y) (f : Y ≃ₗ[ZMod p] Z)
    (he : ∀ (γ : G) (x : X), e (γ • x) = γ • e x)
    (hf : ∀ (γ : G) (y : Y), f (γ • y) = γ • f y) (γ : G) (x : X) :
    (e.trans f) (γ • x) = γ • (e.trans f) x := by
  rw [LinearEquiv.trans_apply, he γ x, hf γ (e x), LinearEquiv.trans_apply]

/-- `tp1` is `G`-equivariant. -/
lemma tp1_equivariant (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (γ : G) (m : M) :
    tp1 p M (γ • m) = γ • tp1 p M m := by
  simp only [tp1]
  rw [PiTensorProduct.subsingletonEquiv_symm_apply', PiTensorProduct.subsingletonEquiv_symm_apply',
    Work.Shrinking.smul_tprod_tensorPower 1 γ]

/-- `TensorPower.mulEquiv.symm` is `G`-equivariant (diagonal actions on both sides). -/
lemma mulEquiv_symm_equivariant (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    {n m : ℕ} (γ : G) (z : TensorPower (ZMod p) (n + m) M) :
    (TensorPower.mulEquiv (R := ZMod p) (M := M) (n := n) (m := m)).symm (γ • z) =
      γ • (TensorPower.mulEquiv (R := ZMod p) (M := M) (n := n) (m := m)).symm z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [show γ • (r • PiTensorProduct.tprod (ZMod p) f)
          = r • (γ • PiTensorProduct.tprod (ZMod p) f) from smul_comm γ r _,
      Work.Shrinking.smul_tprod_tensorPower (n + m) γ f, LinearEquiv.map_smul,
      mulEquiv_symm_tprod]
    rw [LinearEquiv.map_smul, mulEquiv_symm_tprod]
    rw [show γ • (r • ((PiTensorProduct.tprod (ZMod p)
              (fun i : Fin n => f (finSumFinEquiv (Sum.inl i)))) ⊗ₜ[ZMod p]
            (PiTensorProduct.tprod (ZMod p) (fun i : Fin m => f (finSumFinEquiv (Sum.inr i))))))
          = r • (γ • ((PiTensorProduct.tprod (ZMod p)
              (fun i : Fin n => f (finSumFinEquiv (Sum.inl i)))) ⊗ₜ[ZMod p]
            (PiTensorProduct.tprod (ZMod p) (fun i : Fin m => f (finSumFinEquiv (Sum.inr i))))))
          from smul_comm γ r _]
    rw [Work.Shrinking.diagTensor_smul_tmul,
        Work.Shrinking.smul_tprod_tensorPower n γ, Work.Shrinking.smul_tprod_tensorPower m γ]
  | add x y ihx ihy =>
    rw [smul_add, map_add, map_add, ihx, ihy, smul_add]

/-- `TensorPower.mulEquiv` is `G`-equivariant (diagonal actions on both sides). -/
lemma mulEquiv_equivariant (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    {n m : ℕ} (γ : G) (y : TensorPower (ZMod p) n M ⊗[ZMod p] TensorPower (ZMod p) m M) :
    TensorPower.mulEquiv (γ • y) = γ • TensorPower.mulEquiv y :=
  equivariant_of_symm _ (fun γ z => mulEquiv_symm_equivariant M γ z) γ y

/-- `tp2` is `G`-equivariant. -/
lemma tp2_equivariant (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (γ : G) (y : M ⊗[ZMod p] M) :
    tp2 p M (γ • y) = γ • tp2 p M y := by
  simp only [tp2]
  exact trans_equivariant _ _
    (congr_equivariant _ _ (fun γ m => tp1_equivariant M γ m)
      (fun γ m => tp1_equivariant M γ m)) (fun γ z => mulEquiv_equivariant M γ z) γ y

/-- `kappa` is `G`-equivariant. -/
lemma kappa_equivariant (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (γ : G)
    (y : (M ⊗[ZMod p] M) ⊗[ZMod p] M) :
    kappa p M (γ • y) = γ • kappa p M y := by
  simp only [kappa]
  exact trans_equivariant _ _
    (congr_equivariant _ _ (fun γ m => tp2_equivariant M γ m)
      (fun γ m => tp1_equivariant M γ m)) (fun γ z => mulEquiv_equivariant M γ z) γ y

end Equivariance

/-! ## The main construction -/

/-- The associator `((A ⊗ M) ⊗ M) ⊗ M ≃ₗ A ⊗ ⨂^3 M`. -/
noncomputable def rho (p : ℕ) (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    (A : Type uA) [AddCommGroup A] [Module (ZMod p) A] :
    ((A ⊗[ZMod p] M) ⊗[ZMod p] M) ⊗[ZMod p] M ≃ₗ[ZMod p]
      A ⊗[ZMod p] TensorPower (ZMod p) 3 M :=
  (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)).trans
    ((TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M).trans
      (TensorProduct.congr (LinearEquiv.refl (ZMod p) A) (kappa p M)))

/-- Naturality of the associator `(X ⊗ N) ⊗ M ≃ X ⊗ (N ⊗ M)` in the first variable. -/
lemma rTensor_assoc_nat (M : Type uM) [AddCommGroup M] [Module (ZMod p) M]
    {A B N : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup N] [Module (ZMod p) N]
    (φ : A →ₗ[ZMod p] B) :
    (TensorProduct.assoc (ZMod p) B N M :
        ((B ⊗[ZMod p] N) ⊗[ZMod p] M) →ₗ[ZMod p] (B ⊗[ZMod p] (N ⊗[ZMod p] M))) ∘ₗ
        LinearMap.rTensor M (LinearMap.rTensor N φ) =
      LinearMap.rTensor (N ⊗[ZMod p] M) φ ∘ₗ
        (TensorProduct.assoc (ZMod p) A N M :
          ((A ⊗[ZMod p] N) ⊗[ZMod p] M) →ₗ[ZMod p] (A ⊗[ZMod p] (N ⊗[ZMod p] M))) := by
  have h := (TensorProduct.map_map_comp_assoc_eq (φ : A →ₗ[ZMod p] B)
      (LinearMap.id : N →ₗ[ZMod p] N) (LinearMap.id : M →ₗ[ZMod p] M)).symm
  simp only [TensorProduct.map_id] at h
  exact h

/-- Naturality of `id ⊗ κ` in the first variable. -/
lemma congr_refl_nat {A B Z W : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [AddCommGroup Z] [Module (ZMod p) Z]
    [AddCommGroup W] [Module (ZMod p) W] (κ : Z ≃ₗ[ZMod p] W) (φ : A →ₗ[ZMod p] B) :
    LinearMap.rTensor W φ ∘ₗ
        (TensorProduct.congr (LinearEquiv.refl (ZMod p) A) κ :
          (A ⊗[ZMod p] Z) →ₗ[ZMod p] (A ⊗[ZMod p] W)) =
      (TensorProduct.congr (LinearEquiv.refl (ZMod p) B) κ :
          (B ⊗[ZMod p] Z) →ₗ[ZMod p] (B ⊗[ZMod p] W)) ∘ₗ
        LinearMap.rTensor Z φ := by
  simp only [LinearEquiv.refl_toLinearMap, TensorProduct.toLinearMap_congr, LinearMap.rTensor_def]
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
    LinearMap.id_comp, LinearMap.comp_id]

section Main

variable {G : Type uG} [Group G]
variable (M : Type uM) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
  [SMulCommClass G (ZMod p) M]

/-- `rho` is `G`-equivariant. -/
lemma rho_equivariant (A : Type uA) [AddCommGroup A] [Module (ZMod p) A]
    [DistribMulAction G A] [SMulCommClass G (ZMod p) A] (γ : G)
    (x : ((A ⊗[ZMod p] M) ⊗[ZMod p] M) ⊗[ZMod p] M) :
    rho p M A (γ • x) = γ • rho p M A x := by
  have h1 : LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) (γ • x) =
      γ • LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) x :=
    rTensor_equivariant (TensorProduct.assoc (ZMod p) A M M)
      (fun γ z => assoc_equivariant γ z) γ x
  have h2 : TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M
        (γ • (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) x)) =
      γ • TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M
        (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) x) :=
    assoc_equivariant γ _
  have h3 : TensorProduct.congr (LinearEquiv.refl (ZMod p) A) (kappa p M)
        (γ • (TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M
          (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) x))) =
      γ • TensorProduct.congr (LinearEquiv.refl (ZMod p) A) (kappa p M)
        (TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M
          (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M) x)) :=
    congr_equivariant _ _ (fun γ a => rfl) (fun γ w => kappa_equivariant M γ w) γ _
  simp only [rho, LinearEquiv.trans_apply]
  rw [h1, h2, h3]

/-- Naturality of `rho` in the variable `A`. -/
lemma rho_naturality (A : Type uA) [AddCommGroup A] [Module (ZMod p) A]
    (B : Type uA) [AddCommGroup B] [Module (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (x : ((A ⊗[ZMod p] M) ⊗[ZMod p] M) ⊗[ZMod p] M) :
    rho p M B (LinearMap.rTensor M (LinearMap.rTensor M (LinearMap.rTensor M φ)) x) =
      LinearMap.rTensor (TensorPower (ZMod p) 3 M) φ (rho p M A x) := by
  have h1eq : LinearMap.rTensor M (TensorProduct.assoc (ZMod p) B M M) ∘ₗ
        LinearMap.rTensor M (LinearMap.rTensor M (LinearMap.rTensor M φ)) =
      LinearMap.rTensor M (LinearMap.rTensor (M ⊗[ZMod p] M) φ) ∘ₗ
        LinearMap.rTensor M (TensorProduct.assoc (ZMod p) A M M) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp,
      rTensor_assoc_nat (M := M) (N := M) φ]
  have h1 : (LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) B M M))
        (LinearMap.rTensor M (LinearMap.rTensor M (LinearMap.rTensor M φ)) x) =
      LinearMap.rTensor M (LinearMap.rTensor (M ⊗[ZMod p] M) φ)
        ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x) :=
    LinearMap.congr_fun h1eq x
  have h2 : (TensorProduct.assoc (ZMod p) B (M ⊗[ZMod p] M) M)
        (LinearMap.rTensor M (LinearMap.rTensor (M ⊗[ZMod p] M) φ)
          ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x)) =
      LinearMap.rTensor ((M ⊗[ZMod p] M) ⊗[ZMod p] M) φ
        ((TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M)
          ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x)) :=
    LinearMap.congr_fun (rTensor_assoc_nat (M := M) (N := M ⊗[ZMod p] M) φ)
      ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x)
  have h3 : (TensorProduct.congr (LinearEquiv.refl (ZMod p) B) (kappa p M))
        (LinearMap.rTensor ((M ⊗[ZMod p] M) ⊗[ZMod p] M) φ
          ((TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M)
            ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x))) =
      LinearMap.rTensor (TensorPower (ZMod p) 3 M) φ
        ((TensorProduct.congr (LinearEquiv.refl (ZMod p) A) (kappa p M))
          ((TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M)
            ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x))) :=
    (LinearMap.congr_fun (congr_refl_nat (κ := kappa p M) φ)
      ((TensorProduct.assoc (ZMod p) A (M ⊗[ZMod p] M) M)
        ((LinearEquiv.rTensor M (TensorProduct.assoc (ZMod p) A M M)) x))).symm
  simp only [rho, LinearEquiv.trans_apply]
  rw [h1, h2, h3]

end Main

theorem assocTripleTensorGen (p : ℕ) (G : Type uG) [Group G]
    (M : Type uM) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] :
    ∃ ρ : ∀ (A : Type uA) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
        [SMulCommClass G (ZMod p) A],
        TensorProduct (ZMod p) (TensorProduct (ZMod p) (TensorProduct (ZMod p) A M) M) M ≃+
          TensorProduct (ZMod p) A (TensorPower (ZMod p) 3 M),
      (∀ (A : Type uA) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A] (γ : G)
          (x : TensorProduct (ZMod p) (TensorProduct (ZMod p) (TensorProduct (ZMod p) A M) M) M),
        ρ A (γ • x) = γ • ρ A x) ∧
      (∀ (A : Type uA) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
          [SMulCommClass G (ZMod p) A]
        (B : Type uA) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
          [SMulCommClass G (ZMod p) B]
        (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a),
        (ρ B).toAddMonoidHom.comp
            ((LinearMap.rTensor M (LinearMap.rTensor M (LinearMap.rTensor M φ))).toAddMonoidHom)
          = ((LinearMap.rTensor (TensorPower (ZMod p) 3 M) φ).toAddMonoidHom).comp (ρ A).toAddMonoidHom) := by
  refine ⟨fun A _ _ _ _ => (rho p M A).toAddEquiv, ?_, ?_⟩
  · intro A _ _ _ _ γ x
    exact rho_equivariant (p := p) (G := G) M A γ x
  · intro A _ _ _ _ B _ _ _ _ φ hφ
    ext x
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    exact rho_naturality (p := p) M A B φ x

end Work.CohomologicalShrinking.shiftTensor
