/-
# Small `K[G]`-linear isomorphisms for the dimension-shifting chain `chainOfJL52`

The chain identity `Work.ORFinal.Chain.chainOfJL52` identifies `Tor₂^{K[G]}(S, M)` with
`Tor₁^{K[G]}(S ⊗_K I_{K[G]}, M)`.  Its construction (following the route design, T6) uses the
`K[G]`-linear "associativity swap" `Tor_k(S, M ⊗_K N) ≅ Tor_k(S ⊗_K M, N)` for the diagonal
structures, the dimension shift along `0 → I → K[G] → K → 0`, and the trivial module
identifications recorded here:

* `tensorCommDiag` : the flip `M ⊗_K N ≅ N ⊗_K M` is `K[G]`-linear for the diagonal
  `K[G]`-module structures of `Work.ORHomAlg.JL52.instDiagModule`;
* `tensorTrivRight` : `M ⊗_K K ≅ M`, `K` carrying the trivial left `K[G]`-module structure
  and `M` the `K`-structure induced by its `K[G]`-structure;
* `smulCommClass_catK` : the canonical `K`-structure on an object of `ModuleCat (K[G])`
  commutes with the `K[G]`-action.

The three elementary facts about the diagonal action (`diagSMul_add`, `diagAdd_smul`,
`diagSMul_smul`) are recorded separately because the `SMul` instance `JL52.instDiagSMul` is
propositionally, but not syntactically, equal to the one carried by the `Module` instance.
-/
import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORFP2.Basic
import Submission.Work.ORBridgeTor.TrivMod
import Submission.Work.ORBridgeTor.trivTensorEquiv

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MonoidAlgebra TensorProduct MulOpposite
open scoped TensorProduct

namespace Work.ORFinal.Chain

universe u

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-- The diagonal action is additive in the second variable (as a statement about the `SMul`
instance `JL52.instDiagSMul`, which is propositionally equal to the one of the `Module`
instance). -/
theorem diagSMul_add (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (a : MonoidAlgebra K G) (b c : A ⊗[K] X) : a • (b + c) = a • b + a • c := by
  rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
    Work.ORHomAlg.JL52.diag_smul_def, map_add]

/-- The diagonal action is additive in the scalar. -/
theorem diagAdd_smul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (a b : MonoidAlgebra K G) (c : A ⊗[K] X) : (a + b) • c = a • c + b • c := by
  rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
    Work.ORHomAlg.JL52.diag_smul_def, map_add]
  rfl

/-- The `K`-scalars of `K[G]` act on the diagonal tensor product through the `K`-module
structure. -/
theorem diagSMul_smul (A X : Type u) [AddCommGroup A] [Module K A]
    [Module (MonoidAlgebra K G) A] [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X]
    (c : K) (r : MonoidAlgebra K G) (z : A ⊗[K] X) : (c • r) • z = c • (r • z) := by
  rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diag_smul_def,
    Work.ORHomAlg.JL52.diagRingHom_smul]
  rfl

/-- The canonical `K`-structure on an object of `ModuleCat (K[G])`
(`Work.ORHomAlg.JL52.instModuleCatK`) commutes with the `K[G]`-action. -/
theorem smulCommClass_catK (X : ModuleCat.{u} (MonoidAlgebra K G)) :
    SMulCommClass K (MonoidAlgebra K G) ↥X where
  smul_comm c r x := by
    show c • (r • x) = r • (c • x)
    rw [Work.ORHomAlg.JL52.smulCatK_def, Work.ORHomAlg.JL52.smulCatK_def, ← mul_smul, ← mul_smul,
      Algebra.commutes]

/-- **The flip of a diagonal tensor product is `K[G]`-linear.**  For two left `K[G]`-modules `M`,
`N` whose `K`-module structures and `K[G]`-module structures are compatible (`SMulCommClass`),
the flip `M ⊗_K N ≅ N ⊗_K M` is an isomorphism of `K[G]`-modules for the diagonal
`K[G]`-structures. -/
theorem tensorCommDiag (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [SMulCommClass K (MonoidAlgebra K G) M]
    (N : Type u) [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [SMulCommClass K (MonoidAlgebra K G) N] :
    Nonempty (TensorProduct K M N ≃ₗ[MonoidAlgebra K G] TensorProduct K N M) := by
  have hmain : ∀ (x : MonoidAlgebra K G) (z : TensorProduct K M N),
      TensorProduct.comm K M N (x • z) = x • TensorProduct.comm K M N z := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      intro z
      rw [MonoidAlgebra.of_apply]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
        rw [Work.ORHomAlg.JL52.diag_smul_single_tmul, TensorProduct.comm_tmul,
          TensorProduct.comm_tmul, Work.ORHomAlg.JL52.diag_smul_single_tmul]
      | add y y' hy hy' =>
        rw [diagSMul_add M N, map_add]
        rw [show TensorProduct.comm K M N (y + y')
            = TensorProduct.comm K M N y + TensorProduct.comm K M N y' from
          map_add (TensorProduct.comm K M N) y y']
        rw [diagSMul_add N M, hy, hy']
    | add x y hx hy =>
      intro z
      rw [diagAdd_smul M N, map_add, hx z, hy z]
      exact (diagAdd_smul N M x y (TensorProduct.comm K M N z)).symm
    | smul c x hx =>
      intro z
      rw [diagSMul_smul M N c x z, map_smul, hx z]
      exact (diagSMul_smul N M c x (TensorProduct.comm K M N z)).symm
  exact ⟨{ (TensorProduct.comm K M N : TensorProduct K M N ≃ₗ[K] TensorProduct K N M) with
    map_smul' := hmain }⟩

/-- **`M ⊗_K K ≅ M`**, where `K` carries the trivial left `K[G]`-module structure
(`Work.ORBridgeTor.instTrivLeftModule`) and `M` is a left `K[G]`-module whose `K`-module
structure is the one induced by the `K[G]`-action; the tensor carries the diagonal structure. -/
theorem tensorTrivRight (M : Type u) [AddCommGroup M] [Module K M]
    [Module (MonoidAlgebra K G) M] [IsScalarTower K (MonoidAlgebra K G) M]
    [SMulCommClass K (MonoidAlgebra K G) M] :
    Nonempty (TensorProduct K M K ≃ₗ[MonoidAlgebra K G] M) := by
  obtain ⟨e1⟩ := tensorCommDiag (K := K) (G := G) M K
  obtain ⟨e2⟩ := Work.ORBridgeTor.trivTensorEquiv K G M
  exact ⟨e1.trans e2⟩

/-- **`S` as a right `K[G]`-module through `φ`**, encoded (as always here) as a left
`(K[G])ᵐᵒᵖ`-module: `(op x) • s = s * φ x`.  This is the structure with respect to which
`Work.ORCoherence.Tor φ.toRingHom` computes `Tor^{K[G]}(S, -)`; it is pinned by the hypothesis
`h` of `Work.ORHomAlg.Bridge.torEquiv`. -/
noncomputable def rightModuleOfRingHom (K : Type u) [CommSemiring K] (G : Type u) [Group G]
    (S : Type u) [Semiring S] (φ : MonoidAlgebra K G →+* S) :
    Module (MonoidAlgebra K G)ᵐᵒᵖ S where
  smul x s := s * φ (MulOpposite.unop x)
  one_smul s := by
    show s * φ (MulOpposite.unop (1 : (MonoidAlgebra K G)ᵐᵒᵖ)) = s
    rw [MulOpposite.unop_one, map_one, mul_one]
  mul_smul x y s := by
    show s * φ (MulOpposite.unop (x * y))
      = (s * φ (MulOpposite.unop y)) * φ (MulOpposite.unop x)
    rw [MulOpposite.unop_mul, map_mul, mul_assoc]
  smul_zero x := by
    show (0 : S) * φ (MulOpposite.unop x) = 0
    rw [zero_mul]
  smul_add x s t := by
    show (s + t) * φ (MulOpposite.unop x)
      = s * φ (MulOpposite.unop x) + t * φ (MulOpposite.unop x)
    rw [add_mul]
  add_smul x y s := by
    show s * φ (MulOpposite.unop (x + y))
      = s * φ (MulOpposite.unop x) + s * φ (MulOpposite.unop y)
    rw [MulOpposite.unop_add, map_add, mul_add]
  zero_smul s := by
    show s * φ (MulOpposite.unop (0 : (MonoidAlgebra K G)ᵐᵒᵖ)) = 0
    rw [MulOpposite.unop_zero, map_zero, mul_zero]

/-- The computation rule for `rightModuleOfRingHom`. -/
theorem rightModuleOfRingHom_smul {K : Type u} [CommSemiring K] {G : Type u} [Group G]
    {S : Type u} [Semiring S] (φ : MonoidAlgebra K G →+* S)
    (x : (MonoidAlgebra K G)ᵐᵒᵖ) (s : S) :
    letI := rightModuleOfRingHom K G S φ
    x • s = s * φ (MulOpposite.unop x) := rfl

/-- The `K[G]`-action of `rightModuleOfRingHom` and the `S`-action commute. -/
theorem smulCommClass_rightModuleOfRingHom {K : Type u} [CommSemiring K] {G : Type u} [Group G]
    {S : Type u} [Semiring S] (φ : MonoidAlgebra K G →+* S) :
    letI := rightModuleOfRingHom K G S φ
    SMulCommClass S (MonoidAlgebra K G)ᵐᵒᵖ S := by
  letI := rightModuleOfRingHom K G S φ
  refine ⟨fun a x s => ?_⟩
  show a * (s * φ (MulOpposite.unop x)) = (a * s) * φ (MulOpposite.unop x)
  rw [mul_assoc]

/-- The `K`-module structure on the trivial left `K[G]`-module `K`
(`Work.ORBridgeTor.instTrivLeftModule`) is compatible in the sense of `IsScalarTower`. -/
theorem isScalarTower_trivLeft (K : Type u) [Field K] (G : Type u) [Group G] :
    IsScalarTower K (MonoidAlgebra K G) K := by
  refine ⟨fun c x k => ?_⟩
  rw [Algebra.smul_def, Work.ORBridgeTor.instTrivLeftModule_smul,
    Work.ORBridgeTor.instTrivLeftModule_smul, map_mul,
    show Work.ORHomAlg.augmentation K G (algebraMap K (MonoidAlgebra K G) c) = c by
      rw [show algebraMap K (MonoidAlgebra K G) c = MonoidAlgebra.single (1 : G) c from rfl,
        Work.ORHomAlg.JL52.augmentation_single],
    smul_eq_mul, mul_assoc]

/-- `IsZero` for an object of `ModuleCat R` is `Subsingleton` of its underlying type. -/
theorem moduleCat_isZero_iff (R : Type u) [Ring R] (X : ModuleCat.{u} R) :
    CategoryTheory.Limits.IsZero X ↔ Subsingleton ↥X :=
  ⟨fun h => ModuleCat.subsingleton_of_isZero h,
    fun h => by haveI : Subsingleton ↥X := h; exact ModuleCat.isZero_of_subsingleton X⟩

end Work.ORFinal.Chain
