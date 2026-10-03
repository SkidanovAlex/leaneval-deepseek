import Mathlib
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORBridgeTor.Mirror
import Submission.Work.ORHomAlg.Dual
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs
import Submission.Work.ORFlatness.DiagonalRight

namespace Work.ORBridgeTor

/-!
The domain `DualMod (TensorProduct K S M)` carries `Work.ORHomAlg.DualMod.instModuleOfRight`
(the dual of the right action `Work.ORFlatness.diagRightModule`, installed by `letI`), and the
codomain `TensorProduct K S M` carries the diagonal action
`Work.ORHomAlg.JL52.instDiagModule` (built from the `K[G]`-module structure on `S` supplied as an
instance argument, with `hS` recording that it is the structure induced by `φ`).

Suggested proof: the map `s ⊗ₜ[K] m ↦ ι s ⊗ₜ[K] m` (the identity on the underlying type, since
`DualMod M = M`); it is `K`-linear because `ι` is.  For `map_smul'` first prove the monomial case
`g : G` by `TensorProduct.induction_on` together with
`Work.ORFlatness.diagRightModule_op_single_tmul`,
`Work.ORHomAlg.DualMod.instModuleOfRight_smul`,
`Work.ORHomAlg.JL52.diag_smul_single_tmul`, `Work.ORBridgeTor.AntiAut.map_mul`, `hι` and `hS`,
then extend to all scalars with `MonoidAlgebra.induction_on`.
-/
open TensorProduct MulOpposite

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

section Twist

variable (K : Type u) [Field K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
variable [Module (MonoidAlgebra K G) S] [SMulCommClass K (MonoidAlgebra K G) S]
variable (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
variable [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M]
variable (ι : AntiAut K S)

/-- The `K`-linear twist `z ↦ (ι ⊗ id) z` on `S ⊗[K] M`, i.e. `s ⊗ m ↦ ι s ⊗ m`; it is the
comparison map of `Work.ORBridgeTor.dualDiagRight`. -/
noncomputable def twistLin (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (M : Type u) [AddCommGroup M] [Module K M]
    (ι : AntiAut K S) : (S ⊗[K] M) ≃ₗ[K] (S ⊗[K] M) :=
  TensorProduct.congr ι.toLinearEquiv (LinearEquiv.refl K M)

theorem twistLin_tmul (s : S) (m : M) :
    twistLin K G S M ι (s ⊗ₜ[K] m) = ι s ⊗ₜ[K] m := by
  simp [twistLin]

/-- The `K`-scalar compatibility of the diagonal `K[G]`-action on `S ⊗[K] M`. -/
theorem diag_smul_smul (c : K) (x : MonoidAlgebra K G) (w : S ⊗[K] M) :
    (c • x) • w = c • (x • w) := by
  rw [Work.ORHomAlg.JL52.diag_smul_def, Work.ORHomAlg.JL52.diagRingHom_smul]
  rfl

/-- Scalar extraction for the diagonal `K[G]`-action on `S ⊗[K] M`. -/
theorem diag_single_smul (g : G) (c : K) (w : S ⊗[K] M) :
    (MonoidAlgebra.single g c) • w = c • ((MonoidAlgebra.single g (1 : K)) • w) := by
  have h : MonoidAlgebra.single g c = c • (MonoidAlgebra.single g (1 : K)) := by
    rw [Algebra.smul_def, ← MonoidAlgebra.of_apply,
      ← MonoidAlgebra.single_eq_algebraMap_mul_of (M := G) g c]
  rw [h, diag_smul_smul]

/-- **The monomial case of the twist identity** for the diagonal action on `S ⊗[K] M`: the map
`Ψ (s ⊗ m) = ι s ⊗ m` sends the antipode-twisted right action of `single h 1` to the diagonal
action of `single h⁻¹ 1`. -/
theorem twistLin_diagRightAct_single
    (hS : ∀ (x : MonoidAlgebra K G) (s : S), x • s = φ x * s)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (h : G) (z : S ⊗[K] M) :
    twistLin K G S M ι
        (diagRightAct K G S φ M (op (MonoidAlgebra.single h (1 : K))) z) =
      (MonoidAlgebra.single h⁻¹ (1 : K)) • (twistLin K G S M ι z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, diagRightAct_map_zero, map_zero, Work.ORHomAlg.JL52.diag_smul_def, map_zero]
  | tmul s m =>
      rw [diagRightAct_op_single_one_tmul, twistLin_tmul, twistLin_tmul,
        Work.ORHomAlg.JL52.diag_smul_single_tmul]
      congr 1
      rw [hS (MonoidAlgebra.single h⁻¹ (1 : K)) (ι s), AntiAut.map_mul, hι]
      rfl
  | add z w hz hw =>
      rw [diagRightAct_map_add]
      simp only [map_add]
      rw [Work.ORHomAlg.JL52.diag_smul_def, map_add]
      simp only [← Work.ORHomAlg.JL52.diag_smul_def]
      rw [hz, hw]

/-- **The twist identity for all scalars**: the map `Ψ (s ⊗ m) = ι s ⊗ m` intertwines the
antipode-twisted right diagonal action (`diagRightAct`, i.e. the action of the dual
`DualMod (S ⊗[K] M)`) with the diagonal action on `S ⊗[K] M`. -/
theorem twistLin_diagRightAct
    (hS : ∀ (x : MonoidAlgebra K G) (s : S), x • s = φ x * s)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (β : MonoidAlgebra K G) (z : S ⊗[K] M) :
    twistLin K G S M ι (diagRightAct K G S φ M (Work.ORHomAlg.antipodeEquiv K G β) z) =
      β • (twistLin K G S M ι z) := by
  induction β using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, diagRightAct_zero, map_zero, zero_smul]
  | add x y hx hy => rw [map_add, diagRightAct_add, map_add, hx, hy, add_smul]
  | single g c =>
      rw [Work.ORHomAlg.antipodeEquiv_single, diagRightAct_op_single, map_smul,
        twistLin_diagRightAct_single (K := K) (G := G) (S := S) (φ := φ) (M := M) (ι := ι)
          (hS := hS) (hι := hι) (h := g⁻¹), inv_inv]
      exact (diag_single_smul (K := K) (G := G) (S := S) (M := M) g c
        (twistLin K G S M ι z)).symm

end Twist

theorem dualDiagRight (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    [Module (MonoidAlgebra K G) S] [SMulCommClass K (MonoidAlgebra K G) S]
    (hS : ∀ (x : MonoidAlgebra K G) (s : S), x • s = φ x * s)
    (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M]
    (ι : Work.ORBridgeTor.AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹) :
    letI := Work.ORFlatness.diagRightModule K G S φ M
    Nonempty (Work.ORHomAlg.DualMod (TensorProduct K S M) ≃ₗ[MonoidAlgebra K G]
      (TensorProduct K S M)) := by
  letI := Work.ORFlatness.diagRightModule K G S φ M
  refine ⟨{ twistLin K G S M ι with map_smul' := ?_ }⟩
  intro x z
  rw [Work.ORHomAlg.DualMod.instModuleOfRight_smul]
  exact twistLin_diagRightAct (K := K) (G := G) (S := S) (φ := φ) (M := M) (ι := ι)
    (hS := hS) (hι := hι) x z

end Work.ORBridgeTor
