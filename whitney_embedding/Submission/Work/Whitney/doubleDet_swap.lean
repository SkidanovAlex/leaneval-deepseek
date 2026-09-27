import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.LocalModel

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

-- the structure-field proofs below are written uniformly for both components, so a few
-- `simp` arguments are unused in one of the two goals of each pair
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-!
# Swapping the sheets of a double point changes the signed determinant by `(-1)^n`

This file proves `Work.Whitney.doubleDet_swap`.  The signed determinant `doubleDet f p q u v`
is the determinant, read through the block identification `Work.Projection.pairEquiv n`, of the
"two sheets" map `(x, y) ↦ D (chartRepM f p) u x + D (chartRepM f q) v y` from `ℝⁿ × ℝⁿ` to `ℝ^{2n}`.
Swapping `(p, u)` with `(q, v)` precomposes this map with the block swap of `ℝⁿ × ℝⁿ`, whose
determinant is `(-1)ⁿ`; that is the whole content.

## The block swap

For a real vector space `E`, the block swap `swapLM E : E × E → E × E`, `(x, y) ↦ (y, x)`, is
conjugate — through the "Hadamard" linear equivalence `(x, y) ↦ (x + y, x - y)` — to the diagonal
map `diag (1, -1)`, whose determinant is `(-1) ^ finrank E`.  Hence `det (swapLM E) = (-1) ^ finrank E`,
and for `E = ℝⁿ` this is `(-1)ⁿ`.
-/

section BlockSwap

/-- The block swap `(x, y) ↦ (y, x)` of `E × E`, as a linear map. -/
private noncomputable def blockSwapLM (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (E × E) →ₗ[ℝ] (E × E) :=
  (LinearMap.snd ℝ E E).prod (LinearMap.fst ℝ E E)

/-- The diagonal map `(x, y) ↦ (x, -y)` of `E × E`, as a linear map. -/
private noncomputable def blockDiagLM (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (E × E) →ₗ[ℝ] (E × E) :=
  LinearMap.prodMap (LinearMap.id : E →ₗ[ℝ] E) (-(LinearMap.id : E →ₗ[ℝ] E))

/-- The "Hadamard" linear equivalence `(x, y) ↦ (x + y, x - y)` of `E × E` over `ℝ`; its
inverse is `(a, b) ↦ ((a + b)/2, (a - b)/2)`. -/
private noncomputable def blockHadEquiv (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (E × E) ≃ₗ[ℝ] (E × E) where
  toFun v := (v.1 + v.2, v.1 - v.2)
  invFun v := ((2:ℝ)⁻¹ • (v.1 + v.2), (2:ℝ)⁻¹ • (v.1 - v.2))
  left_inv v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_add,
      smul_sub] <;> module
  right_inv v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, smul_add,
      smul_sub] <;> module
  map_add' v w := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, add_add_add_comm, add_sub_add_comm, add_sub]
  map_smul' c v := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_sub, RingHom.id_apply]

@[simp] private lemma blockHadEquiv_fst {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    ((blockHadEquiv E) v).1 = v.1 + v.2 := rfl

@[simp] private lemma blockHadEquiv_snd {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    ((blockHadEquiv E) v).2 = v.1 - v.2 := rfl

@[simp] private lemma blockSwapLM_fst {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    (blockSwapLM E v).1 = v.2 := rfl

@[simp] private lemma blockSwapLM_snd {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    (blockSwapLM E v).2 = v.1 := rfl

@[simp] private lemma blockDiagLM_fst {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    (blockDiagLM E v).1 = v.1 := rfl

@[simp] private lemma blockDiagLM_snd {E : Type*} [AddCommGroup E] [Module ℝ E] (v : E × E) :
    (blockDiagLM E v).2 = -v.2 := rfl

/-- **The determinant of the block swap.**  For a finite free real vector space `E`, the block
swap of `E × E` has determinant `(-1) ^ finrank E`. -/
private theorem det_blockSwapLM (E : Type*) [AddCommGroup E] [Module ℝ E]
    [Module.Free ℝ E] [Module.Finite ℝ E] :
    LinearMap.det (blockSwapLM E) = (-1 : ℝ) ^ Module.finrank ℝ E := by
  -- The determinant of the diagonal map `(x, y) ↦ (x, -y)` is `(-1) ^ finrank E`.
  have hd : LinearMap.det (blockDiagLM E) = (-1 : ℝ) ^ Module.finrank ℝ E := by
    rw [blockDiagLM, LinearMap.det_prodMap, LinearMap.det_id, one_mul]
    have hneg : -(LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ) • (LinearMap.id : E →ₗ[ℝ] E) := by
      ext x; simp
    rw [hneg, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [← hd]
  -- `blockHadEquiv` conjugates the block swap to the diagonal map.
  have hconj : (blockHadEquiv E : (E × E) →ₗ[ℝ] (E × E)) ∘ₗ blockSwapLM E
      = blockDiagLM E ∘ₗ (blockHadEquiv E : (E × E) →ₗ[ℝ] (E × E)) := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp only [LinearMap.comp_apply]
    change (blockHadEquiv E) (blockSwapLM E (x, y)) = blockDiagLM E ((blockHadEquiv E) (x, y))
    apply Prod.ext
    · rw [blockHadEquiv_fst, blockSwapLM_fst, blockSwapLM_snd, blockDiagLM_fst,
        blockHadEquiv_fst]
      exact add_comm y x
    · rw [blockHadEquiv_snd, blockSwapLM_snd, blockSwapLM_fst, blockDiagLM_snd,
        blockHadEquiv_snd]
      exact (neg_sub x y).symm
  -- A linear equivalence has a unit (in particular nonzero) determinant.
  have hdet : LinearMap.det (blockHadEquiv E : (E × E) →ₗ[ℝ] (E × E)) ≠ 0 :=
    (LinearEquiv.isUnit_det' (blockHadEquiv E)).ne_zero
  have h2 := congrArg LinearMap.det hconj
  rw [LinearMap.det_comp, LinearMap.det_comp, mul_comm (LinearMap.det (blockDiagLM E))] at h2
  exact mul_left_cancel₀ hdet h2

end BlockSwap

/-- Swapping the two sheets changes the signed determinant of a double point by `(-1)^n`.  (`Work.Whitney.doubleDet f p q u v` is the determinant of the two-sheets map `(x,y) ↦ D (chartRepM f p) u x + D (chartRepM f q) v y` read as an endomorphism of `ℝⁿ × ℝⁿ` through the block identification `Work.Projection.pairEquiv n`; swapping the two arguments of the `coprod` multiplies the determinant by `det` of the block swap `ℝⁿ × ℝⁿ → ℝⁿ × ℝⁿ`, which is `(-1)^(n*n) = (-1)^n`.) -/
theorem doubleDet_swap {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p q : M)
    (u v : EuclideanSpace ℝ (Fin n)) :
    Work.Whitney.doubleDet f q p v u = (-1) ^ n * Work.Whitney.doubleDet f p q u v := by
  unfold Work.Whitney.doubleDet Work.Whitney.chartRepM
  -- Name the two derivatives of the two chart representations.
  set A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (fun u => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm u)) u with hA
  set B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    fderiv ℝ (fun u => f ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm u)) v with hB
  -- Swapping the two sheets is precomposition with the block swap.
  have hcop : (↑(B.coprod A) :
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
      = (↑(A.coprod B)) ∘ₗ blockSwapLM (EuclideanSpace ℝ (Fin n)) := by
    rw [ContinuousLinearMap.coe_coprod, ContinuousLinearMap.coe_coprod]
    simp only [blockSwapLM]
    rw [LinearMap.coprod_comp_prod]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.coprod_apply]
    exact add_comm _ _
  -- The block swap of `ℝⁿ × ℝⁿ` has determinant `(-1)ⁿ`.
  have hswap : LinearMap.det (blockSwapLM (EuclideanSpace ℝ (Fin n))) = (-1 : ℝ) ^ n := by
    rw [det_blockSwapLM, finrank_euclideanSpace, Fintype.card_fin]
  rw [hcop, ← LinearMap.comp_assoc, LinearMap.det_comp, hswap]
  exact mul_comm _ _

end Work.Whitney
