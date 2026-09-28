/-
# Auxiliary objects for `Work.HP.JcVolNormDet`

For linearly independent `w z` in a Euclidean space, the coordinate map
`x ↦ x₀ • w + x₁ • z : ℝ² → P = ℝw ⊕ ℝz` is the adjoint of the "pairing"
map `lamP w z : P → ℝ²`, and the composite `lamP w z ∘ psiP w z : ℝ² → ℝ²`
is the Gram matrix of `(w,z)`.  These two computations give
`(lamP w z).normDet = √(deltaV w z)`.
-/
import Mathlib
import Submission.Work.HP.JcVolDefs
import Submission.Work.HP.JcVolAlg

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

/-- The linear map `x ↦ x₀ • w + x₁ • z` from `ℝ²` to the ambient space `E`. -/
def psiV {ι : Type*} (w z : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := x 0 • w + x 1 • z
  map_add' x y := by
    simp only [PiLp.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply]

@[simp] lemma psiV_apply {ι : Type*} (w z : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ (Fin 2)) : psiV w z x = x 0 • w + x 1 • z := rfl

variable {ι : Type*} [Fintype ι]

lemma psiV_mem (w z : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ (Fin 2)) :
    psiV w z x ∈ planeP w z := by
  show x 0 • w + x 1 • z ∈ Submodule.span ℝ {w, z}
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_) <;>
    exact Submodule.subset_span (by simp)

/-- The coordinate map `ℝ² → P = ℝw ⊕ ℝz`, `x ↦ x₀ • w + x₁ • z`. -/
def psiP (w z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ↥(planeP w z) :=
  (psiV w z).codRestrict (planeP w z) (psiV_mem w z)

@[simp] lemma psiP_coe (w z : EuclideanSpace ℝ ι) (x : EuclideanSpace ℝ (Fin 2)) :
    ((psiP w z x : ↥(planeP w z)) : EuclideanSpace ℝ ι) = x 0 • w + x 1 • z := rfl

@[simp] lemma psiP_single_zero_coe (w z : EuclideanSpace ℝ ι) :
    (((psiP w z) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) : ↥(planeP w z)) :
      EuclideanSpace ℝ ι) = w := by
  show (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 • w +
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 1 • z = w
  simp

@[simp] lemma psiP_single_one_coe (w z : EuclideanSpace ℝ ι) :
    (((psiP w z) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) : ↥(planeP w z)) :
      EuclideanSpace ℝ ι) = z := by
  show (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0 • w +
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 1 • z = z
  simp

/-- The Gram matrix of the pair `(w,z)`. -/
def gramG (w z : EuclideanSpace ℝ ι) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![‖w‖ ^ 2, inner ℝ w z; inner ℝ w z, ‖z‖ ^ 2]

@[simp] lemma gramG_zero_zero (w z : EuclideanSpace ℝ ι) : gramG w z 0 0 = ‖w‖ ^ 2 := rfl

@[simp] lemma gramG_zero_one (w z : EuclideanSpace ℝ ι) : gramG w z 0 1 = inner ℝ w z := rfl

@[simp] lemma gramG_one_zero (w z : EuclideanSpace ℝ ι) : gramG w z 1 0 = inner ℝ w z := rfl

@[simp] lemma gramG_one_one (w z : EuclideanSpace ℝ ι) : gramG w z 1 1 = ‖z‖ ^ 2 := rfl

lemma gramG_det (w z : EuclideanSpace ℝ ι) : (gramG w z).det = deltaV w z := by
  rw [Matrix.det_fin_two]
  simp only [gramG_zero_zero, gramG_zero_one, gramG_one_zero, gramG_one_one, deltaV]
  ring

end Work.HP
