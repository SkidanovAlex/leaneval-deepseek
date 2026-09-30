import Mathlib
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for `sieg2_PhiE_surjective`

`psiAssemble F N` assembles coordinates indexed by `Fin N × index F` into a tuple of `N` vectors
of the Euclidean mixed space `KE F`, by expanding in the orthonormal basis
`mixedEmbedding.euclidean.stdOrthonormalBasis F`.  It is the linear isomorphism that makes the
matrix model `PhiE a` conjugate to the mixed-space model `Phi a`.
-/

open scoped Classical
open NumberField

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- Assemble coordinates `(j, c) ↦ ℝ` into a tuple of `N` vectors of the Euclidean mixed space,
expanding in the orthonormal basis `stdOrthonormalBasis F`. -/
def psiAssemble (N : ℕ) :
    (Fin N × NumberField.mixedEmbedding.index F → ℝ) →ₗ[ℝ] (Fin N → KE F) where
  toFun x := fun j =>
    ∑ c, x (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

/-- The inverse of `psiAssemble`: the coordinates of a tuple of mixed-space vectors in the
orthonormal basis `stdOrthonormalBasis F`. -/
def psiAssembleInv (N : ℕ) :
    (Fin N → KE F) →ₗ[ℝ] (Fin N × NumberField.mixedEmbedding.index F → ℝ) where
  toFun y := fun p =>
    (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr (y p.1) p.2
  map_add' y z := by
    ext p
    simp only [Pi.add_apply, map_add, WithLp.ofLp_add]
  map_smul' r y := by
    ext p
    simp only [Pi.smul_apply, map_smul, WithLp.ofLp_smul, RingHom.id_apply]

@[simp]
theorem psiAssemble_apply (N : ℕ)
    (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) (j : Fin N) :
    psiAssemble (F := F) N x j =
      ∑ c, x (j, c) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c := rfl

@[simp]
theorem psiAssembleInv_apply (N : ℕ) (y : Fin N → KE F)
    (p : Fin N × NumberField.mixedEmbedding.index F) :
    psiAssembleInv (F := F) N y p =
      (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F).repr (y p.1) p.2 := rfl

theorem psiAssembleInv_psiAssemble (N : ℕ)
    (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) :
    psiAssembleInv (F := F) N (psiAssemble (F := F) N x) = x := by
  ext p
  simp only [psiAssemble_apply, psiAssembleInv_apply, map_sum, map_smul, WithLp.ofLp_sum,
    Finset.sum_apply, Pi.smul_apply, WithLp.ofLp_smul, OrthonormalBasis.repr_self,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem psiAssemble_psiAssembleInv (N : ℕ) (y : Fin N → KE F) :
    psiAssemble (F := F) N (psiAssembleInv (F := F) N y) = y := by
  ext j
  simp only [psiAssemble_apply, psiAssembleInv_apply]
  exact OrthonormalBasis.sum_repr (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) (y j)

theorem psiAssemble_injective (N : ℕ) :
    Function.Injective (psiAssemble (F := F) N) := by
  intro x y h
  have h' := congrArg (psiAssembleInv (F := F) N) h
  rwa [psiAssembleInv_psiAssemble, psiAssembleInv_psiAssemble] at h'

theorem psiAssemble_surjective (N : ℕ) :
    Function.Surjective (psiAssemble (F := F) N) := fun y =>
  ⟨psiAssembleInv (F := F) N y, psiAssemble_psiAssembleInv N y⟩

/-- The linear equivalence assembling coordinates into tuples of the Euclidean mixed space. -/
def psiEquiv (N : ℕ) :
    (Fin N × NumberField.mixedEmbedding.index F → ℝ) ≃ₗ[ℝ] (Fin N → KE F) where
  toLinearMap := psiAssemble N
  invFun := psiAssembleInv N
  left_inv := psiAssembleInv_psiAssemble N
  right_inv := psiAssemble_psiAssembleInv N

/-! ## Algebra of `mulK` -/

theorem mulK_add (x y : F) : mulK (x + y) = mulK x + mulK y := by
  ext z
  simp only [LinearMap.add_apply, mulK_apply, map_add, add_mul]

theorem mulK_mul (x y : F) : mulK (x * y) = (mulK x).comp (mulK y) := by
  ext z
  simp [mulK]

theorem mulK_zero : mulK (0 : F) = 0 := by
  ext z
  simp [mulK]

theorem mulK_sum {ι : Type*} (s : Finset ι) (f : ι → F) (y : KE F) :
    mulK (∑ i ∈ s, f i) y = ∑ i ∈ s, mulK (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [mulK_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mulK_add, LinearMap.add_apply, ih]

/-! ## Basic evaluations of `Phi`, `PhiMat` -/

theorem Phi_single {M N : ℕ} (a : Fin M → Fin N → F) (j : Fin N) (v : KE F) (i : Fin M) :
    Phi a (Pi.single j v) i = mulK (a i j) v := by
  rw [Phi_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem PhiMat_apply_coe {M N : ℕ} (a : Fin M → Fin N → F) (i : Fin M)
    (c : NumberField.mixedEmbedding.index F) (j : Fin N)
    (c' : NumberField.mixedEmbedding.index F) :
    PhiMat a (i, c) (j, c') =
      inner ℝ (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c)
        (mulK (a i j) (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F c')) := by
  simp only [PhiMat, Phi_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem psiAssemble_single (N : ℕ) (q : Fin N × NumberField.mixedEmbedding.index F) :
    psiAssemble (F := F) N (Pi.single q 1) =
      Pi.single q.1 (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F q.2) := by
  ext j
  rw [psiAssemble_apply]
  by_cases h : j = q.1
  · subst h
    rw [Finset.sum_eq_single q.2]
    · simp
    · intro c _ hc
      rw [Pi.single_eq_of_ne (show (q.1, c) ≠ (q.1, q.2) from fun hh => hc (Prod.mk.inj hh).2)]
      simp
    · intro hh; exact absurd (Finset.mem_univ q.2) hh
  · rw [Pi.single_eq_of_ne h]
    exact Finset.sum_eq_zero (fun c _ => by
      rw [Pi.single_eq_of_ne (show (j, c) ≠ q from fun hh => h (Prod.mk.inj hh).1)]
      simp)

end

end Work.BW
