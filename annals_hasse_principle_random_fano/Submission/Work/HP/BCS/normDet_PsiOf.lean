import Mathlib
import Submission.Work.HP.BCS.Transport
import Submission.Work.HP.Lat.detL_basis_gram

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000

open Matrix

namespace Work.HP.BCS

/-- Inner product of two embedded integer vectors, in the order in which the lattice Gram matrix
is written. -/
theorem toEr_inner {ι : Type*} [Fintype ι] [DecidableEq ι] (u v : ι → ℤ) :
    inner ℝ (toEr u) (toEr v) = ∑ κ, ((u κ : ℝ) * (v κ : ℝ)) := by
  rw [show (toEr u : EuclideanSpace ℝ ι) = toE (toR u) from rfl]
  rw [inner_toE_toEr]
  simp only [Work.HP.dotR, Work.HP.toR]

/-- The Gram entries of `Ψ = isomSpan ∘ coeffEquiv` at the standard basis vectors are the Gram
entries of the lattice basis `b`. -/
theorem inner_PsiOf_basisFun {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L)
    (i j : Fin k) :
    inner ℝ (PsiOf L b (EuclideanSpace.single i 1)) (PsiOf L b (EuclideanSpace.single j 1))
      = ∑ κ, (((b i : ι → ℤ) κ : ℝ) * ((b j : ι → ℤ) κ : ℝ)) := by
  rw [PsiOf_single_eq L b i, PsiOf_single_eq L b j,
      LinearIsometryEquiv.inner_map_map (isomSpan L b)]
  rw [Submodule.coe_inner, toEr_inner]

/-- The explicit matrix of Gram entries of the lattice basis `b`, in the form appearing in
`Work.HP.Lat.detL_basis_gram`. -/
def gramB {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Submodule ℤ (ι → ℤ)} {k : ℕ}
    (b : Module.Basis (Fin k) ℤ L) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∑ κ, (((b i : ι → ℤ) κ : ℝ) * ((b j : ι → ℤ) κ : ℝ))

theorem gramB_eq_basis_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    gramB b = Matrix.of fun i j : Fin k =>
        ∑ x, (((b i : ι → ℤ) x : ℝ) * ((b j : ι → ℤ) x : ℝ)) := by
  ext i j
  simp only [gramB, Matrix.of_apply]

/-- The Gram matrix of `Ψ` in the standard orthonormal basis of `ℝ^k` is `gramB b`. -/
theorem gram_PsiOf_basisFun {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (Matrix.gram ℝ fun x => PsiOf L b ((EuclideanSpace.basisFun (Fin k) ℝ) x)) = gramB b := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.of_apply, gramB, EuclideanSpace.basisFun_apply]
  exact inner_PsiOf_basisFun L b i j

/-- `gramB b` is the genuine Gram matrix of the embedded lattice basis vectors, hence positive
semidefinite. -/
theorem gramB_eq_gram_toEr {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    gramB b = Matrix.gram ℝ (fun i => Work.HP.toEr ((b i : ι → ℤ))) := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.of_apply, gramB]
  exact (toEr_inner ((b i : ι → ℤ)) ((b j : ι → ℤ))).symm

theorem gramB_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (gramB b).PosSemidef := by
  rw [gramB_eq_gram_toEr L b]
  exact Matrix.posSemidef_gram ℝ _

theorem gramB_det_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    0 ≤ (gramB b).det :=
  Matrix.PosSemidef.det_nonneg (gramB_posSemidef L b)

-- `normDet` of the coordinate lattice map `Ψ = isomSpan ∘ coeffEquiv : ℝ^k → ℝ^k` equals the
-- covolume `detL L` of the lattice.
--
-- `LinearMap.normDet_sq_eq_det_gram (PsiOf L b) (EuclideanSpace.basisFun (Fin k) ℝ)` gives
-- `↑((PsiOf L b).normDet ^ 2) = (Matrix.gram ℝ (fun x => PsiOf L b (basisFun x))).det`, and
-- `gram_PsiOf_basisFun` identifies that Gram matrix with `gramB b`; `Work.HP.Lat.detL_basis_gram`
-- writes `detL L = Real.sqrt (gramB b).det`.  Both sides of the target are nonnegative, so we
-- rewrite `normDet` as `Real.sqrt (normDet ^ 2)` and use the two square identities.
theorem normDet_PsiOf {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) :
    (Work.HP.BCS.PsiOf L b).normDet = Work.HP.detL L := by
  have h1 : (PsiOf L b).normDet ^ 2 = (gramB b).det := by
    have h := LinearMap.normDet_sq_eq_det_gram (PsiOf L b) (EuclideanSpace.basisFun (Fin k) ℝ)
    rw [gram_PsiOf_basisFun L b] at h
    simpa using h
  have h2 : Work.HP.detL L = Real.sqrt (gramB b).det := by
    rw [Work.HP.Lat.detL_basis_gram L b, ← gramB_eq_basis_gram L b]
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg (PsiOf L b)), h1, ← h2]

end Work.HP.BCS
