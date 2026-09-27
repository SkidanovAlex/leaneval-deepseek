import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubeAux
import Submission.Work.KT.Psi.k3Aux
import Submission.Work.KT.Psi.cubeMvNAux
import Submission.Work.KT.Psi.cls_split
import Submission.Work.KT.Psi.cls_conj
import Submission.Work.KT.Psi.cls_orbit

/-!
# `Work.KT.Psi.cubePart_idem`

`cubePart λ p = (p ⊗ p ⊗ p) · (1 + λ⁻¹ c + λ⁻² c²)/3`, where `c` is the cyclic permutation of
the three tensor factors.  Both factors are idempotent and they commute, so the product is
idempotent:

* `p ⊗ p ⊗ p` is idempotent because `p` is (`kron3_idem`),
* `(1 + λ⁻¹ c + λ⁻² c²)/3` is idempotent because `c³ = 1` and `λ³ = 1`, and
* `p ⊗ p ⊗ p` commutes with the cyclic permutation (`kron3_mul_permMatrix_cyc`).

The work is done on the unreindexed index type `(Fin n × Fin n) × Fin n` (where `cubePartP` lives),
and transported back to `cubePart` by `Matrix.reindex`.
-/

namespace Work.KT.Psi

open Matrix

/-- The "third" spectral projector `(1 + W + W²)/3` of an element `W` with `W³ = 1`: it is the
projector onto the `1`-eigenspace of `W`, hence idempotent. -/
theorem thirdProj_idem {S : Type} [Ring S] [Algebra ℂ S] {W : S} (hW : W * W * W = 1) :
    (1 + W + W*W) * (1 + W + W*W) = (3:ℂ) • (1 + W + W*W) := by
  have hexp : (1 + W + W*W) * (1 + W + W*W) =
      1 + W + W*W + W + W*W + W*W*W + W*W + W*W*W + W*W*W*W := by noncomm_ring
  rw [hexp]
  simp only [hW, one_mul]
  rw [Algebra.smul_def', map_ofNat]
  noncomm_ring

/-- Complex scalars act on matrices compatibly with the matrix product. -/
theorem smul_mul_smul_C {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a b : ℂ) (M N : Matrix ι ι A) : (a • M) * (b • N) = (a*b) • (M*N) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The spectral projector `(1 + λ⁻¹ c + λ⁻² c²)/3` of the cyclic permutation is idempotent
whenever `λ³ = 1`.  Writing `W = λ⁻¹ · c`, it is `(1 + W + W²)/3` with `W³ = λ⁻³ c³ = 1`. -/
theorem cubeProj_idem {A : Type} [Ring A] [Algebra ℂ A]
    (lam : ℂ) (hlam : lam ^ 3 = 1) (p : Mat A) :
    cubeProj p lam * cubeProj p lam = cubeProj p lam := by
  have hξ : (lam⁻¹ : ℂ)^3 = 1 := by rw [inv_pow, hlam, inv_one]
  have hZ3 : Equiv.Perm.permMatrix A (cycPermP p.1) * Equiv.Perm.permMatrix A (cycPermP p.1) *
      Equiv.Perm.permMatrix A (cycPermP p.1) = 1 := permMatrix_cycPermP_cube (A := A)
  have hW3 : ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1)) *
      ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1)) *
      ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1)) = 1 := by
    rw [smul_mul_smul_C, smul_mul_smul_C, hZ3]
    rw [show (lam⁻¹:ℂ) * lam⁻¹ * lam⁻¹ = (lam⁻¹)^3 by ring, hξ, one_smul]
  have hcp : cubeProj p lam =
      (1/3:ℂ) • (1 + (lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1) +
        ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1)) *
        ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1))) := by
    rw [cubeProj_eq, algebraMap_smul_eq_smul_C, algebraMap_smul_eq_smul_C,
      algebraMap_smul_eq_smul_C, pow_two, smul_mul_smul_C]
  rw [hcp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, thirdProj_idem hW3, smul_smul]
  norm_num

/-- `p ⊗ p ⊗ p` commutes with the spectral projector of the cyclic permutation (it commutes with
the cyclic permutation itself). -/
theorem kron3_mul_cubeProj_comm {A : Type} [Ring A] [Algebra ℂ A]
    (hA : ∀ x y : A, x * y = y * x) (lam : ℂ) (p : Mat A) :
    kron3 p.2 * cubeProj p lam = cubeProj p lam * kron3 p.2 := by
  have hZ : kron3 p.2 * Equiv.Perm.permMatrix A (cycPermP p.1) =
      Equiv.Perm.permMatrix A (cycPermP p.1) * kron3 p.2 := kron3_mul_permMatrix_cyc hA p.2
  have hcp : cubeProj p lam =
      (1/3:ℂ) • (1 + (lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1) +
        ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1)) *
        ((lam⁻¹:ℂ) • Equiv.Perm.permMatrix A (cycPermP p.1))) := by
    rw [cubeProj_eq, algebraMap_smul_eq_smul_C, algebraMap_smul_eq_smul_C,
      algebraMap_smul_eq_smul_C, pow_two, smul_mul_smul_C]
  set Z := Equiv.Perm.permMatrix A (cycPermP p.1)
  have hu : kron3 p.2 * ((lam⁻¹:ℂ) • Z) = ((lam⁻¹:ℂ) • Z) * kron3 p.2 := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hZ]
  have hu2 : kron3 p.2 * (((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)) =
      (((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)) * kron3 p.2 := by
    rw [← Matrix.mul_assoc, hu, Matrix.mul_assoc, hu, ← Matrix.mul_assoc]
  have huu : kron3 p.2 * (1 + (lam⁻¹:ℂ) • Z + ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)) =
      (1 + (lam⁻¹:ℂ) • Z + ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)) * kron3 p.2 := by
    rw [mul_add, mul_add, mul_one, add_mul, add_mul, one_mul, hu, hu2]
  rw [hcp]
  calc kron3 p.2 * ((1/3:ℂ) •
          (1 + (lam⁻¹:ℂ) • Z + ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)))
      = (1/3:ℂ) • (kron3 p.2 *
          (1 + (lam⁻¹:ℂ) • Z + ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z))) :=
        Matrix.mul_smul _ _ _
    _ = (1/3:ℂ) • ((1 + (lam⁻¹:ℂ) • Z + ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z)) *
          kron3 p.2) := by rw [huu]
    _ = ((1/3:ℂ) • (1 + (lam⁻¹:ℂ) • Z +
          ((lam⁻¹:ℂ) • Z) * ((lam⁻¹:ℂ) • Z))) * kron3 p.2 :=
        (Matrix.smul_mul _ _ _).symm

/-- On the unreindexed tensor cube, `cubePartP λ p` is idempotent. -/
theorem cubePartP_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) (hlam : lam ^ 3 = 1) {p : Mat A} (hp : p.IsIdem) :
    cubePartP lam p * cubePartP lam p = cubePartP lam p := by
  have hK : kron3 p.2 * kron3 p.2 = kron3 p.2 := kron3_idem hA p.2 hp
  have hP : cubeProj p lam * cubeProj p lam = cubeProj p lam := cubeProj_idem lam hlam p
  have hKP : kron3 p.2 * cubeProj p lam = cubeProj p lam * kron3 p.2 :=
    kron3_mul_cubeProj_comm hA lam p
  rw [cubePartP_eq_kron3_mul]
  calc (kron3 p.2 * cubeProj p lam) * (kron3 p.2 * cubeProj p lam)
      = kron3 p.2 * (cubeProj p lam * kron3 p.2) * cubeProj p lam := by noncomm_ring
    _ = kron3 p.2 * (kron3 p.2 * cubeProj p lam) * cubeProj p lam := by rw [← hKP]
    _ = (kron3 p.2 * kron3 p.2) * (cubeProj p lam * cubeProj p lam) := by noncomm_ring
    _ = kron3 p.2 * cubeProj p lam := by rw [hK, hP]

theorem cubePart_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) (hlam : lam ^ 3 = 1) {p : Mat A} (hp : p.IsIdem) :
    (cubePart lam p).IsIdem := by
  have hX : cubePartP lam p * cubePartP lam p = cubePartP lam p := cubePartP_idem hA lam hlam hp
  show (cubePart lam p).2 * (cubePart lam p).2 = (cubePart lam p).2
  rw [cubePart_eq]
  rw [← reindex_mul', hX]

end Work.KT.Psi
