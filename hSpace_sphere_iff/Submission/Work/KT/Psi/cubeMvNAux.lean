import Mathlib
import Submission.Work.KT.Psi.Basic

/-!
# `Work.KT.Psi.cubeMvNAux`

Auxiliary definitions for `Work.KT.Psi.cubePart_MvN`:

* `kron3r M = M ⊗ M ⊗ M`, the triple Kronecker product of a *possibly rectangular* matrix;
* `cubeW n lam = (1/3)(1 + λ⁻¹ c + λ⁻² c²)`, the spectral projector of the cyclic permutation
  `c = cycPermP n` of the three tensor factors, cast as a matrix on `(Fin n × Fin n) × Fin n`.

The product `cubePartP lam p = kron3r p.2 * cubeW p.1 lam` is definitional.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

variable {A : Type} [Ring A]

/-- The triple Kronecker product `M ⊗ M ⊗ M` of a (possibly rectangular) matrix. -/
def kron3r {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) :
    Matrix ((Fin m × Fin m) × Fin m) ((Fin k × Fin k) × Fin k) A :=
  kroneckerMap (fun a b => a * b) (kroneckerMap (fun a b => a * b) M M) M

@[simp] theorem kron3r_apply {m k : ℕ} (M : Matrix (Fin m) (Fin k) A)
    (x : (Fin m × Fin m) × Fin m) (y : (Fin k × Fin k) × Fin k) :
    kron3r M x y = (M x.1.1 y.1.1 * M x.1.2 y.1.2) * M x.2 y.2 := rfl

variable [Algebra ℂ A]

/-- The spectral projector `(1/3)(1 + λ⁻¹ c + λ⁻² c²)` of the cyclic permutation on
`(Fin n × Fin n) × Fin n`, as it appears in `cubePartP`. -/
def cubeW (n : ℕ) (lam : ℂ) :
    Matrix ((Fin n × Fin n) × Fin n) ((Fin n × Fin n) × Fin n) A :=
  algebraMap ℂ A (1 / 3) •
    (1 + algebraMap ℂ A lam⁻¹ • Equiv.Perm.permMatrix A (cycPermP n) +
      algebraMap ℂ A (lam⁻¹ ^ 2) •
        (Equiv.Perm.permMatrix A (cycPermP n) * Equiv.Perm.permMatrix A (cycPermP n)))

/-- `cubePartP` is the product of the tensor cube and the spectral projector. -/
theorem cubePartP_eq_kron3r (lam : ℂ) (p : Mat A) :
    cubePartP lam p = kron3r p.2 * cubeW p.1 lam := rfl

end

end Work.KT.Psi
