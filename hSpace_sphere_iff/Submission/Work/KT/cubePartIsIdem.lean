import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubeAux

/-!
# `Work.KT.cubePartIsIdem`

`cubePart lam p` is `p ⊗ p ⊗ p = p^{⊗3}` cut down by the spectral projector
`(1 + λ⁻¹c + λ⁻²c²)/3` of the cyclic permutation `c` of the three tensor factors.  It is
idempotent whenever `p` is, because

* `c³ = 1` makes `(1 + λ⁻¹c + λ⁻²c²)/3` idempotent (with `λ³ = 1`), and
* `c` commutes with `p^{⊗3}`, while `(p^{⊗3})² = (p²)^{⊗3} = p^{⊗3}` for idempotent `p`.

Two idempotents that commute have an idempotent product, which is the final assembly.

The proof of the projector identity `T² = 3·T` for `T = 1 + d + d²` with `d³ = 1` is the only
real content: `T·d = 1 + d + d² = T` and hence `T·T = T·1 + T·d + T·d² = 3·T`.
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## The spectral projector of a cube root of unity -/

/-- The spectral projector `(1/3)(1 + λ⁻¹c + λ⁻²c²)` of an element `c` of order three. -/
def cycProj {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [Ring A] [Algebra ℂ A]
    (c : Matrix ι ι A) (lam : ℂ) : Matrix ι ι A :=
  (1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))

/-- In a ring: `T = 1 + d + d²` satisfies `T · T = 3 • T` when `d³ = 1`. -/
theorem one_add_add_sq_three_smul {R : Type} [Ring R] [Algebra ℂ R] {d : R} (hd : d * d * d = 1) :
    ((1 : R) + d + d * d) * (1 + d + d * d) = (3 : ℂ) • (1 + d + d * d) := by
  have h1 : ((1 : R) + d + d * d) * d = (1 + d + d * d) := by
    rw [add_mul, add_mul, one_mul, hd]
    abel
  have h2 : ((1 : R) + d + d * d) * (d * d) = (1 + d + d * d) := by
    rw [← mul_assoc, h1, h1]
  rw [mul_add, mul_add, mul_one, h1, h2]
  rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

/-- The spectral projector `(1/3)(1 + λ⁻¹c + λ⁻²c²)` of an element `c` with `c³ = 1` is
idempotent, for `λ³ = 1`. -/
theorem cycProj_idem {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : Matrix ι ι A) (hc : c * c * c = 1) (lam : ℂ) (hlam : lam ^ 3 = 1) :
    cycProj c lam * cycProj c lam = cycProj c lam := by
  have ha3 : (lam⁻¹ : ℂ) ^ 3 = 1 := by rw [inv_pow, hlam, inv_one]
  have hdd : (lam⁻¹ : ℂ) • c * ((lam⁻¹ : ℂ) • c) = ((lam⁻¹) ^ 2 : ℂ) • (c * c) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  have hd3 : ((lam⁻¹ : ℂ) • c) * ((lam⁻¹ : ℂ) • c) * ((lam⁻¹ : ℂ) • c) = 1 := by
    rw [hdd, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc,
      show ((lam⁻¹ : ℂ) ^ 2 * lam⁻¹) = 1 from by rw [← pow_succ, ha3], one_smul]
  have hT : ((1 : Matrix ι ι A) + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c)) *
      (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c)) =
      (3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c)) := by
    rw [← hdd]
    exact one_add_add_sq_three_smul hd3
  show ((1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))) *
      ((1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))) =
    (1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hT, smul_smul,
    show (1 / 3 : ℂ) * (1 / 3) * 3 = 1 / 3 by norm_num]

/-- `cycProj c lam` commutes with any `K` commuting with `c`. -/
theorem cycProj_comm {A : Type} [Ring A] [Algebra ℂ A] {ι : Type} [Fintype ι] [DecidableEq ι]
    (K c : Matrix ι ι A) (hKc : K * c = c * K) (lam : ℂ) :
    K * cycProj c lam = cycProj c lam * K := by
  have h2 : K * (c * c) = (c * c) * K := by
    calc K * (c * c) = (K * c) * c := (Matrix.mul_assoc K c c).symm
      _ = (c * K) * c := by rw [hKc]
      _ = c * (K * c) := Matrix.mul_assoc c K c
      _ = c * (c * K) := by rw [hKc]
      _ = (c * c) * K := (Matrix.mul_assoc c c K).symm
  have hT : K * (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c)) =
      (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c)) * K := by
    simp only [mul_add, mul_one, add_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul, hKc, h2]
  show K * ((1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))) =
    ((1 / 3 : ℂ) • (1 + (lam⁻¹ : ℂ) • c + ((lam⁻¹) ^ 2 : ℂ) • (c * c))) * K
  rw [Matrix.mul_smul, hT, Matrix.smul_mul]

/-- The projector `Psi.cubeProj p lam` of `Work.KT.Psi.cubeAux` is `cycProj` of the permutation
matrix of the cyclic permutation. -/
theorem cubeProj_eq_cycProj {A : Type} [Ring A] [Algebra ℂ A] (p : Mat A) (lam : ℂ) :
    Psi.cubeProj p lam = cycProj (Equiv.Perm.permMatrix A (cycPermP p.1)) lam := by
  rw [Psi.cubeProj_eq_cubeProjC]
  rfl

/-! ## The lemma -/

/-- `Work.KT.cubePart lam p = (p ⊗ p ⊗ p) · (1 + λ⁻¹c + λ⁻²c²)/3`, the `λ`-eigencomponent of
the cyclic permutation on `p ⊗ p ⊗ p`, is idempotent when `p` is idempotent (over a commutative
ring) and `λ³ = 1`. -/
lemma cubePartIsIdem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (lam : ℂ) (hlam : lam ^ 3 = 1) {p : Work.KT.Mat A} (hp : Work.KT.Mat.IsIdem p) :
    Work.KT.Mat.IsIdem (Work.KT.cubePart lam p) := by
  -- Idempotency of the unreindexed version, on the product index type
  -- `(Fin n × Fin n) × Fin n`: both factors are idempotent and they commute.
  have hP : cubePartP lam p * cubePartP lam p = cubePartP lam p := by
    rw [Psi.cubePartP_eq_kron3_mul]
    have hKK : Psi.kron3 p.2 * Psi.kron3 p.2 = Psi.kron3 p.2 := Psi.kron3_idem hA p.2 hp
    have hWW : Psi.cubeProj p lam * Psi.cubeProj p lam = Psi.cubeProj p lam := by
      rw [cubeProj_eq_cycProj]
      exact cycProj_idem _ Psi.permMatrix_cycPermP_cube lam hlam
    have hKW : Psi.kron3 p.2 * Psi.cubeProj p lam = Psi.cubeProj p lam * Psi.kron3 p.2 := by
      rw [cubeProj_eq_cycProj]
      exact cycProj_comm _ _ (Psi.kron3_mul_permMatrix_cyc hA p.2) lam
    exact IsIdempotentElem.mul_of_commute (a := Psi.kron3 p.2) (b := Psi.cubeProj p lam)
      hKW hKK hWW
  -- Transport back through the reindexing used in the definition of `cubePart`.
  have hsec : Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p) =
      (cubePart lam p).2 := cubePart_reindex lam p
  rw [Mat.IsIdem, ← hsec]
  change Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p) *
      Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p) =
    Matrix.reindex (cycIdx p.1).symm (cycIdx p.1).symm (cubePartP lam p)
  rw [← reindex_mul', hP]

end

end Work.KT
