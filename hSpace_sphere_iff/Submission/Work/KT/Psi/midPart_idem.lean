import Mathlib
import Submission.Work.KT.Psi.psi2sum_Setup
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Defs

/-!
# Idempotency of the mixed block `midPart ε p q`

For idempotent `p`, `q` and `ε² = 1`, the "mixed" block

`midPart ε p q = (1/2) • [[M, ε·M], [ε·M, M]]`,  `M = p ⊗ q`,

is idempotent.  Indeed `M * M = M` (Kronecker product of idempotents), `ε² = 1` and every scalar
is central (the hypothesis `hA`), so the block matrix `N = [[M, εM], [εM, M]]` satisfies
`N * N = 2 • N`; scaling by `1/2` (whose square times `2` is `1/2` again) gives a projection.

The block computation is isolated in the general helper `midPart_idem_aux`, which only needs a
commutative ring of scalars, an idempotent `M`, and two scalars `c`, `e` with `e * e = 1` and
`c * c * 2 = c`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

/-- The generic block computation behind `midPart_idem`: for a commutative scalar ring, an
idempotent `M`, a scalar `e` with `e * e = 1` and a scalar `c` with `c * c * 2 = c`, the scaled
block matrix `c • [[M, e·M], [e·M, M]]` is idempotent. -/
theorem midPart_idem_aux {B : Type} [CommRing B] {ι : Type} [Fintype ι] (M : Matrix ι ι B)
    (c e : B) (hM : M * M = M) (he : e * e = 1) (hc : c * c * 2 = c) :
    (c • Matrix.fromBlocks M (e • M) (e • M) M) *
        (c • Matrix.fromBlocks M (e • M) (e • M) M) =
      c • Matrix.fromBlocks M (e • M) (e • M) M := by
  have h2 : (e • M) * (e • M) = M := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, one_smul, hM]
  have h3 : M * (e • M) = e • M := by rw [Matrix.mul_smul, hM]
  have h4 : (e • M) * M = e • M := by rw [Matrix.smul_mul, hM]
  have hN : Matrix.fromBlocks M (e • M) (e • M) M * Matrix.fromBlocks M (e • M) (e • M) M
      = (2 : B) • Matrix.fromBlocks M (e • M) (e • M) M := by
    rw [Matrix.fromBlocks_multiply, hM, h3, h4, h2]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [two_mul]
  calc (c • Matrix.fromBlocks M (e • M) (e • M) M) *
        (c • Matrix.fromBlocks M (e • M) (e • M) M)
      = c • (Matrix.fromBlocks M (e • M) (e • M) M *
          (c • Matrix.fromBlocks M (e • M) (e • M) M)) := by
        rw [Matrix.smul_mul]
    _ = c • (c • (Matrix.fromBlocks M (e • M) (e • M) M *
          Matrix.fromBlocks M (e • M) (e • M) M)) := by
        rw [Matrix.mul_smul]
    _ = (c * c) • (Matrix.fromBlocks M (e • M) (e • M) M *
          Matrix.fromBlocks M (e • M) (e • M) M) := by
        rw [smul_smul]
    _ = (c * c) • ((2 : B) • Matrix.fromBlocks M (e • M) (e • M) M) := by rw [hN]
    _ = (c * c * 2) • Matrix.fromBlocks M (e • M) (e • M) M := by rw [smul_smul]
    _ = c • Matrix.fromBlocks M (e • M) (e • M) M := by rw [hc]

theorem midPart_idem {A : Type} [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ε : ℂ) (hε : ε * ε = 1) {p q : Work.KT.Mat A} (hp : p.IsIdem) (hq : q.IsIdem) :
    Work.KT.Psi.midPart ε p q * Work.KT.Psi.midPart ε p q = Work.KT.Psi.midPart ε p q := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have hM : kronP p q * kronP p q = kronP p q := by
    unfold kronP
    rw [← Matrix.mul_kronecker_mul, hp, hq]
  have he : algebraMap ℂ A ε * algebraMap ℂ A ε = 1 := by rw [← map_mul, hε, map_one]
  have hc : algebraMap ℂ A (1/2) * algebraMap ℂ A (1/2) * (2 : A) = algebraMap ℂ A (1/2) := by
    rw [show (2 : A) = algebraMap ℂ A (2 : ℂ) from (map_natCast (algebraMap ℂ A) 2).symm,
      ← map_mul, ← map_mul]
    norm_num
  exact midPart_idem_aux (kronP p q) (algebraMap ℂ A (1/2)) (algebraMap ℂ A ε) hM he hc

end

end Work.KT.Psi
