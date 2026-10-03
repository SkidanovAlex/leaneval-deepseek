import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.DualityDefs
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

namespace Work.ORHughesFree.NaturalExtension

universe u

open Matrix Work.ORHughesFree

/-- **The twisted shift as a right multiple.**  Let `Q : Matrix (Fin (k+1)) (Fin (k+2)) R` be the
matrix whose `p`-th row is `Matrix.vecCons 0 (fun q => if p = q then 1 else 0)`, i.e.
`Q p 0 = 0` and `Q p (q+1) = if p = q then 1 else 0`.  Then for any `(m × (k+1))`-matrix `X`,
the `i`-th row of `X * Q` is `Fin.cons 0 (fun p => X i p)`: right multiplication by `Q` shifts
each row one place to the right and inserts a `0` in the first column. -/
private lemma mul_vecCons_eq {R : Type*} [Ring R] {m k : ℕ}
    (X : Matrix (Fin m) (Fin (k + 1)) R) :
    X * (Matrix.of (fun p j => Matrix.vecCons (0 : R)
          (fun q : Fin (k + 1) => if p = q then 1 else 0) j) :
        Matrix (Fin (k + 1)) (Fin (k + 2)) R)
      = fun i : Fin m => Fin.cons 0 (fun p : Fin (k + 1) => X i p) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨q, rfl⟩
  · rw [Matrix.mul_apply]
    simp [Matrix.cons_val_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single q]
    · simp [Matrix.cons_val_succ]
    · intro b _ hb
      simp [Matrix.cons_val_succ, hb]
    · intro hq
      exact absurd (Finset.mem_univ q) hq

/-- A matrix whose `i`-th row is the twisted shift `Fin.cons 0 (τ ∘ (row i of Z))` has rank at
most the dimension of the row span of `Z`.

PROOF SKETCH.  `A = (Z.map τ) * Q` where `Q : Matrix (Fin (k+1)) (Fin (k+2)) R` has
`Q p 0 = 0` and `Q p (j+1) = if p = j then 1 else 0` (using `Fin.cons`'s computation rule and
`Fin.succ`).  Then `rk A ≤ rk (Z.map τ)` by `rk_mul_le_left`, `rk (Z.map τ) = rk Z` by `hτ`, and
`rk Z = rdim rk (span of the rows of Z)` by `rdim_eq_rk_rows`. -/
theorem rk_cons_le {R : Type u} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R)
    (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A)
    {m k : ℕ} (A : Matrix (Fin m) (Fin (k + 2)) R) (Z : Matrix (Fin m) (Fin (k + 1)) R)
    (hAZ : ∀ i : Fin m,
      (fun j => A i j) = Fin.cons 0 (fun p : Fin (k + 1) => (Multiplicative.ofAdd (1 : ℤ)) • Z i p)) :
    rk.rk m (k + 2) A ≤ rdim rk (Submodule.span R (Set.range fun i : Fin m => fun p : Fin (k + 1) => Z i p)) := by
  classical
  have hA_eq : A = (Z.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) *
      (Matrix.of (fun p j => Matrix.vecCons (0 : R)
        (fun q : Fin (k + 1) => if p = q then 1 else 0) j) :
          Matrix (Fin (k + 1)) (Fin (k + 2)) R) := by
    rw [mul_vecCons_eq]
    funext i
    rw [show A i = Fin.cons 0 (fun p : Fin (k + 1) =>
        (Multiplicative.ofAdd (1 : ℤ)) • Z i p) from hAZ i]
    rfl
  calc rk.rk m (k + 2) A
      = rk.rk m (k + 2) ((Z.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) *
          (Matrix.of (fun p j => Matrix.vecCons (0 : R)
            (fun q : Fin (k + 1) => if p = q then 1 else 0) j) :
              Matrix (Fin (k + 1)) (Fin (k + 2)) R)) := by
          rw [hA_eq]
    _ ≤ rk.rk m (k + 1) (Z.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) :=
        rk.rk_mul_le_left _ _
    _ = rk.rk m (k + 1) Z := hτ m (k + 1) Z
    _ = rdim rk (Submodule.span R (Set.range fun i : Fin m => fun p : Fin (k + 1) => Z i p)) :=
        (rdim_eq_rk_rows rk Z).symm

end Work.ORHughesFree.NaturalExtension
