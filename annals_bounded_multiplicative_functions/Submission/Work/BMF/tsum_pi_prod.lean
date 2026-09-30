import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `∑'` of a product over a product of indices

Auxiliary lemma for the formalisation of Matomäki–Radziwiłł–Tao–Teräväinen–Ziegler,
"Higher uniformity of bounded multiplicative functions in short intervals on average".

For finitely many families `φ j : ℤ → ℂ` that are absolutely summable with sums `A j`,
the family `c ↦ ∏ j, φ j (c j)` on the finite product `Fin k → ℤ` is summable in norm,
with sum `∏ j, A j`.  This is the "finitely many factors" version of the classical fact
that the product of two absolutely convergent series is the termwise double sum.
-/

namespace Work.BMF

open scoped BigOperators

/-- Splitting off the `0`-th coordinate of a function on `Fin (n+1)`. -/
def finSuccProdEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    ext <;> simp

@[simp] lemma finSuccProdEquiv_symm_apply {α : Type*} {n : ℕ} (z : α × (Fin n → α)) :
    (finSuccProdEquiv α n).symm z = Fin.cons z.1 z.2 := rfl

set_option maxHeartbeats 1000000 in
theorem tsum_pi_prod_aux (k : ℕ) (φ : Fin k → ℤ → ℂ) (A : Fin k → ℂ)
    (hφ : ∀ j, HasSum (φ j) (A j)) (habs : ∀ j, Summable (fun c : ℤ => ‖φ j c‖)) :
    Summable (fun c : Fin k → ℤ => ∏ j, ‖φ j (c j)‖) ∧
      (∑' c : Fin k → ℤ, ∏ j, φ j (c j)) = ∏ j, A j := by
  induction k with
  | zero =>
    constructor
    · exact Summable.of_finite
    · simp
  | succ k ih =>
    obtain ⟨ihsumm, ihtsum⟩ := ih (fun j => φ j.succ) (fun j => A j.succ)
      (fun j => hφ j.succ) (fun j => habs j.succ)
    constructor
    · -- summability of the product of the norms
      have h1 : Summable (fun z : ℤ × (Fin k → ℤ) =>
          ‖φ 0 z.1‖ * ∏ j : Fin k, ‖φ j.succ (z.2 j)‖) :=
        (habs 0).mul_of_nonneg ihsumm (fun _ => norm_nonneg _)
          (fun w => Finset.prod_nonneg (fun j _ => norm_nonneg _))
      have h2 : Summable (fun z : ℤ × (Fin k → ℤ) =>
          ∏ j : Fin (k+1), ‖φ j (((finSuccProdEquiv ℤ k).symm z) j)‖) := by
        refine h1.congr (fun z => ?_)
        rw [Fin.prod_univ_succ]; simp
      exact (Equiv.summable_iff (finSuccProdEquiv ℤ k).symm
        (f := fun c : Fin (k+1) → ℤ => ∏ j, ‖φ j (c j)‖)).mp h2
    · -- the value of the sum
      have hg : Summable (fun w : Fin k → ℤ => ‖∏ j : Fin k, φ j.succ (w j)‖) := by
        simpa only [norm_prod] using ihsumm
      rw [← Equiv.tsum_eq (finSuccProdEquiv ℤ k).symm
        (fun c : Fin (k+1) → ℤ => ∏ j, φ j (c j))]
      simp_rw [Fin.prod_univ_succ]
      simp only [finSuccProdEquiv_symm_apply, Fin.cons_zero, Fin.cons_succ]
      rw [← tsum_mul_tsum_of_summable_norm (f := φ 0)
        (g := fun w : Fin k → ℤ => ∏ j : Fin k, φ j.succ (w j)) (habs 0) hg]
      rw [hφ 0 |>.tsum_eq, ihtsum]

theorem tsum_pi_prod {k : ℕ} {φ : Fin k → ℤ → ℂ} {A : Fin k → ℂ}
    (hφ : ∀ j, HasSum (φ j) (A j)) (habs : ∀ j, Summable (fun c : ℤ => ‖φ j c‖)) :
    Summable (fun c : Fin k → ℤ => ∏ j, ‖φ j (c j)‖) ∧
      (∑' c : Fin k → ℤ, ∏ j, φ j (c j)) = ∏ j, A j :=
  tsum_pi_prod_aux k φ A hφ habs

end Work.BMF
