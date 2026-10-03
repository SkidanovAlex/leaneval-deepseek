/-
Shared definitions and generic finite-sum lemmas for the Cauchy--Schwarz step
(`winForm_succ_cs`) of the Gowers--Cauchy--Schwarz induction for the box form.

The `ω`-product of the box form splits, at a fixed corner `(z, z') ∈ Tuple n Q × Tuple n Q` and
window point `x ∈ W`, into the product `halfProd ... a` over the "first half" of the cube and the
conjugate of the product `halfProd ... a'` over the "second half"; `halfProd` is that half product.
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.WinAux
import Submission.Work.Peluse.BoxNorm.cauchySchwarzC

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

open Work.Peluse

/-- The "half product" of the box form: for a slot `u`, a corner `(z, z')` of `Tuple n Q`, a
window point `x` and a shift `a`, the product `∏_{ω} C^{|ω|} u_ω (x + σ(corner z z' ω) + a)`
over the `2^n` vertices `ω` of the cube. -/
def halfProd (n : ℕ) (Q : Fin n → Finset ℤ) (u : (Fin n → Bool) → ℤ → ℂ)
    (z z' : Tuple n Q) (x a : ℤ) : ℂ :=
  ∏ ω : Fin n → Bool, (star^[weight ω]) (u ω (x + Tuple.total (Tuple.corner z z' ω) + a))

/-- The slot `ω ↦ φ (false :: ω)` of the second half of the cube. -/
def slotF {n : ℕ} (φ : (Fin (n+1) → Bool) → ℤ → ℂ) : (Fin n → Bool) → ℤ → ℂ :=
  fun ω y => φ (Fin.cases false ω) y

/-- The slot `ω ↦ φ (true :: ω)` of the first half of the cube. -/
def slotT {n : ℕ} (φ : (Fin (n+1) → Bool) → ℤ → ℂ) : (Fin n → Bool) → ℤ → ℂ :=
  fun ω y => φ (Fin.cases true ω) y

/-- `winForm_shift_prod` in terms of `halfProd`. -/
lemma winForm_shift_prod_halfProd {n : ℕ} (Q : Fin n → Finset ℤ) (W : Finset ℤ)
    (u : (Fin n → Bool) → ℤ → ℂ) (a a' : ℤ) :
    winForm n Q W (fun ω y => u ω (y + a) * star (u ω (y + a')))
      = ∑ z : Tuple n Q, ∑ z' : Tuple n Q, ∑ x ∈ W,
          halfProd n Q u z z' x a * star (halfProd n Q u z z' x a') := by
  rw [winForm_shift_prod]
  simp only [halfProd]

/-- Summing a product of a "half" at `a'` and the conjugate of a "half" at `a` over `(a, a')`
factorises into the product of the two sums. -/
lemma sum_factor_star {ι P : Type*} [Fintype ι] [Fintype P] (W : Finset ℤ)
    (F G : ι → P → ℤ → ℂ) :
    (∑ a : ι, ∑ a' : ι, ∑ p : P, ∑ x ∈ W, F a' p x * star (G a p x))
      = ∑ p : P, ∑ x ∈ W, (∑ a' : ι, F a' p x) * star (∑ a : ι, G a p x) := by
  have h1 : ∀ a : ι, (∑ a' : ι, ∑ p : P, ∑ x ∈ W, F a' p x * star (G a p x))
      = ∑ p : P, ∑ x ∈ W, ∑ a' : ι, F a' p x * star (G a p x) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => h1 a)]
  have h2 : (∑ a : ι, ∑ p : P, ∑ x ∈ W, ∑ a' : ι, F a' p x * star (G a p x))
      = ∑ p : P, ∑ x ∈ W, ∑ a : ι, ∑ a' : ι, F a' p x * star (G a p x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
  rw [h2]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => ?_
  rw [star_sum, Finset.sum_mul_sum, Finset.sum_comm]

/-- `z · conj z = |z|²`, as a complex number. -/
lemma sum_mul_star_self {ι : Type*} [Fintype ι] (H : ι → ℂ) :
    (∑ a : ι, H a) * star (∑ a : ι, H a) = ((‖∑ a : ι, H a‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The norm of a finite sum of nonnegative reals, read in `ℂ`. -/
lemma norm_ofReal_sum_eq {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ‖∑ i ∈ s, ((r i : ℝ) : ℂ)‖ = ∑ i ∈ s, r i := by
  rw [← Complex.ofReal_sum]
  exact norm_ofReal_of_nonneg (Finset.sum_nonneg hr)

end

end Work.Peluse.BoxNorm
