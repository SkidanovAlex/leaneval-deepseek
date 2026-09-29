import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Coeff

namespace Commons.Combinatorics.Fintype

open Finset

/-- The product of `w` over the coordinates of `g` only depends on the sizes of the fibres of `g`.
Regrouping the product by fibres. -/
private theorem fiber_prod {α R : Type*} [Fintype α] [DecidableEq α] [CommMonoid R]
    {k : ℕ} (w : α → R) (g : Fin k → α) :
    ∏ c : Fin k, w (g c)
      = ∏ x : α, w x ^ ((Finset.univ.filter (fun c : Fin k => g c = x)).card) := by
  rw [← Finset.prod_fiberwise' (s := (Finset.univ : Finset (Fin k))) (g := g) (f := w)]
  apply Finset.prod_congr rfl
  intro x _
  rw [Finset.prod_const]

/-- Expansion of `(∑ x, X x)^k` as a sum over all functions `Fin k → α`, in the multivariate
polynomial ring. -/
private theorem func_expansion {α : Type*} [Fintype α] (k : ℕ) :
    (∑ x : α, (MvPolynomial.X x : MvPolynomial α ℕ))^k
      = ∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          ∏ c : Fin k, (MvPolynomial.X (g c) : MvPolynomial α ℕ) := by
  have h := Finset.prod_univ_sum (κ := fun _ : Fin k => α)
    (t := fun _ : Fin k => (Finset.univ : Finset α))
    (f := fun (_ : Fin k) (x : α) => (MvPolynomial.X x : MvPolynomial α ℕ))
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- The number of functions `Fin k → α` whose fibre sizes are prescribed by `p` (with
`∑ x, p x = k`) is the multinomial coefficient `Nat.multinomial univ p`.

This is obtained by extracting the coefficient of the monomial `∏ x, X x ^ p x` in the expansion
of `(∑ x, X x)^k`, comparing it with the multinomial formula for coefficients. -/
private theorem card_fiber_eq_multinomial {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℕ) (k : ℕ) (hp : ∑ x, p x = k) :
    ((Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α))).filter
      (fun g => ∀ x, ((Finset.univ : Finset (Fin k)).filter (fun c => g c = x)).card = p x)).card
      = Nat.multinomial Finset.univ p := by
  classical
  let P : α →₀ ℕ := Finsupp.ofSupportFinite p (Set.toFinite _)
  have hP : ∀ x, P x = p x := by
    intro x
    simp only [P]
    rw [Finsupp.ofSupportFinite_coe]
  have hsum : P.sum (fun _ m => m) = k := by
    rw [Finsupp.sum_fintype P (fun _ m => m) (fun i => rfl)]
    simp [hP, hp]
  have hmult : P.multinomial = Nat.multinomial Finset.univ p :=
    (Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)).trans
      (Nat.multinomial_congr (fun a _ => hP a))
  have hcoeff : ∀ g : Fin k → α,
      (∏ c : Fin k, (MvPolynomial.X (g c) : MvPolynomial α ℕ)).coeff P
        = if (∀ x, ((Finset.univ : Finset (Fin k)).filter (fun c => g c = x)).card = p x)
          then 1 else 0 := by
    intro g
    have hiff : (P = Finsupp.indicator (Finset.univ : Finset α)
          (fun i (_ : i ∈ (Finset.univ : Finset α)) =>
            ((Finset.univ : Finset (Fin k)).filter (fun c => g c = i)).card))
        ↔ ∀ x, ((Finset.univ : Finset (Fin k)).filter (fun c => g c = x)).card = p x := by
      rw [Finsupp.ext_iff]
      constructor
      · intro h x
        have hx := h x
        rw [Finsupp.indicator_of_mem (Finset.mem_univ x)
          (fun i _ => ((Finset.univ : Finset (Fin k)).filter (fun c => g c = i)).card)] at hx
        rw [hP x] at hx
        exact hx.symm
      · intro h x
        rw [Finsupp.indicator_of_mem (Finset.mem_univ x)
          (fun i _ => ((Finset.univ : Finset (Fin k)).filter (fun c => g c = i)).card)]
        rw [hP x, h x]
    rw [fiber_prod (fun x => (MvPolynomial.X x : MvPolynomial α ℕ)) g]
    rw [MvPolynomial.coeff_prod_X_pow]
    simp only [hiff]
  calc ((Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α))).filter
      (fun g => ∀ x, ((Finset.univ : Finset (Fin k)).filter (fun c => g c = x)).card = p x)).card
      = ∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          (if (∀ x, ((Finset.univ : Finset (Fin k)).filter (fun c => g c = x)).card = p x)
            then 1 else 0) := by
          rw [Finset.card_filter]
    _ = ∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          (∏ c : Fin k, (MvPolynomial.X (g c) : MvPolynomial α ℕ)).coeff P := by
          apply Finset.sum_congr rfl
          intro g _
          rw [hcoeff g]
    _ = (∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          ∏ c : Fin k, (MvPolynomial.X (g c) : MvPolynomial α ℕ)).coeff P := by
          rw [MvPolynomial.coeff_sum]
    _ = ((∑ x : α, (MvPolynomial.X x : MvPolynomial α ℕ))^k).coeff P := by
          rw [func_expansion]
    _ = (if P.sum (fun _ m => m) = k then P.multinomial else 0) := by
          rw [MvPolynomial.coeff_sum_X_pow_of_fintype]
          simp
    _ = P.multinomial := by rw [if_pos hsum]
    _ = Nat.multinomial Finset.univ p := hmult

theorem sum_piFinset_ite_card_eq_multinomial {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R]
    (p : α → ℕ) (k : ℕ) (hp : ∑ x, p x = k) (w : α → R) :
    (∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
        (if ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x
         then ∏ c, w (g c) else 0))
      = (Nat.multinomial Finset.univ p : R) * ∏ x, w x ^ p x := by
  have hstep : (∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
        (if ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x
          then ∏ c, w (g c) else 0))
      = (∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          (if ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x
            then (1:R) else 0))
        * ∏ x, w x ^ p x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g _
    by_cases h : ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x
    · rw [if_pos h, if_pos h, one_mul, fiber_prod w g]
      apply Finset.prod_congr rfl
      intro x _
      rw [h x]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hstep]
  have hcard : (∑ g ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α)),
          (if ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x
            then (1:R) else 0))
      = (((Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset α))).filter
          (fun g => ∀ x, (Finset.univ.filter (fun c : Fin k => g c = x)).card = p x)).card : R) := by
    rw [Finset.sum_boole]
  rw [hcard, card_fiber_eq_multinomial p k hp]

end Commons.Combinatorics.Fintype