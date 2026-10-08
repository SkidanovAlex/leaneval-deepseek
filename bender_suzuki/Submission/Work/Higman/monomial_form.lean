/-
Copyright (c) 2024. All rights reserved.

# Higman's Lemma 11, type `A` (monomial form of an equivariant quadratic map)

Main result: `Work.Higman.monomial_form`.
-/

import Mathlib
import Submission.Work.Higman.QuadAux
import Submission.Work.Higman.bilinear_frob
import Submission.Work.Higman.coeff_vanishing_of_scale
import Submission.Work.Higman.additive_scale_zero
import Submission.Work.Higman.polar_Q1_eq_B
import Submission.Work.Higman.monomial_extract

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman

/-! ## Elementary rewriting helpers

These turn the statement `B (nu*x) (nu*y) = lam * B x y` (with `B` a double Frobenius sum)
into the shape produced by the `coeff_vanishing_of_scale` interface. -/

section Rewrite

variable {R : Type*} [CommRing R]

lemma scale_rewrite (d : ℕ → ℕ → R) (n : ℕ) (nu lam x y : R) :
    (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, d k l * (nu * x) ^ (2 ^ k) * (nu * y) ^ (2 ^ l))
      - lam * (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
          d k l * x ^ (2 ^ k) * y ^ (2 ^ l))
    = ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
        (d k l * (nu ^ (2 ^ k + 2 ^ l) - lam)) * x ^ (2 ^ k) * y ^ (2 ^ l) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_pow, mul_pow, pow_add]
  ring

lemma scale_rewrite_lin (a : ℕ → R) (n : ℕ) (nu lam x : R) :
    (∑ k ∈ Finset.range n, a k * (nu * x) ^ (2 ^ k))
      - lam * (∑ k ∈ Finset.range n, a k * x ^ (2 ^ k))
    = ∑ k ∈ Finset.range n, (a k * (nu ^ (2 ^ k) - lam)) * x ^ (2 ^ k) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mul_pow]
  ring

lemma scale_rewrite_Q1 (d : ℕ → ℕ → R) (n : ℕ) (nu lam x : R) :
    (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
        d k l * (nu * x) ^ (2 ^ k + 2 ^ l))
      - lam * (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
          d k l * x ^ (2 ^ k + 2 ^ l))
    = ∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
        (d k l * (nu ^ (2 ^ k + 2 ^ l) - lam)) * x ^ (2 ^ k + 2 ^ l) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_pow]
  ring

end Rewrite

/-- **Core linear algebra of Higman's Lemma 11 (type `A`)**, general finite field form. -/
theorem monomial_form_aux {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (ν lam : Fˣ) (hν : orderOf ν = 2 ^ n - 1)
    (hnotconj : ∀ s : ℕ, (ν : F) ≠ (lam : F) ^ 2 ^ s)
    (Q : F → F) (hQ0 : Q 0 = 0)
    (hQne : ∀ α : F, α ≠ 0 → Q α ≠ 0)
    (hadd1 : ∀ α α' γ : F, Q (α + α' + γ) + Q (α + α') + Q γ =
      (Q (α + γ) + Q α + Q γ) + (Q (α' + γ) + Q α' + Q γ))
    (hadd2 : ∀ α γ γ' : F, Q (α + (γ + γ')) + Q α + Q (γ + γ') =
      (Q (α + γ) + Q α + Q γ) + (Q (α + γ') + Q α + Q γ'))
    (hξ : ∀ α : F, Q ((ν : F) * α) = (lam : F) * Q α) :
    ∃ i j : ℕ, i < j ∧ j < n ∧ (ν : F) ^ (2 ^ i + 2 ^ j) = (lam : F) ∧
      ∃ c : F, c ≠ 0 ∧ ∀ α, Q α = c * α ^ (2 ^ i + 2 ^ j) := by
  classical
  -- ## Step 1: the polar form `B`
  let B : F → F → F := fun x y => Q (x + y) + Q x + Q y
  have hBx : ∀ y x x' : F, B (x + x') y = B x y + B x' y := fun y x x' => hadd1 x x' y
  have hBy : ∀ x y y' : F, B x (y + y') = B x y + B x y' := fun x y y' => hadd2 x y y'
  have hBsym : ∀ x y : F, B x y = B y x := by
    intro x y
    show Q (x + y) + Q x + Q y = Q (y + x) + Q y + Q x
    rw [add_comm x y]
    ring
  have hBdiag : ∀ x : F, B x x = 0 := by
    intro x
    show Q (x + x) + Q x + Q x = 0
    rw [CharTwo.add_self_eq_zero x, hQ0, zero_add, CharTwo.add_self_eq_zero]
  obtain ⟨d, hdsym, hddiag, hBexp⟩ :=
    bilinear_frob hcard B hBx hBy hBsym hBdiag
  -- ## Step 2: the quadratic map `Q1` with polar `B`
  let Q1 : F → F := fun x => ∑ k ∈ Finset.range n,
    ∑ l ∈ (Finset.range n).filter (fun l => k < l), d k l * x ^ (2 ^ k + 2 ^ l)
  have hQ1polar : ∀ x y : F, Q1 (x + y) + Q1 x + Q1 y = B x y :=
    fun x y => polar_Q1_eq_B d hddiag hdsym B hBexp x y
  -- ## Step 3: `L = Q - Q1` is additive
  let L : F → F := fun x => Q x - Q1 x
  have hLadd : ∀ x y : F, L (x + y) = L x + L y := by
    intro x y
    have key : L (x + y) + (L x + L y) = 0 := by
      have e1 : L (x + y) + (L x + L y)
          = (Q (x + y) + Q x + Q y) - (Q1 (x + y) + Q1 x + Q1 y) := by
        show (Q (x + y) - Q1 (x + y)) + ((Q x - Q1 x) + (Q y - Q1 y))
          = (Q (x + y) + Q x + Q y) - (Q1 (x + y) + Q1 x + Q1 y)
        abel
      rw [e1, hQ1polar x y]
      exact sub_eq_zero.mpr rfl
    have h2 : L (x + y) = -(L x + L y) := eq_neg_of_add_eq_zero_left key
    rwa [CharTwo.neg_eq] at h2
  have hLfrob : ∀ x : F, L x =
      ∑ k ∈ Finset.range n, (polyRep L).coeff (2 ^ k) * x ^ (2 ^ k) :=
    additive_frob hcard L hLadd
  -- ## Step 4: equivariance of `B`, and the resonance conditions on `d`
  have hBeq : ∀ x y : F, B ((ν : F) * x) ((ν : F) * y) = (lam : F) * B x y := by
    intro x y
    show Q ((ν : F) * x + (ν : F) * y) + Q ((ν : F) * x) + Q ((ν : F) * y)
      = (lam : F) * (Q (x + y) + Q x + Q y)
    rw [← mul_add, hξ (x + y), hξ x, hξ y]
    ring
  have hdcond : ∀ k l : ℕ, k < n → l < n →
      d k l * ((ν : F) ^ (2 ^ k + 2 ^ l) - (lam : F)) = 0 := by
    apply coeff_vanishing_of_scale hcard (ν : F) (lam : F) d
    intro x y
    have h := hBeq x y
    rw [hBexp ((ν : F) * x) ((ν : F) * y), hBexp x y] at h
    rw [← scale_rewrite d n (ν : F) (lam : F) x y, sub_eq_zero]
    exact h
  -- ## Step 5: equivariance of `Q1` and of `L`
  have hQ1eq : ∀ x : F, Q1 ((ν : F) * x) = (lam : F) * Q1 x := by
    intro x
    have h2 : (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l),
          d k l * ((ν : F) * x) ^ (2 ^ k + 2 ^ l))
        - (lam : F) * (∑ k ∈ Finset.range n,
            ∑ l ∈ (Finset.range n).filter (fun l => k < l),
              d k l * x ^ (2 ^ k + 2 ^ l)) = 0 := by
      rw [scale_rewrite_Q1 d n (ν : F) (lam : F) x]
      refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun l hl => ?_))
      rw [hdcond k l (Finset.mem_range.mp hk) (Finset.mem_range.mp (Finset.mem_filter.mp hl).1),
        zero_mul]
    exact sub_eq_zero.mp h2
  have hLeq : ∀ x : F, L ((ν : F) * x) = (lam : F) * L x := by
    intro x
    show Q ((ν : F) * x) - Q1 ((ν : F) * x) = (lam : F) * (Q x - Q1 x)
    rw [hξ x, hQ1eq x, mul_sub]
  -- ## Step 6: `L = 0`
  have hnu_ne : ∀ k : ℕ, k < n → (ν : F) ^ (2 ^ k) ≠ (lam : F) := by
    have hord : orderOf (ν : F) = 2 ^ n - 1 := by
      rw [orderOf_units]; exact hν
    have hpow1 : (ν : F) ^ (2 ^ n - 1) = 1 := by
      rw [← hord]; exact pow_orderOf_eq_one (ν : F)
    have hpowN : (ν : F) ^ (2 ^ n) = (ν : F) := by
      have hp : 0 < 2 ^ n := pow_pos (by norm_num) n
      have h1 : 2 ^ n = 2 ^ n - 1 + 1 := by omega
      rw [h1, pow_add, hpow1, one_mul, pow_one]
    intro k hk hc
    apply hnotconj (n - k)
    rw [← hc, ← pow_mul, ← pow_add, Nat.add_sub_of_le (le_of_lt hk)]
    exact hpowN.symm
  have hLhyp : ∀ x : F, ∑ k ∈ Finset.range n,
      ((polyRep L).coeff (2 ^ k) * ((ν : F) ^ (2 ^ k) - (lam : F))) * x ^ (2 ^ k) = 0 := by
    intro x
    have h := hLeq x
    rw [hLfrob ((ν : F) * x), hLfrob x] at h
    have h2 : (∑ k ∈ Finset.range n, (polyRep L).coeff (2 ^ k) * ((ν : F) * x) ^ (2 ^ k))
        - (lam : F) * (∑ k ∈ Finset.range n,
            (polyRep L).coeff (2 ^ k) * x ^ (2 ^ k)) = 0 := by
      rw [sub_eq_zero]; exact h
    rw [scale_rewrite_lin (fun k => (polyRep L).coeff (2 ^ k)) n (ν : F) (lam : F) x] at h2
    exact h2
  have hLzero : ∀ x : F, L x = 0 := by
    intro x
    have hc := additive_scale_zero hcard (ν : F) (lam : F)
      (fun k => (polyRep L).coeff (2 ^ k)) hLhyp hnu_ne
    rw [hLfrob x]
    exact Finset.sum_eq_zero (fun k hk => by
      rw [hc k (Finset.mem_range.mp hk), zero_mul])
  have hQeqQ1 : ∀ x : F, Q x = Q1 x := by
    intro x
    have h0 : Q x - Q1 x = 0 := hLzero x
    exact sub_eq_zero.mp h0
  -- ## Step 7: extract the monomial
  refine monomial_extract (ν : F) (lam : F) ?_ d hdcond Q ?_ ⟨1, hQne 1 one_ne_zero⟩
  · rw [orderOf_units]; exact hν
  · intro x
    rw [hQeqQ1 x]

/-- **Core linear algebra of Higman's Lemma 11 (type `A`).**  Let `F = GF(2^n)`, let `ν`, `lam` be
primitive elements of `Fˣ` (order `2^n - 1`), and let `Q : F → F` be a quadratic map whose polar
`B α γ = Q (α + γ) + Q α + Q γ` is additive in each variable, with `Q α ≠ 0` for `α ≠ 0`, and
`Q (ν * α) = lam * Q α`.  If the `𝔽₂[ξ]`-module `F` with `ξ = ` mult by `ν` is not isomorphic to
that with `ξ = ` mult by `lam` (hypothesis `hnotconj`), then `Q` is a single monomial
`c * α ^ (2 ^ i + 2 ^ j)`, `i < j < n`, with `ν ^ (2 ^ i + 2 ^ j) = lam` and `c ≠ 0`. -/
theorem monomial_form {n : ℕ} (hn : 0 < n)
    (ν lam : (GaloisField 2 n)ˣ)
    (hν : orderOf ν = 2 ^ n - 1) (hlam : orderOf lam = 2 ^ n - 1)
    (hnotconj : ∀ s : ℕ, (ν : GaloisField 2 n) ≠ (lam : GaloisField 2 n) ^ 2 ^ s)
    (Q : GaloisField 2 n → GaloisField 2 n)
    (hQ0 : Q 0 = 0)
    (hQne : ∀ α : GaloisField 2 n, α ≠ 0 → Q α ≠ 0)
    (hadd1 : ∀ α α' γ : GaloisField 2 n,
      Q (α + α' + γ) + Q (α + α') + Q γ =
        (Q (α + γ) + Q α + Q γ) + (Q (α' + γ) + Q α' + Q γ))
    (hadd2 : ∀ α γ γ' : GaloisField 2 n,
      Q (α + (γ + γ')) + Q α + Q (γ + γ') =
        (Q (α + γ) + Q α + Q γ) + (Q (α + γ') + Q α + Q γ'))
    (hξ : ∀ α : GaloisField 2 n,
      Q ((ν : GaloisField 2 n) * α) = (lam : GaloisField 2 n) * Q α) :
    ∃ i j : ℕ, i < j ∧ j < n ∧
      (ν : GaloisField 2 n) ^ (2 ^ i + 2 ^ j) = (lam : GaloisField 2 n) ∧
      ∃ c : GaloisField 2 n, c ≠ 0 ∧ ∀ α, Q α = c * α ^ (2 ^ i + 2 ^ j) := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 n (Nat.pos_iff_ne_zero.mp hn)
  exact monomial_form_aux hcard ν lam hν hnotconj Q hQ0 hQne hadd1 hadd2 hξ

end Work.Higman
