import Mathlib
import Submission.Work.BW.extract_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivation rule for monomials (`Work.BW.gamma_rule`)

Given a family of additive "derivations" `Λ i : R → R` (additivity `hadd`, Leibniz rule
`hleib`) and elements `u j`, `D j` that agree modulo an ideal `𝔎` in the sense that
`Λ i (u j) - D j * δ_{ij} ∈ 𝔎`, this file computes `Λ i (∏ j, u j ^ γ j)` explicitly: the
"main term" `γ i * D i * ∏ l, u l ^ (decr γ i l)` plus a sum of `𝔎`-multiples of monomials.

The identity is *exact*: neither the ideal `𝔎` nor additivity is needed for the equality
itself (it follows from the Leibniz rule alone); `𝔎` only records that each correction term
lies in the ideal.

The formal proof isolates independent ingredients:

* `deriv_prod` : the Leibniz (product) rule over an arbitrary `Finset`;
* `deriv_pow`  : the power rule `Λ i (x ^ n) = n * x ^ (n-1) * Λ i x`;
* `prod_decr_eq` : the relation between `∏ l, u l ^ decr γ j l` and `∏ l ∈ univ.erase j, u l ^ γ l`;
* `final_alg`  : the purely algebraic rearrangement of the resulting sum.
-/

namespace Work.BW

open scoped BigOperators

/-- **Leibniz (product) rule.**  For a family of maps `Λ i` each satisfying the Leibniz
rule, the application of `Λ i` to a product over a finset is the sum of the products with
one factor differentiated. -/
lemma deriv_prod {ι R : Type*} [DecidableEq ι] [CommRing R]
    (Λ : ι → R → R) (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (i : ι) (s : Finset ι) (f : ι → R) :
    Λ i (∏ j ∈ s, f j) = ∑ j ∈ s, (∏ l ∈ s.erase j, f l) * Λ i (f j) := by
  classical
  have h1 : Λ i (1 : R) = 0 := by
    have h : Λ i 1 = Λ i 1 + Λ i 1 := by simpa using hleib i 1 1
    have h2 : (0 : R) = Λ i 1 := by
      have := congrArg (fun x => x - Λ i 1) h
      simpa using this
    exact h2.symm
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, hleib, ih, Finset.mul_sum, Finset.sum_insert ha]
      rw [Finset.erase_insert ha]
      rw [show ∑ x ∈ s, (∏ l ∈ (insert a s).erase x, f l) * Λ i (f x)
            = ∑ x ∈ s, f a * ((∏ l ∈ s.erase x, f l) * Λ i (f x)) from
          Finset.sum_congr rfl (fun x hx => by
            have hax : a ≠ x := by rintro rfl; exact ha hx
            have hna : a ∉ s.erase x := fun h => ha (Finset.mem_of_mem_erase h)
            rw [Finset.erase_insert_of_ne hax, Finset.prod_insert hna]
            ring)]
      rw [mul_comm (Λ i (f a)) (∏ x ∈ s, f x)]

/-- **Power rule, successor form.**  `Λ i (x ^ (n+1)) = (n+1) * x ^ n * Λ i x`. -/
lemma deriv_pow_succ {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (i : Fin ℓ) (x : R) (n : ℕ) :
    Λ i (x ^ (n + 1)) = ((n + 1 : ℕ) : R) * x ^ n * Λ i x := by
  have h1 : Λ i (1 : R) = 0 := by
    have h : Λ i 1 = Λ i 1 + Λ i 1 := by simpa using hleib i 1 1
    have h2 : (0 : R) = Λ i 1 := by
      have := congrArg (fun x => x - Λ i 1) h
      simpa using this
    exact h2.symm
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, hleib, ih]
    have h2 : ((n + 1 : ℕ) : R) * x ^ n * Λ i x * x
        = ((n + 1 : ℕ) : R) * x ^ n.succ * Λ i x := by
      rw [show ((n + 1 : ℕ) : R) * x ^ n * Λ i x * x
            = ((n + 1 : ℕ) : R) * (x ^ n * x) * Λ i x by ring, ← pow_succ]
    rw [h2]
    have hc : ((Nat.succ n + 1 : ℕ) : R) = ((n + 1 : ℕ) : R) + 1 := by
      push_cast; ring
    rw [hc, pow_succ']
    ring

/-- **Power rule.**  `Λ i (x ^ n) = n * x ^ (n-1) * Λ i x`, with the convention
`x ^ (n - 1) = x ^ 0 = 1` when `n = 0` (the coefficient `n` then vanishes). -/
lemma deriv_pow {R : Type*} [CommRing R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (i : Fin ℓ) (x : R) (n : ℕ) :
    Λ i (x ^ n) = (n : R) * x ^ (n - 1) * Λ i x := by
  cases n with
  | zero =>
    have h1 : Λ i (1 : R) = 0 := by
      have h : Λ i 1 = Λ i 1 + Λ i 1 := by simpa using hleib i 1 1
      have h2 : (0 : R) = Λ i 1 := by
        have := congrArg (fun x => x - Λ i 1) h
        simpa using this
      exact h2.symm
    simpa using h1
  | succ n =>
    rw [deriv_pow_succ Λ hleib i x n]
    simp

/-- Splitting the product `∏ l, u l ^ decr γ j l` at the index `j`, where `decr` lowers the
`j`-th exponent. -/
lemma prod_decr_eq {R : Type*} [CommRing R] {ℓ : ℕ} (u : Fin ℓ → R) (γ : Fin ℓ → ℕ) (j : Fin ℓ) :
    (∏ l, u l ^ decr γ j l) = u j ^ (γ j - 1) * (∏ l ∈ Finset.univ.erase j, u l ^ γ l) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun l => u l ^ decr γ j l) (Finset.mem_univ j)]
  congr 1
  · simp [decr]
  · refine Finset.prod_congr rfl (fun l hl => ?_)
    rw [decr, Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- Algebraic rearrangement: the "main term plus the sum of corrections" equals the sum of
the naive Leibniz terms.  The only index that contributes to the correction sum is `i`. -/
lemma final_alg {R : Type*} [CommRing R] {ℓ : ℕ}
    (M c A d : Fin ℓ → R) (i : Fin ℓ) :
    c i * d i * M i
      + ∑ j, M j * (c j * (A j - d j * (if i = j then (1 : R) else 0)))
      = ∑ j, c j * M j * A j := by
  have hsplit : ∑ j, M j * (c j * (A j - d j * (if i = j then (1 : R) else 0)))
      = ∑ j, M j * (c j * A j)
        - ∑ j, M j * (c j * (d j * (if i = j then (1 : R) else 0))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hdelta : ∑ j, M j * (c j * (d j * (if i = j then (1 : R) else 0)))
      = M i * (c i * d i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsum : ∑ j, M j * (c j * A j) = ∑ j, c j * M j * A j :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsplit, hdelta, hsum]
  ring

/-- The derivation rule for monomials: applying `Λ i` to `∏ j, u j ^ γ j` peels off the expected main term plus an explicit sum of `𝔎`-multiples of monomials. -/
theorem gamma_rule {R : Type*} [CommRing R] {ℓ : ℕ}
    (𝔎 : Ideal R) (Λ : Fin ℓ → R → R) (u D : Fin ℓ → R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y)
    (hleib : ∀ i x y, Λ i (x * y) = Λ i x * y + x * Λ i y)
    (hcong : ∀ i j, Λ i (u j) - D j * (if i = j then (1 : R) else 0) ∈ 𝔎)
    (i : Fin ℓ) (γ : Fin ℓ → ℕ) :
    Λ i (∏ j, u j ^ γ j) =
      (γ i : R) * D i * (∏ l, u l ^ decr γ i l)
        + ∑ j, (∏ l, u l ^ decr γ j l) * ((γ j : R) *
            (Λ i (u j) - D j * (if i = j then (1 : R) else 0))) := by
  have hclean : Λ i (∏ j, u j ^ γ j)
      = ∑ j, (γ j : R) * (∏ l, u l ^ decr γ j l) * Λ i (u j) := by
    rw [deriv_prod Λ hleib i Finset.univ (fun j => u j ^ γ j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [deriv_pow Λ hleib i (u j) (γ j), prod_decr_eq u γ j]
    ring
  rw [hclean]
  exact (final_alg (fun j => ∏ l, u l ^ decr γ j l) (fun j => (γ j : R))
    (fun j => Λ i (u j)) D i).symm

end Work.BW
