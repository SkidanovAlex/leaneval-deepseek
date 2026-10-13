import Mathlib
import Submission.Work.DSM2p.sum_pow_sub_mem

/-!
# `Work.DSM2p.N4b_expand_pow_root`

Node **N4b** of the H2 design: coefficientwise `p`-th roots of `r(X^p)` modulo `ϖ₁ ^ p`.

Assume `(p : C) ∈ (ϖ₁ ^ p)` (`hp`) and that every `c : C` is congruent to a `p`-th power
modulo `(ϖ₁ ^ p)` (`hsurj`).  Then for every polynomial `r` there is `r'` with

`r(X^p) ≡ r'^p   (mod (ϖ₁ ^ p))`,

i.e. `(Polynomial.expand C p) r - r' ^ p ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)}`.

*Proof.*  For each coefficient `cᵢ = r.coeff i` pick `bᵢ` with `cᵢ - bᵢ ^ p ∈ (ϖ₁ ^ p)` and set
`r' = ∑ᵢ bᵢ X^i`, the sum running over the support of `r`.  Then
`r(X^p) = ∑ᵢ cᵢ X^{ip}` and, since `p ∈ (ϖ₁ ^ p)`, the `p`-th power map of `C[X]` is additive
modulo `(ϖ₁ ^ p)` (`N4b_frob_sum_sub_mem`, which is the finite-sum form of
`sum_pow_sub_mem`), so `r'^p ≡ ∑ᵢ bᵢ ^ p X^{ip}`.  Both remainders are killed by the ideal:
`cᵢ - bᵢ ^ p ∈ (ϖ₁ ^ p)` coefficientwise, and the Frobenius cross terms are multiples of `p`.
-/

namespace Work.DSM2p

open Polynomial

/-- **Frobenius difference for finite sums.**  If `(p : R) ∈ Ideal.span {ϖ ^ p}`, then for any
finite family `f` the difference `(∑ i ∈ s, f i) ^ p - ∑ i ∈ s, (f i) ^ p` also lies in
`Ideal.span {ϖ ^ p}`; this is the `Finset` form of `sum_pow_sub_mem`. -/
theorem N4b_frob_sum_sub_mem {R : Type*} [CommRing R] {ι : Type*} {p : ℕ} (hp : p.Prime)
    (ϖ : R) (h : (p : R) ∈ Ideal.span {ϖ ^ p}) (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p - ∑ i ∈ s, (f i) ^ p ∈ Ideal.span {ϖ ^ p} := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow hp.ne_zero, sub_zero]
    exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxy : (f a + ∑ i ∈ s, f i) ^ p - (f a) ^ p - (∑ i ∈ s, f i) ^ p ∈
        Ideal.span {ϖ ^ p} := sum_pow_sub_mem hp ϖ h _ _
    have hsplit : (f a + ∑ i ∈ s, f i) ^ p - ((f a) ^ p + ∑ i ∈ s, (f i) ^ p)
        = ((f a + ∑ i ∈ s, f i) ^ p - (f a) ^ p - (∑ i ∈ s, f i) ^ p)
          + ((∑ i ∈ s, f i) ^ p - ∑ i ∈ s, (f i) ^ p) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ hxy ih

theorem N4b_expand_pow_root {C : Type*} [CommRing C] (p : ℕ) [Fact p.Prime]
    (ϖ₁ : C) (hp : (p : C) ∈ Ideal.span {ϖ₁ ^ p})
    (hsurj : ∀ c : C, ∃ b : C, c - b ^ p ∈ Ideal.span {ϖ₁ ^ p})
    (r : Polynomial C) :
    ∃ r' : Polynomial C,
      (Polynomial.expand C p) r - r' ^ p ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
  classical
  have hpp : p.Prime := Fact.out
  -- For every coefficient `c` of `r` choose a `p`-th root `b c` modulo `ϖ₁ ^ p`.
  choose b hb using hsurj
  set J : Ideal (Polynomial C) := Ideal.span {Polynomial.C (ϖ₁ ^ p)} with hJdef
  -- `p` itself is a multiple of `C (ϖ₁ ^ p)` inside `C[X]`.
  have hpI : (p : Polynomial C) ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
    obtain ⟨x0, hx0⟩ := Ideal.mem_span_singleton'.mp hp
    exact Ideal.mem_span_singleton'.mpr
      ⟨Polynomial.C x0, by rw [← Polynomial.C_mul, hx0]; exact map_natCast (Polynomial.C) p⟩
  have hpC : (p : Polynomial C) ∈ Ideal.span {(Polynomial.C ϖ₁) ^ p} := by
    rw [← Polynomial.C_pow]; exact hpI
  -- The three relevant polynomials: `A = r(X^p)`, `B = ∑ bᵢ ^ p X^{ip}` and `r'`.
  set A : Polynomial C := ∑ i ∈ r.support, Polynomial.C (r.coeff i) * Polynomial.X ^ (p * i)
    with hAdef
  set B : Polynomial C :=
    ∑ i ∈ r.support, Polynomial.C ((b (r.coeff i)) ^ p) * Polynomial.X ^ (p * i) with hBdef
  set r' : Polynomial C := ∑ i ∈ r.support, Polynomial.C (b (r.coeff i)) * Polynomial.X ^ i
    with hr'def
  -- `expand` of a polynomial, as a sum over its support.
  have hE : (Polynomial.expand C p) r = A := by
    rw [hAdef, Polynomial.expand_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_mul]
  -- `A - B` is a sum of coefficients `C cᵢ - C (bᵢ ^ p) ∈ J`, hence lies in `J`.
  have hAB : A - B ∈ J := by
    rw [hAdef, hBdef, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ ?_
    intro i _
    have hc : Polynomial.C (r.coeff i) - Polynomial.C ((b (r.coeff i)) ^ p) ∈ J := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hb (r.coeff i))
      rw [hJdef]
      refine Ideal.mem_span_singleton'.mpr ⟨Polynomial.C a, ?_⟩
      rw [← Polynomial.C_mul, ha, map_sub]
    have hthis : Polynomial.C (r.coeff i) * Polynomial.X ^ (p * i)
        - Polynomial.C ((b (r.coeff i)) ^ p) * Polynomial.X ^ (p * i)
        = (Polynomial.C (r.coeff i) - Polynomial.C ((b (r.coeff i)) ^ p))
          * Polynomial.X ^ (p * i) := by ring
    rw [hthis]
    exact Ideal.mul_mem_right _ J hc
  -- `r'^p ≡ B` modulo `J`: Frobenius is additive modulo `(p) ⊆ J`.
  have hRB : r' ^ p - B ∈ J := by
    have hsum := N4b_frob_sum_sub_mem hpp (Polynomial.C ϖ₁) hpC r.support
      (fun i => Polynomial.C (b (r.coeff i)) * Polynomial.X ^ i)
    have hBs : (∑ i ∈ r.support, (Polynomial.C (b (r.coeff i)) * Polynomial.X ^ i) ^ p) = B := by
      rw [hBdef]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, Nat.mul_comm i p]
    rw [hBs] at hsum
    have hspan : Ideal.span {(Polynomial.C ϖ₁) ^ p} = J := by rw [hJdef, Polynomial.C_pow]
    rw [hspan] at hsum
    rw [hr'def]
    exact hsum
  refine ⟨r', ?_⟩
  have hcomb : (Polynomial.expand C p) r - r' ^ p = (A - B) - (r' ^ p - B) := by
    rw [hE]; ring
  rw [hcomb]
  exact Ideal.sub_mem _ hAB hRB

end Work.DSM2p
