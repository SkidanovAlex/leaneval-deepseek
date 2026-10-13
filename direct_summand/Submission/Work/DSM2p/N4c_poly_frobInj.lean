import Mathlib
import Submission.Work.DSM2p.N4c_frob_sum_monomial_sub_mem
import Submission.Work.DSM2p.N4c_coeff_sum_monomial_mul
import Submission.Work.DSM2p.N4c_mem_span_C_of_coeff_mem

/-!
# `Work.DSM2p.N4c_poly_frobInj` — coefficientwise Frobenius injectivity on `C[X]`

If `p` is a prime, `ϖ₁ : C` is such that `(p : C) ∈ (ϖ₁ ^ p)`, and the Frobenius
`x ↦ x ^ p` is injective modulo `(ϖ₁ ^ p)` on the coefficient ring `C`
(`hinjF`), then the *polynomial* Frobenius `H ↦ H ^ p` is injective modulo
`(C (ϖ₁ ^ p))` on `C[X]`: `H ^ p ∈ (ϖ₁ ^ p)` forces `H ∈ (ϖ₁)`.

The proof is the "Frobenius defect modulo `p`" argument.  Write
`F := ∑ i ∈ H.support, monomial (i * p) (H.coeff i ^ p)` for the *coefficientwise*
`p`-th power of `H`.  Modulo `p` the two agree,

    H ^ p - F ∈ Ideal.span {Polynomial.C (p : C)}

(`N4c_frob_sum_monomial_sub_mem`: the mixed multinomial coefficients of
`(∑ i, m i)^p` are all divisible by `p`).  Since `(p : C) ∈ (ϖ₁ ^ p)` we get
`C (p : C) ∈ (C (ϖ₁ ^ p))`, hence `F ∈ (C (ϖ₁ ^ p))` as well.  Extracting the
coefficient of `X ^ (n * p)` from `F` (`N4c_coeff_sum_monomial_mul`) shows
`(H.coeff n) ^ p ∈ (ϖ₁ ^ p)` for every `n`, so `hinjF` gives `H.coeff n ∈ (ϖ₁)`.
Finally `N4c_mem_span_C_of_coeff_mem` assembles the coefficients into
`H ∈ Ideal.span {Polynomial.C ϖ₁}`.
-/

namespace Work.DSM2p

theorem N4c_poly_frobInj {C : Type*} [CommRing C] (p : ℕ) [Fact p.Prime]
    (ϖ₁ : C) (hp : (p : C) ∈ Ideal.span {ϖ₁ ^ p})
    (hinjF : ∀ b : C, b ^ p ∈ Ideal.span {ϖ₁ ^ p} → b ∈ Ideal.span {ϖ₁})
    (H : Polynomial C) (hH : H ^ p ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)}) :
    H ∈ Ideal.span {Polynomial.C ϖ₁} := by
  have hpp : p.Prime := Fact.out
  -- The coefficientwise `p`-th power of `H`.
  set F : Polynomial C := ∑ i ∈ H.support, Polynomial.monomial (i * p) (H.coeff i ^ p)
    with hFdef
  -- ## Step 1: `H ^ p` and `F` agree modulo `(p)`.
  have hA : H ^ p - F ∈ Ideal.span {Polynomial.C (p : C)} := by
    have h0 := N4c_frob_sum_monomial_sub_mem p hpp H.support H.coeff
    have hsum1 : (∑ i ∈ H.support, Polynomial.monomial i (H.coeff i)) = H := by
      rw [← Polynomial.sum_def]; exact Polynomial.sum_monomial_eq H
    have hsum2 : (∑ i ∈ H.support, (Polynomial.monomial i (H.coeff i)) ^ p)
        = ∑ i ∈ H.support, Polynomial.monomial (i * p) (H.coeff i ^ p) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Polynomial.monomial_pow]
    rw [hsum1, hsum2] at h0
    rw [← hFdef] at h0
    exact h0
  -- ## Step 2: `(p) ⊆ (ϖ₁ ^ p)` as ideals of `C[X]`.
  have hpC : Polynomial.C (p : C) ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hp
    rw [hc, Polynomial.C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hspan_le : Ideal.span {Polynomial.C (p : C)} ≤ Ideal.span {Polynomial.C (ϖ₁ ^ p)} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpC)
  -- ## Step 3: hence `F ∈ (C (ϖ₁ ^ p))`.
  have hFmem : F ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} := by
    have h1' : H ^ p - (H ^ p - F) ∈ Ideal.span {Polynomial.C (ϖ₁ ^ p)} :=
      Ideal.sub_mem _ hH (hspan_le hA)
    rwa [sub_sub_cancel] at h1'
  -- ## Step 4: coefficient extraction gives `H.coeff n ^ p ∈ (ϖ₁ ^ p)`.
  have hcoeff : ∀ n, H.coeff n ^ p ∈ Ideal.span {ϖ₁ ^ p} := by
    intro n
    obtain ⟨G, hG⟩ := Ideal.mem_span_singleton.mp hFmem
    by_cases hn : n ∈ H.support
    · have hFn : F.coeff (n * p) = H.coeff n ^ p := by
        rw [hFdef,
          N4c_coeff_sum_monomial_mul p hpp H.support (fun i => H.coeff i ^ p) n]
        simp [hn]
      rw [← hFn, hG, Polynomial.coeff_C_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
    · have hz : H.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
      rw [hz, zero_pow hpp.ne_zero]
      exact Ideal.zero_mem _
  -- ## Step 5: assemble the coefficients.
  exact N4c_mem_span_C_of_coeff_mem ϖ₁ H (fun n => hinjF _ (hcoeff n))

end Work.DSM2p
