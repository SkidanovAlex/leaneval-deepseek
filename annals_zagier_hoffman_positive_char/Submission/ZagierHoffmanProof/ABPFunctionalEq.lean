import Submission.ZagierHoffmanProof.ABPClincher

/-!
# The clincher relation produced by a functional equation with Frobenius twists

Let `E ∈ K⟦t⟧` be a power series over a ring of characteristic `p` (with `FrobPow K q`), and
suppose that

  `a₀ E + a₁ E^{(1)} + ⋯ + a_ℓ E^{(ℓ)} = 0`

with `aᵢ ∈ K[t]`, where `E^{(i)}` is the `i`-fold Frobenius twist (`coeff k (E^{(i)}) =
(coeff k E) ^ (q^i)`).  If `m` is the order of vanishing of `E` at `0` (so `λ := coeff m E` is the
leading coefficient of the Maclaurin expansion of `E`), then evaluating the identity at `t = 0`
gives

  `∑ᵢ aᵢ(0) · λ ^ (q^i) = 0`.

The point: the exponents `q^i` are **nonnegative**, so this is exactly the input of
`ZagierHoffmanPositiveChar.clincher` (applied to the polynomial `∑ᵢ aᵢ(0) X^(q^i)`), with no
`q`-th roots anywhere.  This is ABP's Step 5 (`a₀(0)λ^{q^0} + ⋯ + a_ℓ(0)λ^{q^{-ℓ}} = 0`,
re-indexed so that all powers are nonnegative).
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {q : ℕ} [FrobPow K q]

/-- The `m`-th coefficient of a Frobenius twist is the `q^i`-th power of the `m`-th coefficient. -/
@[simp] lemma coeff_frobTwist_eq (i m : ℕ) (E : PowerSeries K) :
    PowerSeries.coeff m (frobTwist (R := K) (p := q) i E)
      = (PowerSeries.coeff m E) ^ (q ^ i) :=
  frobTwist_coeff i E m

/-- Multiplying by a polynomial `a` and twisting: if all coefficients of `E` below `m` vanish,
then the `m`-th coefficient of `a · E^{(i)}` is `a(0) · (coeff m E)^(q^i)`. -/
lemma coeff_mul_frobTwist_of_ord {E : PowerSeries K} {a : Polynomial K} {m : ℕ}
    (hm : ∀ k < m, PowerSeries.coeff k E = 0) (i : ℕ) :
    PowerSeries.coeff m ((a : PowerSeries K) * frobTwist (R := K) (p := q) i E)
      = a.coeff 0 * (PowerSeries.coeff m E) ^ (q ^ i) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0, m)]
  · rw [Polynomial.coeff_coe, frobTwist_coeff]
  · intro p hp hne
    have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
    have hp1 : p.1 ≠ 0 := by
      intro h0
      exact hne (Prod.ext h0 (by omega))
    have hlt : p.2 < m := by omega
    rw [frobTwist_coeff, hm p.2 hlt, Polynomial.coeff_coe,
      zero_pow (pow_ne_zero _ (FrobPow.ne_zero K)), mul_zero]
  · intro h0
    exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h0

/-- ★★★ **The clincher relation from a twisted functional equation.**  From
`∑ᵢ aᵢ E^{(i)} = 0` and the vanishing of the coefficients of `E` below order `m` one obtains
`∑ᵢ aᵢ(0) (coeff m E)^(q^i) = 0`. -/
theorem sum_coeff_eq_zero_of_sum_frobTwist {E : PowerSeries K} {m ℓ : ℕ}
    (hm : ∀ k < m, PowerSeries.coeff k E = 0) {a : ℕ → Polynomial K}
    (h : ∑ i ∈ Finset.range (ℓ + 1), (a i : PowerSeries K) * frobTwist (R := K) (p := q) i E = 0) :
    ∑ i ∈ Finset.range (ℓ + 1), (a i).coeff 0 * (PowerSeries.coeff m E) ^ (q ^ i) = 0 := by
  have hc := congrArg (PowerSeries.coeff m) h
  simpa only [map_sum, map_mul, map_zero, coeff_mul_frobTwist_of_ord hm] using hc

section relation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

omit [FrobPow K q] in
/-- ★★★ **The clincher bound from a frobenius-power relation.**  If
`∑ᵢ cᵢ λ^(q^i) = 0` with the nonzero `cᵢ` integral and bounded by `A`, `q ≥ 2` and `λ ≠ 0`, then
`1 ≤ A · v λ`.  This is ABP's Step 5: it is obtained by applying the Liouville inequality
`clincher` to the polynomial `∑ᵢ cᵢ X^(q^i)`. -/
theorem le_mul_v_of_sum_pow_eq_zero {c : ℕ → K} {ℓ : ℕ} {A : Γ₀} (hq : 2 ≤ q)
    (hint : ∀ i, c i ≠ 0 → 1 ≤ Valued.v (c i)) (hbound : ∀ i, Valued.v (c i) ≤ A)
    (hne : ∃ i ∈ Finset.range (ℓ + 1), c i ≠ 0) {lam : K} (hlam : lam ≠ 0)
    (h : ∑ i ∈ Finset.range (ℓ + 1), c i * lam ^ (q ^ i) = 0) :
    1 ≤ A * Valued.v lam := by
  classical
  set f : Polynomial K := ∑ i ∈ Finset.range (ℓ + 1), Polynomial.monomial (q ^ i) (c i) with hf
  have hinj : Function.Injective fun i => q ^ i := Nat.pow_right_injective hq
  have hcoeff : ∀ k : ℕ, f.coeff k
      = ∑ i ∈ (Finset.range (ℓ + 1)).filter (fun i => q ^ i = k), c i := by
    intro k
    rw [hf, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [← Finset.sum_filter]
  have hsingle : ∀ k i, i ∈ (Finset.range (ℓ + 1)).filter (fun i => q ^ i = k) →
      ∑ j ∈ (Finset.range (ℓ + 1)).filter (fun j => q ^ j = k), c j = c i := by
    intro k i hi
    refine Finset.sum_eq_single i ?_ ?_
    · intro b hb hbi
      exfalso
      rw [Finset.mem_filter] at hb hi
      exact hbi (hinj (hb.2.trans hi.2.symm))
    · intro h
      exact absurd hi h
  have hf_ne : f ≠ 0 := by
    obtain ⟨i, hi, hci⟩ := hne
    intro hf0
    have h1 : f.coeff (q ^ i) = c i := by
      rw [hcoeff]
      exact hsingle (q ^ i) i (Finset.mem_filter.mpr ⟨hi, rfl⟩)
    have h0 : f.coeff (q ^ i) = 0 := by rw [hf0]; simp
    rw [h1] at h0
    exact hci h0
  refine clincher hf_ne (fun k hk => ?_) (fun k => ?_) hlam ?_
  · have hne' : ((Finset.range (ℓ + 1)).filter (fun i => q ^ i = k)).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hcoeff k, h, Finset.sum_empty] at hk
      exact hk rfl
    obtain ⟨i, hi⟩ := hne'
    rw [hcoeff k, hsingle k i hi]
    exact hint i (fun hc => hk (by rw [hcoeff k, hsingle k i hi, hc]))
  · by_cases h : ((Finset.range (ℓ + 1)).filter (fun i => q ^ i = k)).Nonempty
    · obtain ⟨i, hi⟩ := h
      rw [hcoeff k, hsingle k i hi]
      exact hbound i
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hcoeff k, h, Finset.sum_empty, map_zero (Valued.v)]
      exact zero_le
  · rw [hf, Polynomial.eval_finsetSum]
    rw [show (∑ i ∈ Finset.range (ℓ + 1), Polynomial.eval lam (Polynomial.monomial (q ^ i) (c i)))
        = ∑ i ∈ Finset.range (ℓ + 1), c i * lam ^ (q ^ i) from
      Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]]
    exact h

end relation


end ZagierHoffmanPositiveChar
