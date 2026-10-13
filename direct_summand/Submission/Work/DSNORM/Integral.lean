import Submission.Work.DSNORM.InForm
import Submission.Work.DSNORM.dvd_of_pow_dvd_pow_add
import Submission.Work.DSNORM.exists_pow_mul_eq_of_isIntegral

/-!
# DSNORM — a regular local ring is integrally closed

This file contains the main argument.

* `Work.DSNORM.inForm_dvd_of_isIntegral`: if `a / b` is integral over `A` (with `a`, `b ≠ 0`) then
  the initial form of `b` divides the initial form of `a`.  This is the way the integrality
  relation is projected to the associated graded ring `k[X₁,…,X_d]`, where unique factorization
  turns asymptotic divisibility of powers into divisibility.
* `Work.DSNORM.exists_sub_mul_mem_pow`: successive approximation — for every `n` there is `q`
  with `a - q * b ∈ 𝔪 ^ n`.
* `Work.DSNORM.dvd_of_isIntegral`: hence `b ∣ a`, by Krull's intersection theorem applied in
  `A ⧸ (b)`.
* `Work.DSNORM.isIntegrallyClosed_of_isRegularLocalRing`: a regular local ring is integrally closed.
-/

namespace Work.DSNORM

open scoped Pointwise

universe u

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- **Projecting the integrality relation to the associated graded ring.**  If `a / b` is integral
over the regular local ring `A` with `a`, `b ≠ 0`, then `inForm b ∣ inForm a`. -/
theorem inForm_dvd_of_isIntegral {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hint : IsIntegral A (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) :
    inForm A b ∣ inForm A a := by
  classical
  obtain ⟨N, hN, hpow⟩ := exists_pow_mul_eq_of_isIntegral (A := A) hb hint
  have hfb : inForm A b ≠ 0 := (inForm_ne_zero_iff A b).mpr hb
  have hfa : inForm A a ≠ 0 := (inForm_ne_zero_iff A a).mpr ha
  refine dvd_of_pow_dvd_pow_add hfb hfa (N - 1) fun m => ?_
  obtain ⟨u, hu⟩ := hpow (m + (N - 1))
  have hu0 : u ≠ 0 := fun h0 => (mul_ne_zero (pow_ne_zero _ hb) (pow_ne_zero _ ha))
    (by rw [hu, h0, mul_zero])
  have hcancel : (inForm A b) ^ (N - 1) * (inForm A a) ^ (m + (N - 1))
      = (inForm A b) ^ (N - 1) * ((inForm A b) ^ m * inForm A u) := by
    have h1 : (inForm A b) ^ (N - 1) * (inForm A a) ^ (m + (N - 1))
        = (inForm A b) ^ (m + (N - 1)) * inForm A u := by
      have h2 := congrArg (inForm A) hu
      rwa [inForm_mul A (pow_ne_zero _ hb) (pow_ne_zero _ ha), inForm_pow A b hb,
        inForm_pow A a ha, inForm_mul A (pow_ne_zero _ hb) hu0, inForm_pow A b hb] at h2
    rw [h1, ← mul_assoc, ← pow_add, Nat.add_comm]
  exact ⟨inForm A u, mul_left_cancel₀ (pow_ne_zero _ hfb) hcancel⟩

/-- **Successive approximation.**  If `a / b` is integral over `A` then, for every `n`, `a` differs
from a multiple of `b` by an element of `𝔪 ^ n`. -/
theorem exists_sub_mul_mem_pow {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hint : IsIntegral A (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) :
    ∀ n : ℕ, ∃ q : A, a - q * b ∈ IsLocalRing.maximalIdeal A ^ n := by
  have hbK : algebraMap A (FractionRing A) b ≠ 0 := fun h =>
    hb (IsFractionRing.injective A (FractionRing A) (by simpa using h))
  intro n
  induction n with
  | zero =>
      exact ⟨0, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      by_cases hzero : a - q * b = 0
      · exact ⟨q, by rw [hzero]; exact Submodule.zero_mem _⟩
      · set u := a - q * b with hu
        have hu0 : u ≠ 0 := hzero
        have hint' : IsIntegral A
            (algebraMap A (FractionRing A) u / algebraMap A (FractionRing A) b) := by
          have hsub : algebraMap A (FractionRing A) u / algebraMap A (FractionRing A) b
              = algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b
                - algebraMap A (FractionRing A) q := by
            rw [hu, map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ hbK]
          rw [hsub]
          exact hint.sub isIntegral_algebraMap
        obtain ⟨q', hq' | hq'⟩ :=
          exists_ordNat_lt_of_dvd A hu0 hb (inForm_dvd_of_isIntegral A hu0 hb hint')
        · refine ⟨q + q', ?_⟩
          have h1 : a = (q + q') * b := by
            have h2 : a = u + q * b := by rw [hu]; ring
            rw [h2, hq']
            ring
          rw [h1, sub_self]
          exact Submodule.zero_mem _
        · have hune : u - q' * b ≠ 0 := fun h0 => by
            rw [h0, ordNat_zero A] at hq'
            omega
          refine ⟨q + q', ?_⟩
          have h1 : a - (q + q') * b = u - q' * b := by rw [hu]; ring
          have hle_u : n ≤ ordNat A u := le_ordNat_of_mem A hu0 hq
          have hle : n + 1 ≤ ordNat A (u - q' * b) :=
            le_trans (Nat.succ_le_succ hle_u) (Nat.succ_le_of_lt hq')
          rw [h1]
          exact Ideal.pow_le_pow_right hle (mem_pow_ordNat A (u - q' * b))

/-- If the fraction `a / b` is integral over the regular local ring `A` and `a ≠ 0`, then
`b ∣ a`. -/
theorem dvd_of_isIntegral {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hint : IsIntegral A (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b)) :
    b ∣ a := by
  classical
  by_cases hunit : IsUnit b
  · exact hunit.dvd
  · have hbmem : b ∈ IsLocalRing.maximalIdeal A := by
      by_contra h
      exact hunit (IsLocalRing.notMem_maximalIdeal.mp h)
    haveI hnt : Nontrivial (A ⧸ Ideal.span {b}) :=
      Work.DSREG.nontrivial_quotient_span_singleton hbmem
    letI : IsLocalRing (A ⧸ Ideal.span {b}) := Work.DSREG.quotientIsLocalRing A (Ideal.span {b})
    set J : Ideal (A ⧸ Ideal.span {b}) :=
      (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {b})) with hJ
    have hJne : J ≠ ⊤ := by
      intro htop
      have h1 : (1 : A ⧸ Ideal.span {b}) ∈ J := by rw [htop]; exact Submodule.mem_top
      rw [hJ, Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (Ideal.span {b}))
        Ideal.Quotient.mk_surjective] at h1
      obtain ⟨m, hm, hm1⟩ := h1
      have h2 : (1 : A) - m ∈ Ideal.span {b} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hm1, sub_self]
      have hle : Ideal.span {b} ≤ IsLocalRing.maximalIdeal A :=
        (Ideal.span_singleton_le_iff_mem (IsLocalRing.maximalIdeal A)).mpr hbmem
      have h3 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        have h4 : m + (1 - m) ∈ IsLocalRing.maximalIdeal A :=
          (IsLocalRing.maximalIdeal A).add_mem hm (hle h2)
        rwa [add_sub_cancel] at h4
      exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one h3
    have hkrull : (⨅ n : ℕ, J ^ n) = (⊥ : Ideal (A ⧸ Ideal.span {b})) :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing J hJne
    have haJ : ∀ n : ℕ, (Ideal.Quotient.mk (Ideal.span {b})) a ∈ J ^ n := by
      intro n
      obtain ⟨q, hq⟩ := exists_sub_mul_mem_pow A ha hb hint n
      have h1 : (Ideal.Quotient.mk (Ideal.span {b})) (a - q * b)
          = (Ideal.Quotient.mk (Ideal.span {b})) a := by
        rw [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self b),
          mul_zero, sub_zero]
      rw [← h1, hJ, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hq
    have hzero : (Ideal.Quotient.mk (Ideal.span {b})) a = 0 := by
      have hbot : (Ideal.span {(Ideal.Quotient.mk (Ideal.span {b})) a}) ≤ ⊥ := by
        rw [← hkrull]
        refine le_iInf fun n => ?_
        rw [Ideal.span_singleton_le_iff_mem]
        exact haJ n
      have := hbot (Ideal.mem_span_singleton_self _)
      simpa using this
    rw [Ideal.Quotient.eq_zero_iff_mem] at hzero
    rwa [Ideal.mem_span_singleton] at hzero

/-- **A regular local ring is integrally closed.** -/
theorem isIntegrallyClosed_of_isRegularLocalRing : IsIntegrallyClosed A := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨a, b, hb, hba⟩ := IsFractionRing.div_surjective A x
  have hb' : b ≠ 0 := by
    rintro rfl
    exact one_ne_zero ((mem_nonZeroDivisors_iff.mp hb).2 1 (by simp))
  rw [← hba] at hx
  by_cases ha : a = 0
  · refine ⟨0, ?_⟩
    rw [ha, map_zero, zero_div] at hba
    simpa using hba
  · have hbK : algebraMap A (FractionRing A) b ≠ 0 := fun h =>
      hb' (IsFractionRing.injective A (FractionRing A) (by simpa using h))
    obtain ⟨c, hc⟩ := dvd_of_isIntegral A ha hb' hx
    refine ⟨c, ?_⟩
    rw [← hba, hc, map_mul, mul_div_cancel_left₀ (algebraMap A (FractionRing A) c) hbK]

end Work.DSNORM
