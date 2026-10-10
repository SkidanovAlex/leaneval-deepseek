import Mathlib
import Submission.Work.MotK.TGen.ZPlaneModel

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 8000000

namespace Work.MotK.TGen

open MvPolynomial

/-!
# `zA` is a non-zero-divisor modulo `(zg)`

`zA` and `zg` depend only on the two variables `x₁, x₂` (`zA = rename zEmb zpA`,
`zg = rename zEmb ZElim2`), and the hypothesis `IsDomain (ZD K a b h)` says that
`ZElim2` is a prime element of `K[x₁,x₂]`.  Since `K[x₀,x₁,x₂] = K[x₁,x₂][x₀]`, the
element `zg` is prime there too, and it does not divide `zA` (which has degree `2`
in `x₂` whereas `zg` has degree `5`).  Hence `zg` is prime and `zg ∤ zA`, which gives
the cancellation.
-/

/-- `finSuccEquiv` turns `rename zEmb` (the inclusion `K[x₁,x₂] → K[x₀,x₁,x₂]`) into the
constant-coefficient inclusion.  (Self-contained copy; a same-named lemma in `zF1Div` would
clash in modules importing both.) -/
theorem zA_finSuccEquiv_rename_zEmb (K : Type) [Field K] (q : MvPolynomial (Fin 2) K) :
    MvPolynomial.finSuccEquiv K 2 (MvPolynomial.rename zEmb q) = Polynomial.C q := by
  have hz : zEmb = Fin.succ := by funext i; fin_cases i <;> rfl
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.rename_C, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      have h1 : MvPolynomial.rename zEmb (p * MvPolynomial.X i)
          = MvPolynomial.rename zEmb p * MvPolynomial.X (zEmb i) := by
        rw [map_mul, MvPolynomial.rename_X]
      rw [h1]
      simp only [map_mul]
      rw [hp]
      have hXi : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X (zEmb i))
          = Polynomial.C (MvPolynomial.X i) := by
        rw [hz]; exact MvPolynomial.finSuccEquiv_X_succ
      rw [hXi, ← Polynomial.C_mul]

private lemma degreeOf_zA (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) :
    MvPolynomial.degreeOf (2 : Fin 3) (zA K a b h) = 2 := by
  have hneg : ∀ p : MvPolynomial (Fin 3) K,
      MvPolynomial.degreeOf (2 : Fin 3) (-p) = MvPolynomial.degreeOf (2 : Fin 3) p :=
    fun p => by simp [MvPolynomial.degreeOf_def]
  have hc1 : (MvPolynomial.C (b ^ 3 * h) : MvPolynomial (Fin 3) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 hb) hh)
  have hc2 : (MvPolynomial.C (a ^ 3 * h) : MvPolynomial (Fin 3) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 ha) hh)
  have hX1 : (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) K) ≠ 0 :=
    MvPolynomial.X_ne_zero 1
  have hX2 : ((MvPolynomial.X (2 : Fin 3)) ^ 2 : MvPolynomial (Fin 3) K) ≠ 0 :=
    pow_ne_zero 2 (MvPolynomial.X_ne_zero 2)
  have hA : MvPolynomial.degreeOf (2 : Fin 3)
      (MvPolynomial.C (b ^ 3 * h) * (MvPolynomial.X (1 : Fin 3)) :
        MvPolynomial (Fin 3) K) = 0 := by
    rw [MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 3)) hc1 hX1, MvPolynomial.degreeOf_C,
      MvPolynomial.degreeOf_X_of_ne (by decide)]
  have hB : MvPolynomial.degreeOf (2 : Fin 3)
      (MvPolynomial.C (a ^ 3 * h) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) K) = 2 := by
    rw [MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 3)) hc2 hX2, MvPolynomial.degreeOf_C,
      MvPolynomial.degreeOf_X_self_pow]
  rw [zA]
  rw [show (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X 1
        - MvPolynomial.C (a ^ 3 * h) * (MvPolynomial.X 2) ^ 2 : MvPolynomial (Fin 3) K)
      = (-(MvPolynomial.C (a ^ 3 * h) * (MvPolynomial.X 2) ^ 2))
        + (MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X 1) from by ring]
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := (2 : Fin 3))
      (p := -(MvPolynomial.C (a ^ 3 * h) * (MvPolynomial.X 2) ^ 2))
      (q := MvPolynomial.C (b ^ 3 * h) * MvPolynomial.X 1)
      (by rw [hneg, hB, hA]; norm_num)]
  rw [hneg, hB]

private lemma degreeOf_zg (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hh : h ≠ 0) :
    MvPolynomial.degreeOf (2 : Fin 3) (zg K a b h) = 5 := by
  have hneg : ∀ p : MvPolynomial (Fin 3) K,
      MvPolynomial.degreeOf (2 : Fin 3) (-p) = MvPolynomial.degreeOf (2 : Fin 3) p :=
    fun p => by simp [MvPolynomial.degreeOf_def]
  rw [zg_eq_ZElim, Work.MotK.TwCensus.ZElim]
  set T1 : MvPolynomial (Fin 3) K :=
    MvPolynomial.C (a * b ^ 7 * h ^ 2) * (MvPolynomial.X 1) ^ 5 with hT1
  set T2 : MvPolynomial (Fin 3) K :=
    MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) * (MvPolynomial.X 1) ^ 2 * MvPolynomial.X 2
    with hT2
  set T3 : MvPolynomial (Fin 3) K :=
    MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * MvPolynomial.X 1 * (MvPolynomial.X 2) ^ 3
    with hT3
  set T4 : MvPolynomial (Fin 3) K :=
    MvPolynomial.C (a ^ 6 * b ^ 2 * h) * (MvPolynomial.X 2) ^ 5 with hT4
  set T5 : MvPolynomial (Fin 3) K := MvPolynomial.C (a ^ 6 * b ^ 2) with hT5
  have hc4 : (MvPolynomial.C (a ^ 6 * b ^ 2 * h) : MvPolynomial (Fin 3) K) ≠ 0 :=
    MvPolynomial.C_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) hh)
  have hX25 : ((MvPolynomial.X (2 : Fin 3)) ^ 5 : MvPolynomial (Fin 3) K) ≠ 0 :=
    pow_ne_zero 5 (MvPolynomial.X_ne_zero 2)
  have hT4eq : MvPolynomial.degreeOf (2 : Fin 3) T4 = 5 := by
    rw [hT4, MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 3)) hc4 hX25, MvPolynomial.degreeOf_C,
      MvPolynomial.degreeOf_X_self_pow]
  have b1 : MvPolynomial.degreeOf (2 : Fin 3) T1 ≤ 3 := by
    rw [hT1]
    calc MvPolynomial.degreeOf (2 : Fin 3)
          (MvPolynomial.C (a * b ^ 7 * h ^ 2) * (MvPolynomial.X 1) ^ 5)
        ≤ MvPolynomial.degreeOf (2 : Fin 3) (MvPolynomial.C (a * b ^ 7 * h ^ 2))
            + MvPolynomial.degreeOf (2 : Fin 3) ((MvPolynomial.X 1) ^ 5) :=
          MvPolynomial.degreeOf_mul_le (2 : Fin 3) _ _
      _ = 0 := by
          rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_pow_of_ne 5 (by decide)]
      _ ≤ 3 := by norm_num
  have b2 : MvPolynomial.degreeOf (2 : Fin 3) T2 ≤ 3 := by
    rw [hT2]
    have h1 : MvPolynomial.degreeOf (2 : Fin 3)
        (MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) * (MvPolynomial.X 1) ^ 2 :
          MvPolynomial (Fin 3) K) ≤ 0 := by
      refine (MvPolynomial.degreeOf_mul_le (2 : Fin 3) _ _).trans ?_
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide)]
    have h2 : MvPolynomial.degreeOf (2 : Fin 3) (MvPolynomial.X 2 : MvPolynomial (Fin 3) K)
        ≤ 1 := by
      rw [MvPolynomial.degreeOf_X_self]
    calc MvPolynomial.degreeOf (2 : Fin 3)
          (MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) * (MvPolynomial.X 1) ^ 2
            * MvPolynomial.X 2)
        ≤ MvPolynomial.degreeOf (2 : Fin 3)
            (MvPolynomial.C (b ^ 3 * h * (3 * a ^ 5 + b ^ 5)) * (MvPolynomial.X 1) ^ 2)
          + MvPolynomial.degreeOf (2 : Fin 3) (MvPolynomial.X 2) :=
          MvPolynomial.degreeOf_mul_le (2 : Fin 3) _ _
      _ ≤ 0 + 1 := add_le_add h1 h2
      _ ≤ 3 := by norm_num
  have b3 : MvPolynomial.degreeOf (2 : Fin 3) T3 ≤ 3 := by
    rw [hT3]
    have h1 : MvPolynomial.degreeOf (2 : Fin 3)
        (MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * MvPolynomial.X 1 :
          MvPolynomial (Fin 3) K) ≤ 0 := by
      refine (MvPolynomial.degreeOf_mul_le (2 : Fin 3) _ _).trans ?_
      rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_of_ne (by decide)]
    have h2 : MvPolynomial.degreeOf (2 : Fin 3) ((MvPolynomial.X 2) ^ 3 : MvPolynomial (Fin 3) K)
        ≤ 3 := by
      rw [MvPolynomial.degreeOf_X_self_pow]
    calc MvPolynomial.degreeOf (2 : Fin 3)
          (MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * MvPolynomial.X 1
            * (MvPolynomial.X 2) ^ 3)
        ≤ MvPolynomial.degreeOf (2 : Fin 3)
            (MvPolynomial.C (a ^ 3 * h * (a ^ 5 + 2 * b ^ 5)) * MvPolynomial.X 1)
          + MvPolynomial.degreeOf (2 : Fin 3) ((MvPolynomial.X 2) ^ 3) :=
          MvPolynomial.degreeOf_mul_le (2 : Fin 3) _ _
      _ ≤ 0 + 3 := add_le_add h1 h2
      _ ≤ 3 := by norm_num
  have b5 : MvPolynomial.degreeOf (2 : Fin 3) T5 ≤ 3 := by
    rw [hT5, MvPolynomial.degreeOf_C]
    norm_num
  have hS : MvPolynomial.degreeOf (2 : Fin 3) (T1 - T2 + T3 + T5) ≤ 3 := by
    have h12 : MvPolynomial.degreeOf (2 : Fin 3) (T1 - T2) ≤ 3 := by
      rw [sub_eq_add_neg]
      refine (MvPolynomial.degreeOf_add_le (2 : Fin 3) T1 (-T2)).trans (max_le b1 ?_)
      rw [hneg T2]
      exact b2
    have h123 : MvPolynomial.degreeOf (2 : Fin 3) (T1 - T2 + T3) ≤ 3 :=
      (MvPolynomial.degreeOf_add_le (2 : Fin 3) (T1 - T2) T3).trans (max_le h12 b3)
    exact (MvPolynomial.degreeOf_add_le (2 : Fin 3) (T1 - T2 + T3) T5).trans
      (max_le h123 b5)
  rw [show T1 - T2 + T3 - T4 + T5 = (-T4) + (T1 - T2 + T3 + T5) from by ring]
  rw [MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (i := (2 : Fin 3)) (p := -T4)
    (q := T1 - T2 + T3 + T5) (by rw [hneg T4, hT4eq]; omega)]
  rw [hneg T4, hT4eq]

theorem zA_cancel_zg (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0)
    [IsDomain (Work.MotK.TGen.ZD K a b h)] (x : MvPolynomial (Fin 3) K) :
    Work.MotK.TGen.zA K a b h * x ∈ Ideal.span {Work.MotK.TGen.zg K a b h} →
      x ∈ Ideal.span {Work.MotK.TGen.zg K a b h} := by
  have hDq : IsDomain (MvPolynomial (Fin 2) K ⧸
      Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K))) :=
    ‹IsDomain (Work.MotK.TGen.ZD K a b h)›
  have hIp : (Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} :
      Set (MvPolynomial (Fin 2) K))).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime
      (Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)))).mp hDq
  have hp_ne : Work.MotK.TwCensus.ZElim2 a b h ≠ 0 := by
    intro hzero
    have hc : MvPolynomial.constantCoeff (Work.MotK.TwCensus.ZElim2 a b h) = 0 := by
      rw [hzero, map_zero]
    rw [Work.MotK.TwCensus.ZElim2] at hc
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.constantCoeff_C,
      MvPolynomial.constantCoeff_X] at hc
    exact (mul_ne_zero (pow_ne_zero 6 ha) (pow_ne_zero 2 hb)) (by simpa using hc)
  have hp : Prime (Work.MotK.TwCensus.ZElim2 a b h) := (Ideal.span_singleton_prime hp_ne).mp hIp
  have hzg_prime : Prime (zg K a b h) := by
    refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2) (p := zg K a b h)).1 ?_
    rw [show MvPolynomial.finSuccEquiv K 2 (zg K a b h)
        = Polynomial.C (Work.MotK.TwCensus.ZElim2 a b h) from
      zA_finSuccEquiv_rename_zEmb K (Work.MotK.TwCensus.ZElim2 a b h)]
    exact Polynomial.prime_C_iff.mpr hp
  have hdegzA : MvPolynomial.degreeOf (2 : Fin 3) (zA K a b h) = 2 :=
    degreeOf_zA K a b h ha hb hh
  have hdegzg : MvPolynomial.degreeOf (2 : Fin 3) (zg K a b h) = 5 :=
    degreeOf_zg K a b h ha hb hh
  have hzg_ne : zg K a b h ≠ 0 := by
    intro h0
    have h1 : MvPolynomial.degreeOf (2 : Fin 3) (zg K a b h) = 0 := by
      rw [h0, MvPolynomial.degreeOf_zero]
    rw [hdegzg] at h1
    exact (by norm_num : ¬ ((5 : ℕ) = 0)) h1
  have hndvd : ¬ (zg K a b h ∣ zA K a b h) := by
    rintro ⟨q, hq⟩
    by_cases hq0 : q = 0
    · rw [hq0, mul_zero] at hq
      have h1 : MvPolynomial.degreeOf (2 : Fin 3) (zA K a b h) = 0 := by
        rw [hq, MvPolynomial.degreeOf_zero]
      rw [hdegzA] at h1
      exact (by norm_num : ¬ ((2 : ℕ) = 0)) h1
    · have h := MvPolynomial.degreeOf_mul_eq (n := (2 : Fin 3)) hzg_ne hq0
      rw [← hq, hdegzA, hdegzg] at h
      omega
  have hI3 : (Ideal.span ({zg K a b h} : Set (MvPolynomial (Fin 3) K))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hzg_prime
  intro hx
  rcases hI3.mem_or_mem hx with h | h
  · exact absurd (Ideal.mem_span_singleton.mp h) hndvd
  · exact h

end Work.MotK.TGen
