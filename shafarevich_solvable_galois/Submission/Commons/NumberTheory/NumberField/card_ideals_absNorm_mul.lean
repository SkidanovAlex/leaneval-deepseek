import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_one_lower_bound_quadratic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

open Commons.NumberTheory.DirichletCharacter

section Main

variable {K : Type*} [Field K] [NumberField K]

/-- For a number field `K`, if `I` is an ideal of norm `m * n` with `m`, `n` coprime and
nonzero, then the "`m`-part" `I + (m)` has norm `m`. -/
theorem absNorm_sup_span_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : m.Coprime n) {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) = m := by
  have hmn : (m : 𝓞 K) * (n : 𝓞 K) ∈ I := mul_mem_of_absNorm_eq (K := K) hI
  have hprod := sup_mul_sup_eq_self (K := K) hcop hmn
  set A : ℕ := Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) with hA
  set B : ℕ := Ideal.absNorm (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) with hB
  have hAB : A * B = m * n := by
    rw [hA, hB]
    have h : Ideal.absNorm ((I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) *
        (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)))) = m * n := by rw [hprod, hI]
    rwa [map_mul] at h
  have hAm : A ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    have h : Ideal.absNorm (I ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) ∣
        Ideal.absNorm (Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    rw [Ideal.absNorm_span_natCast] at h
    rw [hA]; exact h
  have hAcop : A.Coprime n :=
    Nat.Coprime.coprime_dvd_left hAm (hcop.pow_left _)
  have hA_m : A ∣ m := hAcop.dvd_of_dvd_mul_right ⟨B, hAB.symm⟩
  have hBn : B ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    have h : Ideal.absNorm (I ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) ∣
        Ideal.absNorm (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le le_sup_right
    rw [Ideal.absNorm_span_natCast] at h
    rw [hB]; exact h
  have hBcop : B.Coprime m :=
    Nat.Coprime.coprime_dvd_left hBn (hcop.symm.pow_left _)
  have hB_n : B ∣ n :=
    hBcop.dvd_of_dvd_mul_right ⟨A, by rw [mul_comm n m, hAB.symm]; ring⟩
  obtain ⟨t, ht⟩ := hA_m
  obtain ⟨u, hu⟩ := hB_n
  have hA0 : A ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hAB
    exact (mul_ne_zero hm hn) hAB.symm
  have hB0 : B ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hAB
    exact (mul_ne_zero hm hn) hAB.symm
  have htu : t * u = 1 := by
    have h3 : A * B = A * B * (t * u) := by
      calc A * B = m * n := hAB
        _ = A * t * (B * u) := by rw [← ht, ← hu]
        _ = A * B * (t * u) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mul_ne_zero hA0 hB0))
      (by simpa using h3.symm)
  have ht1 : t = 1 := Nat.dvd_one.mp ⟨u, htu.symm⟩
  have hm' : m = A := by rw [ht, ht1, mul_one]
  exact hm'.symm

/-- If `J` has norm `m`, `K` has norm `n` with `m`, `n` coprime, then the `m`-part of the
product `J * K` is `J`. -/
lemma mul_sup_span_eq_left {m n : ℕ} (hcop : m.Coprime n) {J K' : Ideal (𝓞 K)}
    (hJ : Ideal.absNorm J = m) (hK : Ideal.absNorm K' = n) :
    J * K' ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) = J := by
  have hJle : Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ≤ J := by
    rw [← hJ]; exact Ideal.span_singleton_absNorm_le J
  have hKle : Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) ≤ K' := by
    rw [← hK]; exact Ideal.span_singleton_absNorm_le K'
  have hKm : K' ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) = ⊤ :=
    top_le_iff.mp (by
      calc ⊤ = Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) ⊔
            Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) :=
            (sup_span_eq_top_of_coprime (K := K) hcop).symm
        _ ≤ K' ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) :=
            sup_le le_sup_right (le_trans hKle le_sup_left))
  have hsplit : J = J * K' ⊔ J * Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) := by
    rw [← Ideal.mul_sup, hKm, Ideal.mul_top]
  refine le_antisymm (sup_le Ideal.mul_le_left hJle) ?_
  calc J = J * K' ⊔ J * Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) := hsplit
    _ ≤ J * K' ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) :=
        sup_le_sup le_rfl Ideal.mul_le_right

/-- There is exactly one ideal of absolute norm `0`, namely `⊥`. -/
lemma card_absNorm_eq_zero : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} = 1 := by
  haveI : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_bot⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp I.2) }
  exact Nat.card_unique

/-- There is exactly one ideal of absolute norm `1`, namely `⊤`. -/
lemma card_absNorm_eq_one : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
  haveI : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} :=
    { default := ⟨⊤, Ideal.absNorm_top⟩
      uniq := fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2) }
  exact Nat.card_unique

/-- The number of ideals of absolute norm `m * n` equals the product of the numbers of
ideals of absolute norm `m` and of absolute norm `n`, for coprime `m` and `n`. -/
theorem card_ideals_absNorm_mul {K : Type*} [Field K] [NumberField K] {m n : ℕ}
    (hmn : m.Coprime n) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m * n} =
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m} *
        Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} := by
  by_cases hm0 : m = 0
  · rw [hm0] at hmn ⊢
    have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hmn
    subst hn1
    rw [zero_mul, card_absNorm_eq_one, mul_one]
  by_cases hn0 : n = 0
  · rw [hn0] at hmn ⊢
    have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
    subst hm1
    rw [mul_zero, card_absNorm_eq_one, one_mul]
  · have hm : m ≠ 0 := hm0
    have hn : n ≠ 0 := hn0
    -- Instances of finiteness for `Nat.card_le_card_of_injective`.
    haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (m * n)).fintype
    haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) m).fintype
    haveI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).fintype
    -- (1) `prod ≤ LHS`, via injectivity of `(J,K) ↦ J * K`.
    let Ψ : {J : Ideal (𝓞 K) // Ideal.absNorm J = m} ×
          {L : Ideal (𝓞 K) // Ideal.absNorm L = n} →
        {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} :=
      fun p => ⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩
    have hΨinj : Function.Injective Ψ := by
      intro p q hpq
      have hval : p.1.1 * p.2.1 = q.1.1 * q.2.1 := congrArg Subtype.val hpq
      have hJp : p.1.1 * p.2.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) = p.1.1 :=
        mul_sup_span_eq_left hmn p.1.2 p.2.2
      have hJq : q.1.1 * q.2.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) = q.1.1 :=
        mul_sup_span_eq_left hmn q.1.2 q.2.2
      have hKp : p.1.1 * p.2.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) = p.2.1 := by
        rw [mul_comm]; exact mul_sup_span_eq_left hmn.symm p.2.2 p.1.2
      have hKq : q.1.1 * q.2.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) = q.2.1 := by
        rw [mul_comm]; exact mul_sup_span_eq_left hmn.symm q.2.2 q.1.2
      have h1 : p.1.1 = q.1.1 := by rw [← hJp, hval, hJq]
      have h2 : p.2.1 = q.2.1 := by rw [← hKp, hval, hKq]
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    have hΨ := Nat.card_le_card_of_injective Ψ hΨinj
    rw [Nat.card_prod] at hΨ
    -- (2) `LHS ≤ prod`, via injectivity of `I ↦ (I + (m), I + (n))`.
    let Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m * n} →
        {J : Ideal (𝓞 K) // Ideal.absNorm J = m} ×
          {L : Ideal (𝓞 K) // Ideal.absNorm L = n} :=
      fun I => (⟨I.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)),
          absNorm_sup_span_of_coprime hm hn hmn I.2⟩,
        ⟨I.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)),
          absNorm_sup_span_of_coprime hn hm hmn.symm (by rw [I.2, mul_comm])⟩)
    have hΦinj : Function.Injective Φ := by
      intro I I' h
      have h1 : I.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) =
          I'.1 ⊔ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) := by
        simpa using congrArg (fun t => (t.1 : Ideal (𝓞 K))) h
      have h2 : I.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) =
          I'.1 ⊔ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
        simpa using congrArg (fun t => (t.2 : Ideal (𝓞 K))) h
      refine Subtype.ext ?_
      rw [eq_inf_sup_span hmn I.2, eq_inf_sup_span hmn I'.2, h1, h2]
    have hΦ := Nat.card_le_card_of_injective Φ hΦinj
    rw [Nat.card_prod] at hΦ
    exact le_antisymm hΦ hΨ

end Main

end Commons.NumberTheory.NumberField
