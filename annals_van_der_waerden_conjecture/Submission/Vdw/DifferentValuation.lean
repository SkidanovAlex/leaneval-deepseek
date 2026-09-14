import Mathlib

open Function Polynomial
open scoped BigOperators NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Discriminant valuations from the different ideal (Case-I squarefullness input)

This module develops the *valuation half* of the Case-I squarefullness
statement (`fieldDisc_squarefull_of_no_transposition`, see `CaseI.lean`).
For a number field `K` with ring of integers `𝒪`, the absolute discriminant
satisfies `|discr K| = absNorm (differentIdeal ℤ 𝒪)`
(`NumberField.absNorm_differentIdeal`).  The main result proved here:

**`ramified_prime_of_padicValNat_eq_one`** (instantiated at `K_f` in
`CaseI.fieldDisc_val_one_local_structure`): if a rational prime `p` divides
the discriminant exactly once (`padicValNat p |discr K| = 1`), then the
factorisation of `p` in `𝒪` contains a unique ramified prime `P`, with
ramification index `2` and inertia degree `1`, and every other prime over
`p` is unramified.

This is the local input to the classical transposition argument: the tame
inertia group at such a `P` (in the Galois closure) acts on the
embeddings/roots as a transposition (that last step is Hilbert-theory and is
recorded separately).  The proof here only uses: `absNorm`-multiplicativity,
`differentIdeal` support (`P ∣ differentIdeal ⟺ ramified`, Mathlib
`Ideal.dvd_differentIdeal_iff`), the exponent lower bound
`P^(e−1) ∣ differentIdeal` (`Ideal.pow_sub_one_dvd_differentIdeal`), and the
prime-ideal norm formula `absNorm P = p^(inertiaDeg P)`.
-/

namespace Submission.Vdw

noncomputable section

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The prime ideals of `𝒪_K` lying over the rational prime `p`. -/
def OverPrime (p : ℕ) (P : Ideal (𝓞 K)) : Prop :=
  P.IsPrime ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))

/-- A maximal prime over `p` that divides the ideal `I`. -/
def PrimeDivisorOver (p : ℕ) (I : Ideal (𝓞 K)) (P : Ideal (𝓞 K)) : Prop :=
  P.IsMaximal ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) ∧ P ∣ I

/-- Existence of a prime divisor over `p` from `p | I.absNorm` (Mathlib). -/
theorem exists_prime_divisor_over_of_dvd_absNorm (p : ℕ) (hp : Nat.Prime p)
    (I : Ideal (𝓞 K)) (hI : p ∣ I.absNorm) :
    ∃ P : Ideal (𝓞 K), PrimeDivisorOver p I P := by
  rcases Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hI with ⟨P, hPmax, hPunder, hPdvd⟩
  refine ⟨P, hPmax, ⟨hPunder.symm⟩, hPdvd⟩

/-- The norm of a prime over `p` is a power of `p`. -/
theorem absNorm_prime_over_pow (p : ℕ) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P.absNorm = p ^ P.inertiaDeg ℤ := by
  exact (Ideal.pow_inertiaDeg p P).symm



/-- A prime of `𝒪_K` divides the different ideal iff it is ramified over `ℚ`.
(Mathlib: `Ideal.dvd_differentIdeal_iff`.) -/
theorem prime_dvd_differentIdeal_iff_ramified (P : Ideal (𝓞 K)) [P.IsPrime] :
    P ∣ differentIdeal ℤ (𝓞 K) ↔ ¬ Algebra.IsUnramifiedAt ℤ P := by
  exact dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K) (P := P)

/-- Unramified at a prime iff ramification index is one. -/
theorem ramificationIdx_eq_one_iff_unramified (P : Ideal (𝓞 K)) [P.IsPrime] :
    P.ramificationIdx ℤ = 1 ↔ Algebra.IsUnramifiedAt ℤ P := by
  exact Ideal.ramificationIdx_eq_one_iff (q := P) (R := ℤ)

/-- The ramification index is positive. -/
theorem ramificationIdx_pos_of_prime (P : Ideal (𝓞 K)) [P.IsPrime] :
    0 < P.ramificationIdx ℤ := by
  exact Ideal.ramificationIdx_pos P ℤ

/-- A ramified prime has ramification index at least two. -/
theorem ramificationIdx_two_le_of_ramified (P : Ideal (𝓞 K)) [P.IsPrime]
    (hram : ¬ Algebra.IsUnramifiedAt ℤ P) : 2 ≤ P.ramificationIdx ℤ := by
  have hpos : 0 < P.ramificationIdx ℤ := ramificationIdx_pos_of_prime P
  have hne : P.ramificationIdx ℤ ≠ 1 := by
    intro h1
    exact hram ((ramificationIdx_eq_one_iff_unramified P).mp h1)
  omega

/-- A prime dividing the different ideal has ramification index at least two. -/
theorem ramificationIdx_two_le_of_dvd_different (P : Ideal (𝓞 K)) [P.IsPrime]
    (hPδ : P ∣ differentIdeal ℤ (𝓞 K)) : 2 ≤ P.ramificationIdx ℤ := by
  apply ramificationIdx_two_le_of_ramified P
  exact (prime_dvd_differentIdeal_iff_ramified P).mp hPδ

/-- Inertia degree is positive. -/
theorem inertiaDeg_pos_of_prime (p : ℕ) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : 0 < P.inertiaDeg ℤ := by
  exact Ideal.inertiaDeg_pos P ℤ



/-- The ideal `(p)` of `ℤ` is maximal for a prime `p`. -/
theorem span_prime_isMaximal (p : ℕ) (hp : Nat.Prime p) :
    (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ).IsMaximal := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  exact ((Ideal.span_singleton_prime (p := (p : ℤ)) hp0).mpr (Nat.prime_iff_prime_int.mp hp)).isMaximal
    (by simpa using hp0)

/-- The principal ideal `(p)` of `ℤ` is nonzero for a prime `p`. -/
theorem span_prime_ne_bot (p : ℕ) (hp : Nat.Prime p) :
    (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) ≠ ⊥ := by
  intro hs
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Nat.Prime.ne_zero hp)
  exact hp0 (Ideal.span_singleton_eq_bot.mp hs)

/-- For a prime `P` of `𝒪_K` over `p`, the ramification index `e` satisfies
`P^e | p·𝒪_K`. -/
theorem pow_ramificationIdx_dvd_map (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P ^ P.ramificationIdx ℤ ∣ (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K)) := by
  classical
  let J : Ideal (𝓞 K) := (Ideal.span ({(p : ℤ)} : Set ℤ)).map (algebraMap ℤ (𝓞 K))
  have hJne : J ≠ ⊥ := by
    dsimp [J]
    exact (Ideal.map_eq_bot_iff_of_injective (f := algebraMap ℤ (𝓞 K))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))).not.mpr (span_prime_ne_bot p hp)
  have hcount : P.ramificationIdx ℤ =
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors J) := by
    exact Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (R := ℤ) (S := 𝓞 K) (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (q := P) hJne
  obtain ⟨Q, _hQsup, hJeq⟩ := Ideal.eq_prime_pow_mul_coprime hJne P
  refine ⟨Q, ?_⟩
  change J = P ^ P.ramificationIdx ℤ * Q
  rw [hJeq]
  rw [← hcount]

/-- Lower bound on the different-ideal valuation: for a prime `P` of `𝒪_K`
over `p`, the different ideal is divisible by `P^(e−1)` where
`e = ramificationIdx`. -/
theorem pow_sub_one_dvd_differentIdeal_of_over (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    P ^ (P.ramificationIdx ℤ - 1) ∣ differentIdeal ℤ (𝓞 K) := by
  letI : (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ).IsMaximal := span_prime_isMaximal p hp
  exact pow_sub_one_dvd_differentIdeal (A := ℤ) (B := 𝓞 K) P (P.ramificationIdx ℤ)
    (span_prime_ne_bot p hp) (pow_ramificationIdx_dvd_map p hp P)

/-- Norm of a power of a prime over `p`: `absNorm (P^k) = p^(f·k)`. -/
theorem absNorm_prime_over_pow_mul (p : ℕ) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (k : ℕ) :
    (P ^ k).absNorm = p ^ (P.inertiaDeg ℤ * k) := by
  calc
    (P ^ k).absNorm = (P.absNorm) ^ k := by simp
    _ = (p ^ P.inertiaDeg ℤ) ^ k := by rw [absNorm_prime_over_pow p P]
    _ = p ^ (P.inertiaDeg ℤ * k) := by rw [pow_mul]



/-- From `padicValNat p N = 1` and `p^k | N` deduce `k ≤ 1` (i.e. the
divisibility `p^k | N` accounts for the whole power of `p` in `N`). -/
theorem pow_dvd_le_one_of_padicValNat_eq_one (p k N : ℕ) (hp : Nat.Prime p)
    (hN : N ≠ 0) (hv : padicValNat p N = 1) (hdiv : p ^ k ∣ N) : k ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hle : k ≤ padicValNat p N := (padicValNat_dvd_iff_le (p := p) (n := k) (a := N) hN).mp hdiv
  omega

/-- The `p`-adic valuation of the norm of the different ideal equals one iff
`p` divides the absolute discriminant exactly once. -/
theorem padicValNat_differentIdeal_discr (K : Type*) [Field K] [NumberField K]
    (p : ℕ) : padicValNat p ((differentIdeal ℤ (𝓞 K)).absNorm) = padicValNat p (NumberField.discr K).natAbs := by
  rw [NumberField.absNorm_differentIdeal K (𝒪 := 𝓞 K)]

/-- A prime over `p` dividing the different ideal has, when the discriminant
valuation is one, inertia degree one and ramification index two. -/
theorem e_and_f_of_prime_dvd_different {p : ℕ} (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hPδ : P ∣ differentIdeal ℤ (𝓞 K))
    (hv : padicValNat p ((differentIdeal ℤ (𝓞 K)).absNorm) = 1) :
    P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 2 := by
  classical
  let δ : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K)
  have hδne : δ.absNorm ≠ 0 := by
    -- discr K ≠ 0 for a number field; absNorm δ = |discr K|
    rw [NumberField.absNorm_differentIdeal K (𝒪 := 𝓞 K)]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  -- exponent bound: p^(f·(e−1)) | δ.absNorm
  have hPdiff : P ^ (P.ramificationIdx ℤ - 1) ∣ δ :=
    pow_sub_one_dvd_differentIdeal_of_over p hp P
  have hnorm : (P ^ (P.ramificationIdx ℤ - 1)).absNorm ∣ δ.absNorm := by
    exact map_dvd Ideal.absNorm hPdiff
  have hpowNorm : (P ^ (P.ramificationIdx ℤ - 1)).absNorm =
      p ^ (P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) :=
    absNorm_prime_over_pow_mul p P (P.ramificationIdx ℤ - 1)
  have hmain : P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1) ≤ 1 := by
    apply pow_dvd_le_one_of_padicValNat_eq_one p _ _ hp hδne hv
    rwa [hpowNorm] at hnorm
  have hfpos : 0 < P.inertiaDeg ℤ := inertiaDeg_pos_of_prime p P
  have hram : ¬ Algebra.IsUnramifiedAt ℤ P := (prime_dvd_differentIdeal_iff_ramified P).mp hPδ
  have he2 : 2 ≤ P.ramificationIdx ℤ := ramificationIdx_two_le_of_ramified P hram
  have hprod : (P.ramificationIdx ℤ - 1) * P.inertiaDeg ℤ ≤ 1 := by
    simpa [mul_comm] using hmain
  constructor
  · -- f = 1
    have hle : P.inertiaDeg ℤ ≤ P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1) := by
      exact Nat.le_mul_of_pos_right (P.inertiaDeg ℤ) (by omega)
    omega
  · -- e = 2
    have hle2 : P.ramificationIdx ℤ - 1 ≤ (P.ramificationIdx ℤ - 1) * P.inertiaDeg ℤ := by
      exact Nat.le_mul_of_pos_right (P.ramificationIdx ℤ - 1) hfpos
    omega



/-- At most one maximal prime of `𝒪_K` over `p` divides the different ideal,
when the `p`-adic valuation of its norm (= `|discr K|`) is one. -/
theorem atMostOne_max_prime_dvd_different_of_val_one (p : ℕ) (hp : Nat.Prime p)
    (hv : padicValNat p ((differentIdeal ℤ (𝓞 K)).absNorm) = 1)
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (Q : Ideal (𝓞 K)) [Q.IsMaximal] [Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hPdvd : P ∣ differentIdeal ℤ (𝓞 K)) (hQdvd : Q ∣ differentIdeal ℤ (𝓞 K)) : P = Q := by
  classical
  let δ : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K)
  by_contra hne
  have hsup : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne ‹P.IsMaximal› ‹Q.IsMaximal› hne
  have hinf : P * Q = P ⊓ Q := Ideal.mul_eq_inf_of_coprime hsup
  -- δ ≤ P and δ ≤ Q, hence δ ≤ P ⊓ Q = P·Q, i.e. P·Q | δ
  have hδP : δ ≤ P := (Ideal.dvd_iff_le).mp hPdvd
  have hδQ : δ ≤ Q := (Ideal.dvd_iff_le).mp hQdvd
  have hδPQ : δ ≤ P * Q := by
    rw [hinf]
    exact le_inf hδP hδQ
  have hdiv : P * Q ∣ δ := (Ideal.dvd_iff_le).mpr hδPQ
  have hnorm : (P * Q).absNorm ∣ δ.absNorm := map_dvd Ideal.absNorm hdiv
  have hprod : (P * Q).absNorm = p ^ (P.inertiaDeg ℤ + Q.inertiaDeg ℤ) := by
    calc
      (P * Q).absNorm = P.absNorm * Q.absNorm := by rw [map_mul]
      _ = (p ^ P.inertiaDeg ℤ) * (p ^ Q.inertiaDeg ℤ) := by
        rw [absNorm_prime_over_pow p P, absNorm_prime_over_pow p Q]
      _ = p ^ (P.inertiaDeg ℤ + Q.inertiaDeg ℤ) := by rw [pow_add]
  have hδne : δ.absNorm ≠ 0 := by
    rw [NumberField.absNorm_differentIdeal K (𝒪 := 𝓞 K)]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hsum_le : P.inertiaDeg ℤ + Q.inertiaDeg ℤ ≤ 1 := by
    apply pow_dvd_le_one_of_padicValNat_eq_one p (P.inertiaDeg ℤ + Q.inertiaDeg ℤ) _ hp hδne hv
    rwa [hprod] at hnorm
  have hposP : 0 < P.inertiaDeg ℤ := inertiaDeg_pos_of_prime p P
  have hposQ : 0 < Q.inertiaDeg ℤ := inertiaDeg_pos_of_prime p Q
  omega

/-- The main local valuation statement behind Case-I squarefullness: if the
`p`-adic valuation of the absolute discriminant of the number field `K` is
one, then `p` has exactly one ramified prime `P` over it, with
`ramificationIdx = 2` and `inertiaDeg = 1`, and every other prime over `p`
is unramified (`ramificationIdx = 1`). -/
theorem ramified_prime_of_padicValNat_eq_one (p : ℕ) (hp : Nat.Prime p)
    (hv : padicValNat p ((differentIdeal ℤ (𝓞 K)).absNorm) = 1) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) ∧
      P.ramificationIdx ℤ = 2 ∧ P.inertiaDeg ℤ = 1 ∧
      ∀ Q : Ideal (𝓞 K), Q.IsMaximal → Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) →
        Q ≠ P → Q.ramificationIdx ℤ = 1 := by
  classical
  let δ : Ideal (𝓞 K) := differentIdeal ℤ (𝓞 K)
  have hδne : δ.absNorm ≠ 0 := by
    rw [NumberField.absNorm_differentIdeal K (𝒪 := 𝓞 K)]
    exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  have hdiv : p ∣ δ.absNorm := by
    apply dvd_of_one_le_padicValNat
    rw [show padicValNat p δ.absNorm = 1 by simpa [δ] using hv]
  obtain ⟨P, hPmax, hPover, hPdvd⟩ := exists_prime_divisor_over_of_dvd_absNorm p hp δ hdiv
  refine ⟨P, hPmax, hPover, ?_, ?_, ?_⟩
  · -- e = 2, f = 1
    haveI : P.IsMaximal := hPmax
    haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPover
    exact (e_and_f_of_prime_dvd_different hp P hPdvd hv).2
  · haveI : P.IsMaximal := hPmax
    haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPover
    exact (e_and_f_of_prime_dvd_different hp P hPdvd hv).1
  · -- every other maximal prime Q over p is unramified
    intro Q hQmax hQover hQne
    have hQndvd : ¬ Q ∣ δ := by
      intro hQdvd
      haveI : P.IsMaximal := hPmax
      haveI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPover
      haveI : Q.IsMaximal := hQmax
      haveI : Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hQover
      exact hQne ((atMostOne_max_prime_dvd_different_of_val_one p hp hv P Q hPdvd hQdvd).symm)
    have hunram : Algebra.IsUnramifiedAt ℤ Q := by
      haveI : Q.IsPrime := hQmax.isPrime
      exact (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 K) (P := Q)).mp hQndvd
    haveI : Q.IsPrime := hQmax.isPrime
    exact (ramificationIdx_eq_one_iff_unramified Q).mpr hunram

end


/-- `p | N` exactly once (`p² ∤ N`) iff the `p`-adic valuation of `N` is one. -/
theorem padicValNat_eq_one_iff_dvd_not_sq_dvd {p N : ℕ} (hp : Nat.Prime p) (hN : N ≠ 0) :
    padicValNat p N = 1 ↔ p ∣ N ∧ ¬ p ^ 2 ∣ N := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hv
    constructor
    · apply dvd_of_one_le_padicValNat
      omega
    · intro hsq
      have h2 : 2 ≤ padicValNat p N := (padicValNat_dvd_iff_le (p := p) (n := 2) (a := N) hN).mp hsq
      omega
  · intro h
    have h1 : 1 ≤ padicValNat p N := by
      have hpow : p ^ 1 ∣ N := by simpa using h.1
      exact (padicValNat_dvd_iff_le (p := p) (n := 1) (a := N) hN).mp hpow
    have hle : padicValNat p N ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ padicValNat p N := by omega
      exact h.2 ((padicValNat_dvd_iff_le (p := p) (n := 2) (a := N) hN).mpr h2)
    omega

/-- If `p | N` and `p² ∤ N` then the `p`-adic valuation of `N` is exactly one
(the contrapositive form used by the squarefullness argument). -/
theorem padicValNat_eq_one_of_dvd_not_sq_dvd {p N : ℕ} (hp : Nat.Prime p) (hN : N ≠ 0)
    (hdvd : p ∣ N) (hnot : ¬ p ^ 2 ∣ N) : padicValNat p N = 1 := by
  exact (padicValNat_eq_one_iff_dvd_not_sq_dvd hp hN).mpr ⟨hdvd, hnot⟩

end Submission.Vdw
