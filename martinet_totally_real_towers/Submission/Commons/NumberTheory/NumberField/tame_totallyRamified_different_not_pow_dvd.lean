import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.RingTheory.RamificationInertia.Basic

open scoped NumberField BigOperators Polynomial
open UniqueFactorizationMonoid

noncomputable section

namespace Commons.NumberTheory.NumberField

set_option autoImplicit false
set_option maxHeartbeats 1200000

universe u

variable {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K] [Algebra E K]

/-- The finrank of 𝒪_K over 𝒪_E equals the field degree [K : E]. -/
lemma finrank_ringOfIntegers_eq_finrank :
    Module.finrank (𝓞 E) (𝓞 K) = Module.finrank E K := by
  symm
  exact IsFractionRing.finrank_eq (A := 𝓞 E) (K := E) (B := 𝓞 K) (L := K)

/-- For a prime ideal P₀ of 𝒪_E, the primes of 𝒪_K over P₀ form a finite type. -/
noncomputable instance fintype_primesOver (P₀ : Ideal (𝓞 E)) [P₀.IsPrime] :
    Fintype (P₀.primesOver (𝓞 K)) := by
  classical
  exact (Algebra.QuasiFinite.finite_primesOver (R := 𝓞 E) (S := 𝓞 K) P₀).fintype

/-- Fundamental identity: sum of e·f over the primes over P₀ equals the field degree. -/
lemma sum_ramification_inertia_eq_finrank_E (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] :
    ∑ q : P₀.primesOver (𝓞 K), q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E) =
      Module.finrank E K := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  rw [← finrank_ringOfIntegers_eq_finrank (E := E) (K := K)]
  exact Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 E) (p := P₀) (S := 𝓞 K)

/-- Total ramification (`finrank = ramification index`) forces `P` to be the unique prime
over `P₀`, with inertia degree one. -/
lemma unique_prime_over_of_totallyRamified (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E)) :
    (∀ Q : Ideal (𝓞 K), Q ∈ P₀.primesOver (𝓞 K) → Q = P) ∧
      P.inertiaDeg (𝓞 E) = 1 := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  letI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let x : P₀.primesOver (𝓞 K) := ⟨P, ⟨‹P.IsPrime›, ‹P.LiesOver P₀›⟩⟩
  let t : P₀.primesOver (𝓞 K) → ℕ := fun q => q.1.ramificationIdx (𝓞 E) * q.1.inertiaDeg (𝓞 E)
  have hsum : (∑ q : P₀.primesOver (𝓞 K), t q) = P.ramificationIdx (𝓞 E) := by
    rw [sum_ramification_inertia_eq_finrank_E (E := E) (K := K) P₀, he]
  have hx_term : t x = P.ramificationIdx (𝓞 E) * P.inertiaDeg (𝓞 E) := rfl
  have hpos_e : 0 < P.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos P (𝓞 E)
  have hpos_f : 0 < P.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos P (𝓞 E)
  have hx_le : t x ≤ ∑ q : P₀.primesOver (𝓞 K), t q := by
    simpa using (Finset.single_le_sum (s := (Finset.univ : Finset (P₀.primesOver (𝓞 K))))
      (f := t) (by intro q hq; exact Nat.zero_le _) (Finset.mem_univ x))
  have hx_ge : P.ramificationIdx (𝓞 E) ≤ t x := by
    rw [hx_term]
    exact Nat.le_mul_of_pos_right _ hpos_f
  have hx_eq : t x = P.ramificationIdx (𝓞 E) :=
    le_antisymm (by simpa [hsum] using hx_le) hx_ge
  have hf : P.inertiaDeg (𝓞 E) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos_e
    calc
      P.ramificationIdx (𝓞 E) * P.inertiaDeg (𝓞 E) = t x := hx_term.symm
      _ = P.ramificationIdx (𝓞 E) := hx_eq
      _ = P.ramificationIdx (𝓞 E) * 1 := by rw [mul_one]
  constructor
  · intro Q hQ
    by_contra hQne
    haveI : Q.IsPrime := hQ.1
    let y : P₀.primesOver (𝓞 K) := ⟨Q, hQ⟩
    have hyx : y ≠ x := by
      intro hyx
      exact hQne (congrArg Subtype.val hyx)
    have hy_pos : 0 < t y := by
      have h1 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos Q (𝓞 E)
      have h2 : 0 < Q.inertiaDeg (𝓞 E) := Ideal.inertiaDeg_pos Q (𝓞 E)
      simpa [t] using Nat.mul_pos h1 h2
    have hxmem : x ∈ (Finset.univ.erase y : Finset (P₀.primesOver (𝓞 K))) := by
      simp [Finset.mem_erase, hyx.symm]
    have hrest : t x ≤ ∑ q ∈ (Finset.univ.erase y : Finset (P₀.primesOver (𝓞 K))), t q := by
      exact Finset.single_le_sum (s := (Finset.univ.erase y : Finset (P₀.primesOver (𝓞 K))))
        (f := t) (by intro q hq; exact Nat.zero_le _) hxmem
    have hpair : t x + t y ≤ ∑ q : P₀.primesOver (𝓞 K), t q := by
      have hsplit : (∑ q ∈ (Finset.univ.erase y : Finset (P₀.primesOver (𝓞 K))), t q) + t y =
          ∑ q : P₀.primesOver (𝓞 K), t q := by
        simpa using (Finset.sum_erase_add (s := (Finset.univ : Finset (P₀.primesOver (𝓞 K))))
          (f := t) (a := y) (Finset.mem_univ y))
      calc
        t x + t y ≤ (∑ q ∈ (Finset.univ.erase y : Finset (P₀.primesOver (𝓞 K))), t q) + t y := by
          exact add_le_add hrest (le_refl (t y))
        _ = ∑ q : P₀.primesOver (𝓞 K), t q := hsplit
    have hty_le0 : t y ≤ 0 := by
      have hsum' : (∑ q : P₀.primesOver (𝓞 K), t q) = t x := by simpa [hx_eq] using hsum
      have : t x + t y ≤ t x := by simpa [hsum'] using hpair
      omega
    omega
  · exact hf


/-- The extension of `P₀` in `𝒪_K` is exactly `P ^ e`, where `e` is the ramification index,
whenever `P` is the only prime over `P₀`. -/
lemma map_P₀_eq_pow_of_unique (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hP₀ : P₀ ≠ ⊥)
    (huniq : ∀ Q : Ideal (𝓞 K), Q ∈ P₀.primesOver (𝓞 K) → Q = P) :
    Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E) := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  have hdec := Ideal.map_algebraMap_eq_finsetProd_pow (S := 𝓞 E) (R := 𝓞 K) (p := P₀) hP₀
  have hset : P₀.primesOver (𝓞 K) = {P} := by
    ext Q
    constructor
    · intro hQ
      exact Set.mem_singleton_iff.mpr (huniq Q hQ)
    · intro hQ
      have hQP : Q = P := Set.mem_singleton_iff.mp hQ
      subst Q
      exact ⟨‹P.IsPrime›, ‹P.LiesOver P₀›⟩
  rw [hdec]
  simpa [hset]


/-! ## The P-adic order of an element (count of P in the principal ideal) -/

section Order

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- The multiplicity of a prime ideal `P` in the principal ideal generated by `x`. -/
noncomputable def orderCount (P : Ideal R) [P.IsPrime] (x : R) : ℕ :=
  (normalizedFactors (Ideal.span {x} : Ideal R)).count P

/-- Membership in `P ^ k` gives a lower bound on the order. -/
lemma orderCount_ge_of_mem_pow (P : Ideal R) [P.IsPrime] {x : R} (hx : x ≠ 0) (k : ℕ)
    (h : x ∈ P ^ k) : k ≤ orderCount P x := by
  classical
  by_cases hP0 : P = ⊥
  · subst P
    cases k with
    | zero => simp [orderCount]
    | succ k =>
      exfalso
      exact hx (Ideal.mem_bot.mp (by simpa using h))
  · have hp : Prime P := Ideal.prime_of_isPrime hP0 ‹P.IsPrime›
    have hPk_ne : P ^ k ≠ 0 := pow_ne_zero k hP0
    have hspan_ne : Ideal.span {x} ≠ 0 := by simpa [Ideal.span_singleton_eq_bot] using hx
    have hdvd : P ^ k ∣ Ideal.span {x} := by
      exact (Ideal.dvd_iff_le).mpr ((Ideal.span_singleton_le_iff_mem (P ^ k)).symm.mp h)
    have hle : normalizedFactors (P ^ k) ≤ normalizedFactors (Ideal.span {x}) :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hPk_ne hspan_ne).mp hdvd
    have hcount : (normalizedFactors (P ^ k)).count P ≤
        (normalizedFactors (Ideal.span {x})).count P :=
      Multiset.count_le_of_le P hle
    rw [Irreducible.normalizedFactors_pow hp.irreducible, Multiset.count_replicate] at hcount
    simpa [orderCount, normalize_eq P] using hcount

/-- Non-membership of `P ^ k` follows from a strict upper bound on the order. -/
lemma not_mem_pow_of_order_lt (P : Ideal R) [P.IsPrime] {x : R} (hx : x ≠ 0) {k : ℕ}
    (h : orderCount P x < k) : x ∉ P ^ k := by
  intro hk
  exact (not_lt_of_ge (orderCount_ge_of_mem_pow (P := P) hx k hk)) h

/-- The order of the exact power: membership of `P ^ k` but not `P ^ (k+1)`. -/
lemma orderCount_eq_of_mem_pow_not_mem_pow_succ (P : Ideal R) [P.IsPrime]
    {x : R} {k : ℕ} (hx : x ∈ P ^ k) (hx' : x ∉ P ^ (k + 1)) :
    orderCount P x = k := by
  classical
  exact Ideal.count_normalizedFactors_eq (p := P) (x := Ideal.span {x})
    (by simpa [Ideal.span_singleton_le_iff_mem] using hx)
    (by simpa [Ideal.span_singleton_le_iff_mem] using hx')

/-- The order of a product is the sum of the orders. -/
lemma orderCount_mul (P : Ideal R) [P.IsPrime] {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    orderCount P (x * y) = orderCount P x + orderCount P y := by
  classical
  unfold orderCount
  rw [← Ideal.span_singleton_mul_span_singleton x y]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul]
  · rw [Multiset.count_add]
  · exact (Ideal.span_singleton_eq_bot.not.mpr hx)
  · exact (Ideal.span_singleton_eq_bot.not.mpr hy)

/-- The order of a power. -/
lemma orderCount_pow (P : Ideal R) [P.IsPrime] {x : R} (hx : x ≠ 0) (n : ℕ) :
    orderCount P (x ^ n) = n * orderCount P x := by
  classical
  induction n with
  | zero =>
      rw [pow_zero]
      unfold orderCount
      rw [Ideal.span_singleton_one, ← Ideal.one_eq_top,
        UniqueFactorizationMonoid.normalizedFactors_one]
      simp
  | succ n ih =>
      rw [pow_succ, orderCount_mul (P := P) (pow_ne_zero _ hx) hx, ih,
        Nat.succ_mul, Nat.add_comm]

/-- Multiplying by an element of zero order preserves the exact power classes. -/
lemma mul_of_order_eq_zero (P : Ideal R) [P.IsPrime] {c x : R} (hc : c ≠ 0)
    (hord : orderCount P c = 0) {k : ℕ} (hx : x ∈ P ^ k) (hx' : x ∉ P ^ (k + 1)) :
    c * x ∈ P ^ k ∧ c * x ∉ P ^ (k + 1) := by
  classical
  have hcx : c * x ≠ 0 := mul_ne_zero hc (by
    intro hx0
    exact hx' (by simpa [hx0] using (Ideal.zero_mem (P ^ (k + 1)))))
  constructor
  · exact Ideal.mul_mem_left (P ^ k) c hx
  · intro hmem
    have h1 : k + 1 ≤ orderCount P (c * x) := orderCount_ge_of_mem_pow (P := P) hcx (k+1) hmem
    have h2 : orderCount P (c * x) = orderCount P c + orderCount P x :=
      orderCount_mul (P := P) hc (by intro hx0; exact hx' (by simp [hx0]))
    have h3 : orderCount P x = k := orderCount_eq_of_mem_pow_not_mem_pow_succ (P := P) hx hx'
    omega


/-- The multiplicity of a prime ideal `P` in a nonzero ideal `I`. -/
noncomputable def idealCount (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ :=
  (normalizedFactors I).count P

/-- A lower bound on the order gives membership in the prime power. -/
lemma mem_pow_of_orderCount_ge (P : Ideal R) [P.IsPrime] {x : R} (hx : x ≠ 0) {k : ℕ}
    (h : k ≤ orderCount P x) : x ∈ P ^ k := by
  classical
  by_cases hP0 : P = ⊥
  · subst P
    cases k with
    | zero => simp
    | succ k =>
        exfalso
        have hz : Multiset.count (⊥ : Ideal R) (normalizedFactors (Ideal.span {x})) = 0 := by
          apply Multiset.count_eq_zero.mpr
          intro hmem
          have hprim : Prime (⊥ : Ideal R) := prime_of_normalized_factor _ hmem
          exact hprim.ne_zero rfl
        simp [orderCount] at h
        omega
  · have hp : Prime P := Ideal.prime_of_isPrime hP0 ‹P.IsPrime›
    have hspan_ne : Ideal.span {x} ≠ 0 := by simpa [Ideal.span_singleton_eq_bot] using hx
    -- nf(P^k) ≤ nf(span{x})
    have hle : normalizedFactors (P ^ k) ≤ normalizedFactors (Ideal.span {x}) := by
      rw [Irreducible.normalizedFactors_pow hp.irreducible]
      rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a = P
      · subst a
        simp [Multiset.count_replicate, normalize_eq P, orderCount]
        exact h
      · simp [Multiset.count_replicate, normalize_eq P, ha, Ne.symm ha]
    have hdvd : P ^ k ∣ Ideal.span {x} :=
      (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
        (pow_ne_zero k hP0) hspan_ne).mpr hle
    exact (Ideal.span_singleton_le_iff_mem (P ^ k)).mp ((Ideal.dvd_iff_le).mp hdvd)

/-- The ideal count of a product is the sum of the counts. -/
lemma idealCount_mul (P : Ideal R) [P.IsPrime] {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealCount P (I * J) = idealCount P I + idealCount P J := by
  classical
  unfold idealCount
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.count_add]

/-- If `P` does not divide `I`, then the ideal count of `P` in `I` is zero. -/
lemma idealCount_eq_zero_of_not_dvd (P : Ideal R) [P.IsPrime] {I : Ideal R} (h : ¬ P ∣ I) :
    idealCount P I = 0 := by
  classical
  unfold idealCount
  refine Multiset.count_eq_zero_of_notMem ?_
  intro hmem
  exact h (dvd_of_mem_normalizedFactors hmem)

/-- The ideal count of `P` in `P ^ k` equals `k`. -/
lemma idealCount_prime_pow (P : Ideal R) [P.IsPrime] (hP0 : P ≠ 0) (k : ℕ) :
    idealCount P (P ^ k) = k := by
  classical
  have hp : Prime P := Ideal.prime_of_isPrime hP0 ‹P.IsPrime›
  unfold idealCount
  rw [Irreducible.normalizedFactors_pow hp.irreducible, Multiset.count_replicate]
  simp [normalize_eq P]

/-- Membership in a prime power forces the count to be at least the exponent. -/
lemma idealCount_ge_of_mem_pow (P : Ideal R) [P.IsPrime] {x : R} (hx : x ≠ 0) (k : ℕ)
    (h : x ∈ P ^ k) : k ≤ idealCount P (Ideal.span {x}) := by
  classical
  exact orderCount_ge_of_mem_pow (P := P) hx k h


/-- If `π ∈ P \ P^2` then the powers of `π` are in the exact powers of the maximal ideal
`P`: `π ^ n ∈ P ^ n \ P ^ (n+1)` for all `n ≥ 1`. -/
lemma uniformizer_pow_not_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {π : R} (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    ∀ n : ℕ, 0 < n → π ^ n ∈ P ^ n ∧ π ^ n ∉ P ^ (n + 1) := by
  classical
  intro n hn
  have hπ0 : π ≠ 0 := by
    intro h0
    subst π
    exact hπ2 (by simp)
  have hπn0 : π ^ n ≠ 0 := pow_ne_zero n hπ0
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  have hcnt1 : (normalizedFactors (Ideal.span {π} : Ideal R)).count P = 1 := by
    exact Ideal.count_normalizedFactors_eq (p := P) (x := Ideal.span {π})
      (by simpa [Ideal.span_singleton_le_iff_mem] using hπ)
      (by simpa [Ideal.span_singleton_le_iff_mem] using hπ2)
  constructor
  · exact Ideal.pow_mem_pow hπ n
  · intro hπn
    have hge : n + 1 ≤ (normalizedFactors (Ideal.span {π ^ n} : Ideal R)).count P :=
      orderCount_ge_of_mem_pow (P := P) hπn0 (n + 1) hπn
    have hcnt : (normalizedFactors (Ideal.span {π ^ n} : Ideal R)).count P = n := by
      calc
        (normalizedFactors (Ideal.span {π ^ n} : Ideal R)).count P
            = (normalizedFactors ((Ideal.span {π} : Ideal R) ^ n)).count P := by
              rw [Ideal.span_singleton_pow]
        _ = n * (normalizedFactors (Ideal.span {π} : Ideal R)).count P := by
              rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
        _ = n := by rw [hcnt1, mul_one]
    omega

end Order


/-! ## Totally ramified structure, uniformizers, and the different -/

section TotallyRamified

/-- A maximal ideal of the ring of integers is nonzero. -/
lemma IsMaximal_ne_zero (P : Ideal (𝓞 K)) [P.IsMaximal] : P ≠ ⊥ := by
  exact (inferInstance : NeZero P).out

/-- Existence of a uniformizer of a maximal ideal `P` (an element of `P \ P^2`). -/
lemma exists_uniformizer (P : Ideal (𝓞 K)) [P.IsMaximal] :
    ∃ π : 𝓞 K, π ∈ P ∧ π ∉ P ^ 2 := by
  classical
  obtain ⟨x, hx1, hx2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P (IsMaximal_ne_zero P)
    ‹P.IsMaximal›.ne_top 1
  exact ⟨x, by simpa using hx1, hx2⟩

/-- Combined structure of a totally ramified extension at `P` over `P₀`. -/
theorem totallyRamified_structure (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E)) :
    (∀ Q : Ideal (𝓞 K), Q ∈ P₀.primesOver (𝓞 K) → Q = P) ∧
      P.inertiaDeg (𝓞 E) = 1 ∧
      Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E) := by
  classical
  have h₁ := unique_prime_over_of_totallyRamified (E := E) (K := K) P₀ P he
  refine ⟨h₁.1, h₁.2, ?_⟩
  exact map_P₀_eq_pow_of_unique (E := E) (K := K) P₀ P (IsMaximal_ne_zero P₀) h₁.1

/-- The map `𝓞 E → 𝓞 K` is injective. -/
lemma injective_ringOfIntegers_map : Function.Injective (algebraMap (𝓞 E) (𝓞 K)) := by
  have hE : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have hK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hfield : Function.Injective (algebraMap E K) := by
    intro a b h
    apply sub_eq_zero.mp
    by_contra hne
    have hz : algebraMap E K (a - b) = 0 := by rw [map_sub, h, sub_self]
    have hc : algebraMap E K (a - b) * algebraMap E K ((a - b)⁻¹) = 0 := by rw [hz, zero_mul]
    have h1 : algebraMap E K (a - b) * algebraMap E K ((a - b)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    exact one_ne_zero (hc ▸ h1.symm)
  have hEK : Function.Injective (algebraMap (𝓞 E) K) := by
    intro x y h
    apply hE
    apply hfield
    simpa [IsScalarTower.algebraMap_apply (R := 𝓞 E) (S := E) (A := K)] using h
  intro x y h
  apply hEK
  have : algebraMap (𝓞 K) K (algebraMap (𝓞 E) (𝓞 K) x) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 E) (𝓞 K) y) := by rw [h]
  simpa [IsScalarTower.algebraMap_apply (R := 𝓞 E) (S := 𝓞 K) (A := K)] using this

/-- The order at `P` of an element of `𝒪_E` is `e` times its order at `P₀`, where
`e` is the ramification index of `P` over `P₀`. -/
lemma orderCount_tower (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    {a : 𝓞 E} (ha : a ≠ 0) :
    orderCount P (algebraMap (𝓞 E) (𝓞 K) a) =
      P.ramificationIdx (𝓞 E) * orderCount P₀ a := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let f := algebraMap (𝓞 E) (𝓞 K)
  let e := P.ramificationIdx (𝓞 E)
  let c := (normalizedFactors (Ideal.span {a} : Ideal (𝓞 E))).count P₀
  have hIinj : Function.Injective f := injective_ringOfIntegers_map (E := E) (K := K)
  have hIa : (Ideal.span {a} : Ideal (𝓞 E)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  obtain ⟨Q, hPQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hIa P₀
  have hIQc : (Ideal.span {a} : Ideal (𝓞 E)) = P₀ ^ c * Q := by simpa [c] using hIQ
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hIa
    simpa [hQ, Ideal.mul_bot] using hIQc
  have hmapQ : ¬ P ∣ Ideal.map f Q := by
    intro hPdvd
    have hle : Ideal.map f Q ≤ P := (Ideal.dvd_iff_le).mp hPdvd
    have hcomap : Q ≤ Ideal.comap f P := (Ideal.map_le_iff_le_comap).mp hle
    have hQle : Q ≤ P₀ := by
      simpa [Ideal.LiesOver.over (P := P) (p := P₀)] using hcomap
    have : P₀ = ⊤ := by
      calc P₀ = P₀ ⊔ Q := by rw [sup_eq_left.mpr hQle]
           _ = ⊤ := hPQ
    exact ‹P₀.IsMaximal›.ne_top this
  have hmapQne : Ideal.map f Q ≠ ⊥ := by
    intro h
    apply hQne
    have hcomap : Q ≤ Ideal.comap f ⊥ := by
      exact (Ideal.map_le_iff_le_comap).mp (by simpa [h])
    have hker : Ideal.comap f ⊥ = ⊥ := by
      change RingHom.ker f = ⊥
      exact (RingHom.injective_iff_ker_eq_bot (f := f)).mp hIinj
    simpa [hker] using hcomap
  have hPne : P ≠ ⊥ := IsMaximal_ne_zero P
  have hfa : f a ≠ 0 := by
    intro h
    apply ha
    exact hIinj (by simpa using h)
  have hspan : Ideal.span {(f a)} = Ideal.map f (Ideal.span {a} : Ideal (𝓞 E)) := by
    simpa using (Ideal.map_span f {a}).symm
  have hEq : Ideal.map f (Ideal.span {a} : Ideal (𝓞 E)) = P ^ (e * c) * Ideal.map f Q := by
    calc
      Ideal.map f (Ideal.span {a} : Ideal (𝓞 E)) = Ideal.map f (P₀ ^ c * Q) := by rw [hIQc]
      _ = (Ideal.map f P₀) ^ c * Ideal.map f Q := by rw [Ideal.map_mul, Ideal.map_pow]
      _ = (P ^ e) ^ c * Ideal.map f Q := by rw [hmap]
      _ = P ^ (e * c) * Ideal.map f Q := by rw [pow_mul]
  have h1 : (normalizedFactors (P ^ (e * c))).count P = e * c := by
    have hp : Prime P := Ideal.prime_of_isPrime hPne ‹P.IsPrime›
    rw [Irreducible.normalizedFactors_pow hp.irreducible, Multiset.count_replicate]
    simp [normalize_eq P]
  have h2 : (normalizedFactors (Ideal.map f Q)).count P = 0 := by
    refine Multiset.count_eq_zero_of_notMem ?_
    intro hmem
    exact hmapQ (dvd_of_mem_normalizedFactors hmem)
  have hcnt : (normalizedFactors (Ideal.map f (Ideal.span {a} : Ideal (𝓞 E)))).count P = e * c := by
    rw [hEq]
    rw [normalizedFactors_mul (pow_ne_zero _ hPne) hmapQne]
    rw [Multiset.count_add, h1, h2]
    simp
  unfold orderCount
  rw [hspan, hcnt]


noncomputable def quotientAlgebra_inst (P₀ : Ideal (𝓞 E)) :
    Algebra ((𝓞 E) ⧸ P₀) ((𝓞 K) ⧸ (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)) := by
  classical
  exact Ideal.Quotient.algebraQuotientOfLEComap
    (p := P₀) (P := (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀))
    (by exact (Ideal.map_le_iff_le_comap (f := (algebraMap (𝓞 E) (𝓞 K)))).mp le_rfl)

lemma mk_uniformizer_pow_e_zero (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) :
    Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀) (π ^ P.ramificationIdx (𝓞 E)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rw [hmap]
  exact Ideal.pow_mem_pow hπ (P.ramificationIdx (𝓞 E))

lemma mk_uniformizer_pow_sub_one_ne_zero (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)
        (π ^ (P.ramificationIdx (𝓞 E) - 1)) ≠ 0 := by
  intro hzero
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  have hmem : π ^ (P.ramificationIdx (𝓞 E) - 1) ∈
      Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ := (Ideal.Quotient.eq_zero_iff_mem).mp hzero
  rw [hmap] at hmem
  have hpos : 0 < P.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos P (𝓞 E)
  by_cases he1 : P.ramificationIdx (𝓞 E) - 1 = 0
  · have h1e : (1 : 𝓞 K) ∈ P ^ P.ramificationIdx (𝓞 E) := by simpa [he1] using hmem
    have hinc : P ^ P.ramificationIdx (𝓞 E) ≤ P := by
      simpa using (Ideal.pow_le_pow_right (R := 𝓞 K) (I := P) (m := 1)
        (n := P.ramificationIdx (𝓞 E)) (by omega))
    have h1 : (1 : 𝓞 K) ∈ P := hinc h1e
    have htop : P = ⊤ := by
      apply eq_top_iff.mpr
      intro x
      simpa using (Ideal.mul_mem_left P x h1)
    exact ‹P.IsMaximal›.ne_top htop
  · have hn : 0 < P.ramificationIdx (𝓞 E) - 1 := Nat.pos_of_ne_zero he1
    have hv := uniformizer_pow_not_mem (R := 𝓞 K) P hπ hπ2 (P.ramificationIdx (𝓞 E) - 1) hn
    have hE : (P.ramificationIdx (𝓞 E) - 1) + 1 = P.ramificationIdx (𝓞 E) := Nat.sub_add_cancel hpos
    exact hv.2 (by simpa [hE] using hmem)

lemma uniformizer_pow_linearIndependent_quotient
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    LinearIndependent ((𝓞 E) ⧸ P₀) (fun i : Fin (P.ramificationIdx (𝓞 E)) =>
      (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀) π) ^ (i : ℕ)) := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let e := P.ramificationIdx (𝓞 E)
  let R := (𝓞 K) ⧸ (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)
  let k := (𝓞 E) ⧸ P₀
  letI : Field k := Ideal.Quotient.field P₀
  let πq : R := Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀) π
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hci
  have hpos : 0 < e := by
    dsimp [e]
    exact Ideal.ramificationIdx_pos P (𝓞 E)
  have hπq_e : πq ^ e = 0 := by
    have hz := mk_uniformizer_pow_e_zero (E := E) (K := K) P₀ P hmap π hπ
    simpa [πq] using (map_pow (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)) π e).trans hz
  have hπq_sub : πq ^ (e - 1) ≠ 0 := by
    intro h0
    have hz := mk_uniformizer_pow_sub_one_ne_zero (E := E) (K := K) P₀ P hmap π hπ hπ2
    exact hz (by simpa [πq] using h0)
  have hc' : (∑ j : Fin e, (algebraMap k R (c j)) * (πq ^ (j : ℕ))) = 0 := by
    simpa [Algebra.smul_def] using hc
  let S : Finset (Fin e) := Finset.univ.filter (fun j => c j ≠ 0)
  have hSi : i ∈ S := by simp [S, hci]
  have hS : S.Nonempty := ⟨i, hSi⟩
  let m : Fin e := S.min' hS
  have hmS : m ∈ S := Finset.min'_mem S hS
  have hcm : c m ≠ 0 := by simpa [S] using hmS
  have hmin : ∀ j : Fin e, j ∈ S → m ≤ j := fun j hj => Finset.min'_le S j hj
  have hzero_below : ∀ j : Fin e, (j : ℕ) < (m : ℕ) → c j = 0 := by
    intro j hj
    by_contra hj0
    have hjm : j ∈ S := by simp [S, hj0]
    have hle : (m : ℕ) ≤ (j : ℕ) := hmin j hjm
    exact (not_lt_of_ge hle) hj
  have hpow_ge_e : ∀ j : Fin e, (m : ℕ) < (j : ℕ) → πq ^ ((j : ℕ) + (e - 1 - (m : ℕ))) = 0 := by
    intro j hj
    have hexp : e ≤ (j : ℕ) + (e - 1 - (m : ℕ)) := by
      have hm_e : (m : ℕ) < e := m.2
      omega
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hexp
    rw [hs, pow_add, hπq_e, zero_mul]
  have hsum_collapse :
      (∑ j : Fin e, (algebraMap k R (c j)) * (πq ^ ((j : ℕ) + (e - 1 - (m : ℕ))))) =
        algebraMap k R (c m) * πq ^ (e - 1) := by
    have h₀ : ∀ b : Fin e, b ∈ (Finset.univ : Finset (Fin e)) → b ≠ m →
        (algebraMap k R (c b)) * (πq ^ ((b : ℕ) + (e - 1 - (m : ℕ)))) = 0 := by
      intro b hb hbm
      by_cases hb_lt : (b : ℕ) < (m : ℕ)
      · have hc0 : c b = 0 := hzero_below b hb_lt
        simp [hc0]
      · have hb_gt : (m : ℕ) < (b : ℕ) := by omega
        have hπt : πq ^ ((b : ℕ) + (e - 1 - (m : ℕ))) = 0 := hpow_ge_e b hb_gt
        simp [hπt]
    have hmm : (m : ℕ) + (e - 1 - (m : ℕ)) = e - 1 := by
      have hm_e : (m : ℕ) < e := m.2
      omega
    simpa [hmm] using (Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin e))) m
      (Finset.mem_univ m) h₀)
  have hmul_eq : (∑ j : Fin e, (algebraMap k R (c j)) * (πq ^ (j : ℕ)) * (πq ^ (e - 1 - (m : ℕ)))) =
      algebraMap k R (c m) * πq ^ (e - 1) := by
    simpa [pow_add, mul_assoc] using hsum_collapse
  have hmul_zero : (∑ j : Fin e, (algebraMap k R (c j)) * (πq ^ (j : ℕ)) * (πq ^ (e - 1 - (m : ℕ)))) = 0 := by
    rw [← Finset.sum_mul, hc', zero_mul]
  have hmain : algebraMap k R (c m) * πq ^ (e - 1) = 0 := by
    simpa [hmul_eq] using hmul_zero
  have hsmul : c m • (πq ^ (e - 1)) = 0 := by
    simpa [Algebra.smul_def] using hmain
  have hcancel : πq ^ (e - 1) = 0 := by
    have h1 : (c m)⁻¹ • (c m • (πq ^ (e - 1))) = 0 := by
      rw [hsmul, smul_zero]
    have h2 : (c m)⁻¹ • (c m • (πq ^ (e - 1))) = πq ^ (e - 1) := by
      rw [smul_smul, inv_mul_cancel₀ hcm, one_smul]
    exact h2 ▸ h1
  exact hπq_sub hcancel

lemma aeval_eq_sum_fin_of_pow_eq_zero {k R : Type*} [CommSemiring k] [CommRing R] [Algebra k R]
    (x : R) (e : ℕ) (hxe : x ^ e = 0) (p : k[X]) :
    Polynomial.aeval x p =
      ∑ j : Fin e, Polynomial.coeff p (j : ℕ) • x ^ (j : ℕ) := by
  classical
  let g : ℕ → R := fun i => Polynomial.coeff p i • x ^ i
  let N := max (p.natDegree + 1) e
  have hN1 : p.natDegree + 1 ≤ N := le_max_left _ _
  have hNe : e ≤ N := le_max_right _ _
  have hmain1 : (∑ i ∈ Finset.range (p.natDegree + 1), g i) = ∑ i ∈ Finset.range N, g i := by
    exact Finset.sum_subset (s₁ := Finset.range (p.natDegree + 1)) (s₂ := Finset.range N)
      (by intro i hi; exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hN1))
      (by
        intro i hi hiN
        have hi_large : p.natDegree + 1 ≤ i := by
          by_contra h
          exact hiN (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
        have hc : Polynomial.coeff p i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
          (Nat.lt_of_succ_le hi_large)
        simp [g, hc])
  have hmain2 : (∑ i ∈ Finset.range e, g i) = ∑ i ∈ Finset.range N, g i := by
    exact Finset.sum_subset (s₁ := Finset.range e) (s₂ := Finset.range N)
      (by intro i hi; exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) hNe))
      (by
        intro i hi hiN
        have hi_large : e ≤ i := by
          by_contra h
          exact hiN (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
        obtain ⟨s0, hs0⟩ := Nat.exists_eq_add_of_le hi_large
        rw [hs0]
        simp [g, pow_add, hxe])
  rw [Polynomial.aeval_eq_sum_range]
  rw [hmain1, ← hmain2]
  rw [← Fin.sum_univ_eq_sum_range g e]

lemma minpoly_coeff_uniformizer_mem_P₀ (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    ∀ j : ℕ, j < P.ramificationIdx (𝓞 E) →
      Polynomial.coeff (minpoly (𝓞 E) π) j ∈ P₀ := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let e := P.ramificationIdx (𝓞 E)
  let R := (𝓞 K) ⧸ (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)
  let k := (𝓞 E) ⧸ P₀
  letI : Field k := Ideal.Quotient.field P₀
  let πq : R := Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀) π
  let f := minpoly (𝓞 E) π
  have hf0 : Polynomial.aeval π f = 0 := minpoly.aeval (𝓞 E) π
  have hrel0 : (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀))
      (Polynomial.aeval π f) = 0 := by
    rw [hf0]
    simp
  have hrel : Polynomial.aeval πq (f.map (Ideal.Quotient.mk P₀)) = 0 := by
    let ψ : (𝓞 E) →+* R := (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)).comp
      (algebraMap (𝓞 E) (𝓞 K))
    have h2 : (algebraMap k R).comp (Ideal.Quotient.mk P₀) = ψ := by
      ext x
      change algebraMap k R (Ideal.Quotient.mk P₀ x) = algebraMap (𝓞 E) R x
      exact (IsScalarTower.algebraMap_apply (R := 𝓞 E) (S := k) (A := R) x).symm
    -- mk (aeval π f) = eval₂ ψ (mk π) f:
    have hA : Polynomial.eval₂ ψ (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀) π) f = 0 := by
      rw [Polynomial.aeval_def] at hrel0
      rw [Polynomial.hom_eval₂ (p := f) (f := algebraMap (𝓞 E) (𝓞 K))
        (g := Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)) (x := π)] at hrel0
      exact hrel0
    -- aeval πq (f.map mkP₀) = eval₂ ψ πq f:
    have hB : Polynomial.aeval πq (f.map (Ideal.Quotient.mk P₀)) =
        Polynomial.eval₂ ψ πq f := by
      rw [Polynomial.aeval_def]
      rw [Polynomial.eval₂_map]
      exact congrArg (fun h : (𝓞 E) →+* R => Polynomial.eval₂ h πq f) h2
    rw [hB]
    dsimp [πq]
    exact hA

  have hπq_e : πq ^ e = 0 := by
    have hz := mk_uniformizer_pow_e_zero (E := E) (K := K) P₀ P hmap π hπ
    simpa [πq] using (map_pow (Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀)) π e).trans hz
  have hfin : Polynomial.aeval πq (f.map (Ideal.Quotient.mk P₀)) =
      ∑ j : Fin e, (Ideal.Quotient.mk P₀ (Polynomial.coeff f (j : ℕ))) • πq ^ (j : ℕ) := by
    rw [aeval_eq_sum_fin_of_pow_eq_zero (x := πq) e hπq_e]
    simp [Polynomial.coeff_map]
  have hind := uniformizer_pow_linearIndependent_quotient (E := E) (K := K) P₀ P hmap π hπ hπ2
  have hall : ∀ i : Fin e, (Ideal.Quotient.mk P₀ (Polynomial.coeff f (i : ℕ))) = 0 := by
    rw [Fintype.linearIndependent_iff] at hind
    exact hind (fun i : Fin e => Ideal.Quotient.mk P₀ (Polynomial.coeff f (i : ℕ)))
      (by rw [← hfin]; exact hrel)
  intro j hj
  have hjf : Ideal.Quotient.mk P₀ (Polynomial.coeff f j) = 0 := by
    exact hall ⟨j, hj⟩
  exact (Ideal.Quotient.eq_zero_iff_mem.mp hjf)

lemma minpoly_uniformizer_natDegree_eq (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E)) :
    (minpoly (𝓞 E) π).natDegree = P.ramificationIdx (𝓞 E) := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  let e := P.ramificationIdx (𝓞 E)
  let f := minpoly (𝓞 E) π
  have hInt : IsIntegral (𝓞 E) π := IsIntegralClosure.isIntegral (R := 𝓞 E) (A := 𝓞 K) K π
  have hmonic : f.Monic := minpoly.monic hInt
  have hc := minpoly_coeff_uniformizer_mem_P₀ (E := E) (K := K) P₀ P hmap π hπ hπ2
  have hge : e ≤ f.natDegree := by
    by_contra hnot
    have hlt : f.natDegree < e := Nat.lt_of_not_ge hnot
    have hc0 : Polynomial.coeff f f.natDegree ∈ P₀ := hc f.natDegree hlt
    have h1e : (1 : 𝓞 E) ∈ P₀ := by
      have hlead : f.leadingCoeff = 1 := hmonic.leadingCoeff
      simpa [Polynomial.leadingCoeff] using (hlead ▸ hc0)
    have htop : P₀ = ⊤ := by
      apply eq_top_iff.mpr
      intro x
      simpa using (Ideal.mul_mem_left P₀ x h1e)
    exact ‹P₀.IsMaximal›.ne_top htop
  have hle : f.natDegree ≤ e := by
    have hfr := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 E) (K := E) (L := K)
      (S := 𝓞 K) (s := π) hInt
    have hb : (minpoly E ((algebraMap (𝓞 K) K) π)).natDegree ≤ Module.finrank E K :=
      minpoly.natDegree_le (A := E) (B := K) ((algebraMap (𝓞 K) K) π)
    rw [hfr] at hb
    rw [Polynomial.Monic.natDegree_map hmonic (algebraMap (𝓞 E) E)] at hb
    simpa [he] using hb
  exact le_antisymm hle hge

theorem uniformizer_generates_endgame (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E)) :
    Algebra.adjoin E {algebraMap (𝓞 K) K π} = ⊤ := by
  classical
  let x : K := algebraMap (𝓞 K) K π
  let M : IntermediateField E K := IntermediateField.adjoin E {x}
  have hxInt : IsIntegral E x := Algebra.IsIntegral.isIntegral x
  have hxAlg : IsAlgebraic E x := hxInt.isAlgebraic
  have hdegE : (minpoly E x).natDegree = P.ramificationIdx (𝓞 E) := by
    have hdeg := minpoly_uniformizer_natDegree_eq (E := E) (K := K) P₀ P hmap π hπ hπ2 he
    have hInt : IsIntegral (𝓞 E) π := IsIntegralClosure.isIntegral (R := 𝓞 E) (A := 𝓞 K) K π
    have hmonic : (minpoly (𝓞 E) π).Monic := minpoly.monic hInt
    have hfr := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 E) (K := E) (L := K)
      (S := 𝓞 K) (s := π) hInt
    -- x = algebraMap (𝓞K) K π, minpoly E x = (minpoly 𝓞E π).map ...
    rw [hfr]
    exact hdeg ▸ Polynomial.Monic.natDegree_map hmonic (algebraMap (𝓞 E) E)
  have hfinM : Module.finrank E M = Module.finrank E K := by
    rw [IntermediateField.adjoin.finrank hxInt, hdegE, he]
  have htopM : M = ⊤ := by
    have htopmod : Subalgebra.toSubmodule M.toSubalgebra = ⊤ := by
      exact Submodule.eq_top_of_finrank_eq (h := by
        simpa using hfinM)
    ext y
    constructor
    · intro hy; trivial
    · intro hy
      change y ∈ (Subalgebra.toSubmodule M.toSubalgebra)
      simpa [htopmod]
  have hadj : M.toSubalgebra = Algebra.adjoin E {x} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (F := E) (E := K) (α := x) hxAlg
  -- M = ⊤: toSubalgebra of ⊤ is ⊤
  have htopalg : (⊤ : IntermediateField E K).toSubalgebra = ⊤ := by
    ext; simp
  have hMalg : M.toSubalgebra = ⊤ := by
    rw [htopM]
    exact htopalg
  rw [← hadj]
  exact hMalg


lemma aeval_derivative_eq_sum (π : 𝓞 K) (f : (𝓞 E)[X]) (e : ℕ) (he : f.natDegree = e) :
    Polynomial.aeval π (Polynomial.derivative f) =
      ∑ i ∈ Finset.range (e + 1), (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) *
        (i : 𝓞 K) * (π ^ (i - 1)) := by
  classical
  have hder : Polynomial.derivative f =
      ∑ i ∈ Finset.range (e + 1),
        Polynomial.derivative (Polynomial.monomial i (Polynomial.coeff f i)) := by
    calc
      Polynomial.derivative f
          = Polynomial.derivative
              (∑ i ∈ Finset.range (f.natDegree + 1), Polynomial.monomial i (Polynomial.coeff f i)) := by
              conv_lhs => rw [Polynomial.as_sum_range f]
      _ = ∑ i ∈ Finset.range (f.natDegree + 1),
            Polynomial.derivative (Polynomial.monomial i (Polynomial.coeff f i)) := by
              rw [Polynomial.derivative_sum]
      _ = ∑ i ∈ Finset.range (e + 1),
            Polynomial.derivative (Polynomial.monomial i (Polynomial.coeff f i)) := by
              rw [he]
  rw [hder]
  rw [map_sum (Polynomial.aeval π) (fun i =>
    Polynomial.derivative (Polynomial.monomial i (Polynomial.coeff f i))) (Finset.range (e + 1))]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Polynomial.derivative_monomial]
  rw [Polynomial.aeval_monomial]
  simp only [map_mul, map_natCast]

lemma orderCount_eq_zero_of_not_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] {x : R} (hx : x ∉ P) : orderCount P x = 0 := by
  classical
  exact orderCount_eq_of_mem_pow_not_mem_pow_succ (P := P) (x := x) (k := 0)
    (by simp) (by simpa using hx)

lemma uniformizer_e_term_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (htame : ¬ p ∣ P.ramificationIdx (𝓞 E)) :
    ((P.ramificationIdx (𝓞 E) : 𝓞 K) * π ^ (P.ramificationIdx (𝓞 E) - 1)) ∉
      P ^ P.ramificationIdx (𝓞 E) := by
  classical
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let e := P.ramificationIdx (𝓞 E)
  have hpos : 0 < e := by dsimp [e]; exact Ideal.ramificationIdx_pos P (𝓞 E)
  -- e ∉ P (as element): 
  have he_notP : (e : 𝓞 K) ∉ P := by
    intro hmem
    -- (e : 𝓞K) ∈ P ⇒ (e:𝓞E) ∈ P₀
    have hememE : (e : 𝓞 E) ∈ P₀ := by
      -- P₀ = under 𝓞E P
      have hunder : P₀ = Ideal.under (𝓞 E) P := by
        exact (Ideal.LiesOver.over (p := P₀) (P := P))
      rw [hunder]
      -- membership in comap: (e : 𝓞E) maps to (e : 𝓞K) ∈ P
      exact Ideal.mem_comap.mp (by simpa using hmem)
    -- (e : 𝓞E) ∈ P₀ ⇒ e ∈ span{(p:ℤ)} ⇒ p | e
    have hespan : (e : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := by
      have hunder0 : Ideal.span ({(p : ℤ)} : Set ℤ) = Ideal.under ℤ P₀ := by
        exact (Ideal.LiesOver.over (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (P := P₀))
      rw [hunder0]
      exact Ideal.mem_comap.mp (by simpa using hememE)
    have hpdvd : p ∣ e := by
      -- e : ℤ in span{(p:ℤ)} means (p:ℤ) | (e:ℤ)
      have : (p : ℤ) ∣ (e : ℤ) := (Ideal.mem_span_singleton.mp hespan)
      exact Int.ofNat_dvd.mp this
    exact htame hpdvd
  have hord0 : orderCount P (e : 𝓞 K) = 0 := orderCount_eq_zero_of_not_mem (P := P) he_notP
  have hπne : π ≠ 0 := by
    intro h0
    subst π
    exact hπ2 (by simp)
  by_cases he1 : e - 1 = 0
  · -- e = 1: π^0 = 1; e·1 = e ∉ P
    have he1' : e = 1 := by omega
    simpa [e, he1', pow_zero, mul_one] using he_notP
  · -- 0 < e-1:
    have hn : 0 < e - 1 := Nat.pos_of_ne_zero he1
    have hv := uniformizer_pow_not_mem (R := 𝓞 K) P hπ hπ2 (e - 1) hn
    have hx1 : π ^ (e - 1) ∈ P ^ (e - 1) := hv.1
    have hE' : (e - 1) + 1 = e := Nat.sub_add_cancel hpos
    have hx2 : π ^ (e - 1) ∉ P ^ e := by
      simpa [hE'] using hv.2
    have hz := mul_of_order_eq_zero (P := P) (c := (e : 𝓞 K)) (x := π ^ (e - 1))
      (hc := by exact_mod_cast (show e ≠ 0 from Nat.ne_of_gt hpos))
      (hord := hord0) (k := e - 1) hx1 (by simpa [hE'] using hx2)
    simpa [e, hE'] using hz.2

lemma derivative_uniformizer_tame_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal]
    [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ = P ^ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2)
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E))
    (htame : ¬ p ∣ P.ramificationIdx (𝓞 E)) :
    Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 E) π)) ∉
      P ^ P.ramificationIdx (𝓞 E) := by
  classical
  letI : P₀.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P₀.IsMaximal)
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  let e := P.ramificationIdx (𝓞 E)
  let f := minpoly (𝓞 E) π
  have hpos : 0 < e := by dsimp [e]; exact Ideal.ramificationIdx_pos P (𝓞 E)
  have hdeg : f.natDegree = e := by
    dsimp [f, e]
    exact minpoly_uniformizer_natDegree_eq (E := E) (K := K) P₀ P hmap π hπ hπ2 he
  have hc := minpoly_coeff_uniformizer_mem_P₀ (E := E) (K := K) P₀ P hmap π hπ hπ2
  have hmain : ((e : 𝓞 K) * π ^ (e - 1)) ∉ P ^ e := by
    dsimp [e]
    exact uniformizer_e_term_not_mem_pow (E := E) (K := K) p P₀ P hmap π hπ hπ2 htame
  have hsum : Polynomial.aeval π (Polynomial.derivative f) =
      ∑ i ∈ Finset.range (e + 1),
        (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1)) := by
    dsimp [f, e]
    exact aeval_derivative_eq_sum π f e hdeg
  have hterm_lt : ∀ i : ℕ, i < e →
      (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1)) ∈ P ^ e := by
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp
    · have hci : Polynomial.coeff f i ∈ P₀ := hc i hi
      have hmem : (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) ∈ P ^ e := by
        have h1 : algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i) ∈
            Ideal.map (algebraMap (𝓞 E) (𝓞 K)) P₀ :=
              Ideal.mem_map_of_mem (f := algebraMap (𝓞 E) (𝓞 K)) hci
        simpa [hmap] using h1
      have hmem' : (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) ∈ P ^ e := by
        simpa [mul_comm] using (Ideal.mul_mem_left (P ^ e) (i : 𝓞 K) hmem)
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Ideal.mul_mem_left (P ^ e) (π ^ (i - 1)) hmem')
  have hrest : (∑ i ∈ Finset.range e,
      (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1))) ∈ P ^ e := by
    exact Submodule.sum_mem (p := P ^ e) (t := (Finset.range e))
      (f := fun i => (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1)))
      (fun i hi => hterm_lt i (Finset.mem_range.mp hi))
  have hce : Polynomial.coeff f e = 1 := by
    have hInt : IsIntegral (𝓞 E) π := IsIntegralClosure.isIntegral (R := 𝓞 E) (A := 𝓞 K) K π
    have hmonic : f.Monic := minpoly.monic hInt
    have hlc : f.leadingCoeff = 1 := hmonic.leadingCoeff
    simpa [Polynomial.leadingCoeff, hdeg] using hlc
  intro hmem
  -- total = rest + term_e ; term_e ∉ P^e:
  have hsum_succ := Finset.sum_range_succ (fun i : ℕ =>
      (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1))) e
  -- hsum_succ : ∑ range (e+1) = ∑ range e + term e
  have htotal : ((e : 𝓞 K) * π ^ (e - 1)) ∈ P ^ e := by
    -- total ∈ P^e (hmem) and rest ∈ P^e ⇒ term_e = total - rest ∈ P^e
    have hterm_e : (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f e)) * (e : 𝓞 K) * (π ^ (e - 1)) ∈ P ^ e := by
      have : (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f e)) * (e : 𝓞 K) * (π ^ (e - 1))
          = ((∑ i ∈ Finset.range (e + 1),
              (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1))))
            - (∑ i ∈ Finset.range e,
              (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1))) := by
        rw [hsum_succ]
        ring
      have hA : (∑ i ∈ Finset.range (e + 1),
          (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f i)) * (i : 𝓞 K) * (π ^ (i - 1))) ∈ P ^ e := by
        simpa [f, hsum] using hmem
      have : (algebraMap (𝓞 E) (𝓞 K) (Polynomial.coeff f e)) * (e : 𝓞 K) * (π ^ (e - 1)) ∈ P ^ e := by
        rw [this]
        exact Submodule.sub_mem _ hA hrest
      simpa [hce] using this
    -- term_e = (1) * e * π^{e-1} = e·π^{e-1}:
    have hmain' : ((e : 𝓞 K) * π ^ (e - 1)) ∈ P ^ e := by
      simpa [hce, one_mul, mul_assoc] using hterm_e
    exact hmain'
  exact False.elim (hmain htotal)

/-- A uniformizer of a totally ramified extension generates the whole field. -/
theorem uniformizer_generates {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K]
    [Algebra E K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    Algebra.adjoin E {algebraMap (𝓞 K) K π} = ⊤ := by
  classical
  have hstruc := totallyRamified_structure (E := E) (K := K) p P₀ P he
  exact uniformizer_generates_endgame (E := E) (K := K) P₀ P hstruc.2.2 π hπ hπ2 he

/-- The derivative of the minimal polynomial of a uniformizer lies in the different. -/
lemma uniformizer_derivative_mem_different (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 E) π)) ∈
      differentIdeal (𝓞 E) (𝓞 K) := by
  classical
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  -- the uniformizer generates K over E:
  have hgen : Algebra.adjoin E {algebraMap (𝓞 K) K π} = ⊤ :=
    uniformizer_generates (E := E) (K := K) p P₀ P he π hπ hπ2
  exact aeval_derivative_mem_differentIdeal (A := 𝓞 E) (K := E) (L := K)
    (B := 𝓞 K) π hgen

/-- The derivative of the minimal polynomial of a uniformizer is not in `P ^ e`. -/
lemma uniformizer_derivative_not_mem_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (𝓞 E)) [P₀.IsMaximal] [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (𝓞 E))
    (htame : ¬ p ∣ P.ramificationIdx (𝓞 E))
    (π : 𝓞 K) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) :
    Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 E) π)) ∉
      P ^ P.ramificationIdx (𝓞 E) := by
  classical
  have hstruc := totallyRamified_structure (E := E) (K := K) p P₀ P he
  exact derivative_uniformizer_tame_not_mem_pow (E := E) (K := K) p P₀ P hstruc.2.2
    π hπ hπ2 he htame

/-- The main tame totally ramified different bound. -/
theorem tame_totallyRamified_different_not_pow_dvd
    {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K] [Algebra E K]
    (p : ℕ) [Fact (Nat.Prime p)]
    (P₀ : Ideal (NumberField.RingOfIntegers E)) [P₀.IsMaximal]
    [P₀.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal] [P.LiesOver P₀]
    (he : Module.finrank E K = P.ramificationIdx (NumberField.RingOfIntegers E))
    (htame : ¬ p ∣ P.ramificationIdx (NumberField.RingOfIntegers E)) :
    ¬ P ^ P.ramificationIdx (NumberField.RingOfIntegers E) ∣
      differentIdeal (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) := by
  classical
  haveI : P.IsPrime := Ideal.IsMaximal.isPrime (by infer_instance : P.IsMaximal)
  obtain ⟨π, hπ, hπ2⟩ := exists_uniformizer P
  have hm : Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 E) π)) ∈
      differentIdeal (𝓞 E) (𝓞 K) :=
    uniformizer_derivative_mem_different (E := E) (K := K) p P₀ P he π hπ hπ2
  have hn : Polynomial.aeval π (Polynomial.derivative (minpoly (𝓞 E) π)) ∉
      P ^ P.ramificationIdx (𝓞 E) :=
    uniformizer_derivative_not_mem_pow (E := E) (K := K) p P₀ P he htame π hπ hπ2
  intro hdiv
  have hle : differentIdeal (𝓞 E) (𝓞 K) ≤ P ^ P.ramificationIdx (𝓞 E) :=
    (Ideal.dvd_iff_le).mp hdiv
  exact hn (hle hm)

end TotallyRamified

end Commons.NumberTheory.NumberField