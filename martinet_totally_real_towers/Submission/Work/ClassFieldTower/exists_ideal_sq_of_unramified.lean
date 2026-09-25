import Mathlib
import Submission.Work.ClassFieldTower.Defs

namespace Work.ClassFieldTower

open scoped Classical
open NumberField

set_option linter.unusedVariables false

/-! ## Auxiliary lemmas

These are the two purely formal ingredients of the proof:

* `isSquare_coe_iff` : the inclusion `α → WithZero α` (for `α` a monoid) reflects and preserves
  squares;
* `isSquare_exp_iff` : accordingly, `WithZero.exp m` is a square in `ℤᵐ⁰` iff `m` is even.
-/

private lemma isSquare_coe_iff {α : Type*} [Monoid α] (x : α) :
    IsSquare (↑x : WithZero α) ↔ IsSquare x := by
  refine ⟨?_, fun h => h.map (WithZero.coeMonoidHom (α := α))⟩
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := fun h0 =>
    WithZero.coe_ne_zero (show (↑x : WithZero α) = 0 by rw [hr, h0, mul_zero])
  refine ⟨WithZero.unzero hr0, ?_⟩
  apply WithZero.coe_inj.mp
  rw [WithZero.coe_mul, WithZero.coe_unzero hr0]
  exact hr

private lemma isSquare_exp_iff (m : ℤ) : IsSquare (WithZero.exp m) ↔ Even m := by
  unfold WithZero.exp
  rw [isSquare_coe_iff, isSquare_ofAdd_iff]

/-- In the monoid of ideals of a semiring, an idempotent square root of `1` is `1`:
`I * I = 1` forces `I = 1` (because `I * I ≤ I` and `1` is the top ideal). -/
private lemma Ideal.eq_one_of_mul_self_eq_one {R : Type*} [Semiring R] {I : Ideal R} [I.IsTwoSided]
    (h : I * I = 1) : I = 1 := by
  have hh := Ideal.mul_le_left (I := I) (J := I)
  rw [h, Ideal.one_eq_top] at hh
  rw [top_le_iff.mp hh, Ideal.one_eq_top]

/-- **Assembling principal ideals with even valuations.**

If every prime valuation of a principal ideal `(a)` (with `a ≠ 0`) is even, then `(a)` is the
square of an integral ideal, namely of the finprod `∏_v v^{v(a)/2}` over the height one primes,
which is a finitely supported product of genuine prime powers because the exponents are
nonnegative. -/
theorem exists_ideal_sq_of_even_count {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) (ha : a ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        Even (FractionalIdeal.count K v
          ((Ideal.span {a}) : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))) :
    ∃ I : Ideal (NumberField.RingOfIntegers K), I * I = Ideal.span {a} := by
  classical
  have hspan : Ideal.span {a} ≠ 0 := fun hh => ha (Ideal.span_singleton_eq_bot.mp hh)
  -- the multiplicity of `v` in `(a)`, as a natural number
  set N : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors with hN
  have hNeven : ∀ v, Even (N v) := by
    intro v
    rw [hN]
    exact (Int.even_coe_nat _).mp (by rw [← FractionalIdeal.count_coe K v hspan]; exact h v)
  have h2N : ∀ v, N v = 2 * (N v / 2) := fun v =>
    (Nat.mul_div_cancel' (even_iff_two_dvd.mp (hNeven v))).symm
  have hmax : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v.maxPowDividing (Ideal.span {a}) = v.asIdeal ^ (N v) := by
    intro v
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hN]
  -- finiteness of the support
  have hfsG : Function.HasFiniteMulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        v.maxPowDividing (Ideal.span {a})) := Ideal.hasFiniteMulSupport hspan
  have hfs : Function.HasFiniteMulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        v.asIdeal ^ (N v / 2)) := by
    refine hfsG.subset (fun v hv => ?_)
    simp only [Function.mem_mulSupport] at hv ⊢
    intro h1
    rw [hmax v, h2N v, Nat.mul_comm, pow_mul] at h1
    exact hv (Ideal.eq_one_of_mul_self_eq_one (by rwa [pow_two] at h1))
  refine ⟨∏ᶠ v, v.asIdeal ^ (N v / 2), ?_⟩
  rw [← pow_two, finprod_pow hfs]
  have hcongr : (∏ᶠ v, (v.asIdeal ^ (N v / 2)) ^ 2) = ∏ᶠ v, v.asIdeal ^ (N v) :=
    finprod_congr (fun v => by rw [← pow_mul, Nat.mul_comm, ← h2N v])
  rw [hcongr, ← finprod_congr hmax]
  exact Ideal.finprod_heightOneSpectrum_factorization hspan

/-- **Unramifiedness forces even valuations** (the second ingredient of the elementary Kummer
two-descent): if a finite Galois extension `L/K` of number fields is unramified
(`differentIdeal (𝓞 K) (𝓞 L) = ⊤`) and `a ∈ 𝓞 K` has a square root in `L`, then the principal ideal
`(a) = Ideal.span {a}` is a square of an integral ideal of `𝓞 K`.

Proof strategy: suppose `P` is a prime ideal of `𝓞 K` with `v_P(a)` odd.  Write
`a = π^{2k+1} u` with `π` a uniformizer at `P` and `u` a unit; then
`K(√a) = K(√(π u))` and `X² - πu` is Eisenstein at `P`, so `K_P(√a)/K_P` is totally ramified of
degree `2`, i.e. `P` ramifies in `K(√a)`.  Since `K(√a) ⊆ L` and ramification indices multiply in a
tower (`Ideal.ramificationIdx_tower`), `P` ramifies in `L/K` as well, contradicting
`differentIdeal (𝓞 K) (𝓞 L) = ⊤` (equivalently `Q.ramificationIdx (𝓞 K) = 1` for all primes `Q`,
`Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal`).  Hence all
`v_P(a)` are even, and `I := ∏_P P^{v_P(a)/2}` is an integral ideal with `I * I = (a)`.

(The ideal-theoretic assembling of the even exponents is
`Work.ShafarevichKoch.exists_sq_eq_of_forall_even_count`; the content here is the local
ramification step.) -/
theorem exists_ideal_sq_of_unramified {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (a : NumberField.RingOfIntegers K) (ha : a ≠ 0)
    (hunr : differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤)
    (hsq : ∃ b : L, b * b = algebraMap K L (a : K)) :
    ∃ I : Ideal (NumberField.RingOfIntegers K), I * I = Ideal.span {a} := by
  obtain ⟨b, hb⟩ := hsq
  refine exists_ideal_sq_of_even_count a ha (fun 𝔭 => ?_)
  -- pick a height one prime `𝔓` of `𝓞 L` lying over `𝔭`
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_primesOver (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers L) 𝔭.asIdeal
  have hQprime : Q.IsPrime := hQ.1
  have hQlies : Q.LiesOver 𝔭.asIdeal := hQ.2
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot hQ
  let 𝔓 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    IsDedekindDomain.HeightOneSpectrum.mk Q hQprime hQne
  have hlies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := hQlies
  -- unramifiedness: the ramification index of `𝔓` over `𝔭` is `1`
  have hnotdvd :
      ¬ 𝔓.asIdeal ∣ differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) := by
    rw [hunr]
    exact fun h => 𝔓.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
  have hram : 𝔓.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
    (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := K) (K := L) 𝔓.asIdeal 𝔓.isPrime).mp hnotdvd
  have hram' : 𝔭.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal 𝔓.asIdeal 𝔭.ne_bot, hram]
  -- the `𝔓`-adic valuation of `a` is the square of the `𝔓`-adic valuation of `b`
  have hval := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L) L 𝔭 𝔓 (a : K)
  rw [hram', pow_one] at hval
  have hsquare : IsSquare (𝔭.valuation K (a : K)) := by
    rw [hval, ← hb]
    exact ⟨_, by rw [map_mul]⟩
  -- `𝔭.valuation K a = exp (-count)`
  have hspan : Ideal.span {a} ≠ 0 := fun hh => ha (Ideal.span_singleton_eq_bot.mp hh)
  have hval2 : 𝔭.valuation K (a : K) = WithZero.exp
      (-(FractionalIdeal.count K 𝔭
        ((Ideal.span {a}) : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg 𝔭 (r := a) ha,
      FractionalIdeal.count_coe K 𝔭 hspan]
  rw [hval2] at hsquare
  have h1 : Even (-(FractionalIdeal.count K 𝔭
      ((Ideal.span {a}) : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))) :=
    (isSquare_exp_iff _).mp hsquare
  obtain ⟨k, hk⟩ := h1
  exact ⟨-k, by omega⟩

end Work.ClassFieldTower
