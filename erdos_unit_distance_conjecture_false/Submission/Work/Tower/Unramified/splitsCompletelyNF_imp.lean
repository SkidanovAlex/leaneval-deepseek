import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

/-!
# Complete splitting descends along the base and along primes

Let `F ⊆ L` be an extension of number fields and let `q` be a rational prime.  If `q` splits
completely in `L` (in the normal form `Work.Tower.Unramified.SplitsCompletelyNF q L`), then
`q` splits completely in `F` and every prime `𝔭` of `𝓞 F` above `q` splits completely in the
extension `L/F`.

This is the standard tower computation.  Fix a prime `P` of `𝓞 L` above a prime `𝔭` of `𝓞 F`
above `q`.  Then

* `P` lies over `q`, so `e(P/q) = f(P/q) = 1` by hypothesis;
* ramification indices and inertia degrees are multiplicative in towers
  (`Ideal.ramificationIdx_tower`, `Ideal.inertiaDeg_tower`), so
  `e(𝔭/q) ∣ e(P/q) = 1` and `f(𝔭/q) ∣ f(P/q) = 1`
  (`Ideal.ramificationIdx_below_dvd`, `Ideal.inertiaDeg_below_dvd`), hence `e(𝔭/q) = f(𝔭/q) = 1`;
* dually `e(P/𝔭) ∣ e(P/q) = 1` and `f(P/𝔭) ∣ f(P/q) = 1`
  (`Ideal.ramificationIdx_above_dvd`, `Ideal.inertiaDeg_above_dvd`), hence `e(P/𝔭) = f(P/𝔭) = 1`.

The counting is then the fundamental identity `∑_{P | 𝔭} e(P) f(P) = [L : F]`
(`Ideal.sum_ramification_inertia_eq_finrank`) together with the corresponding identity over `ℤ`:
since every term of each sum is `1`, the number of primes above `𝔭` in `𝓞 L` is `[L : F]`, and the
number of primes above `q` in `𝓞 F` is `[F : ℚ]`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

theorem splitsCompletelyNF_imp {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] (q : ℕ) (hq : Nat.Prime q)
    (h : Work.Tower.Unramified.SplitsCompletelyNF q L) :
    Work.Tower.Unramified.SplitsCompletelyNF q F ∧
      ∀ 𝔭 : Ideal (NumberField.RingOfIntegers F), 𝔭.IsPrime →
        (q : NumberField.RingOfIntegers F) ∈ 𝔭 →
        Work.Tower.Unramified.SplitsCompletelyInNF F L 𝔭 := by
  classical
  -- `(q) ⊆ ℤ` is a prime (indeed maximal) ideal.
  haveI hqprime : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsPrime := isPrime_span_singleton_int hq
  have hqF : (q : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  obtain ⟨hcardL, hefL⟩ := h
  -- Step 1: every prime of `𝓞 F` above `q` has ramification index and inertia degree `1` over `ℤ`.
  have hefF : ∀ 𝔭 : (Ideal.span {(q : ℤ)}).primesOver (𝓞 F),
      𝔭.1.ramificationIdx ℤ = 1 ∧ 𝔭.1.inertiaDeg ℤ = 1 := by
    intro 𝔭
    obtain ⟨h𝔭prime, h𝔭lie⟩ := 𝔭.2
    have hq𝔭 : (q : 𝓞 F) ∈ 𝔭.1 := ((mem_primesOver_span_nat_iff hq 𝔭.1).mp 𝔭.2).2
    haveI : 𝔭.1.IsPrime := h𝔭prime
    haveI : 𝔭.1.LiesOver (Ideal.span {(q : ℤ)}) := h𝔭lie
    have h𝔭0 : 𝔭.1 ≠ ⊥ := by
      intro hbot
      have h0 : (q : 𝓞 F) = 0 := by simpa [hbot] using hq𝔭
      exact hqF h0
    haveI : 𝔭.1.IsMaximal := h𝔭prime.isMaximal h𝔭0
    -- a prime `P` of `𝓞 L` above `𝔭` (hence above `q`)
    obtain ⟨P, hPmax, hPlie⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 F) (S := 𝓞 L) 𝔭.1
    haveI : P.LiesOver 𝔭.1 := hPlie
    haveI : P.IsPrime := hPmax.isPrime
    have hPmem : P ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 L) :=
      ⟨hPmax.isPrime, Ideal.LiesOver.trans P 𝔭.1 (Ideal.span {(q : ℤ)})⟩
    obtain ⟨hPe, hPf⟩ := hefL ⟨P, hPmem⟩
    -- `e(𝔭/q) ∣ e(P/q) = 1` and `f(𝔭/q) ∣ f(P/q) = 1`
    exact ⟨Nat.dvd_one.mp (hPe ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) (q := 𝔭.1) (r := P)),
           Nat.dvd_one.mp (hPf ▸ Ideal.inertiaDeg_below_dvd (R := ℤ) (q := 𝔭.1) (r := P))⟩
  -- Step 2: `q` splits completely in `F`, by the fundamental identity over `ℤ`.
  have hcardF : Nat.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 F)) = Module.finrank ℚ F := by
    haveI : Fintype ((Ideal.span {(q : ℤ)}).primesOver (𝓞 F)) :=
      (Algebra.QuasiFinite.finite_primesOver (R := ℤ) (S := 𝓞 F) (Ideal.span {(q : ℤ)})).fintype
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card ((Ideal.span {(q : ℤ)}).primesOver (𝓞 F))
        = ∑ _x : (Ideal.span {(q : ℤ)}).primesOver (𝓞 F), (1 : ℕ) := Fintype.card_eq_sum_ones
      _ = ∑ x : (Ideal.span {(q : ℤ)}).primesOver (𝓞 F),
            x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ :=
          Finset.sum_congr rfl fun x _ => by rw [(hefF x).1, (hefF x).2, mul_one]
      _ = Module.finrank ℤ (𝓞 F) :=
          Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (Ideal.span {(q : ℤ)}) (𝓞 F)
      _ = Module.finrank ℚ F := RingOfIntegers.rank F
  refine ⟨⟨hcardF, hefF⟩, ?_⟩
  -- Step 3: a prime `𝔭` of `𝓞 F` containing `q` splits completely in `L/F`.
  intro 𝔭 h𝔭prime hq𝔭
  haveI : 𝔭.IsPrime := h𝔭prime
  have h𝔭mem : 𝔭 ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 F) :=
    (mem_primesOver_span_nat_iff hq 𝔭).mpr ⟨h𝔭prime, hq𝔭⟩
  haveI : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := h𝔭mem.2
  -- every prime of `𝓞 L` above `𝔭` has `e = f = 1` over `𝓞 F`
  have hef𝔭 : ∀ P : 𝔭.primesOver (𝓞 L),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
    intro P
    haveI : P.1.LiesOver 𝔭 := P.2.2
    haveI : P.1.IsPrime := P.2.1
    have hPmem : P.1 ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 L) :=
      ⟨P.2.1, Ideal.LiesOver.trans P.1 𝔭 (Ideal.span {(q : ℤ)})⟩
    obtain ⟨hPe, hPf⟩ := hefL ⟨P.1, hPmem⟩
    -- `e(P/𝔭) ∣ e(P/q) = 1` and `f(P/𝔭) ∣ f(P/q) = 1`
    exact ⟨Nat.dvd_one.mp (hPe ▸ Ideal.ramificationIdx_above_dvd (R := ℤ) (q := 𝔭) (r := P.1)),
           Nat.dvd_one.mp (hPf ▸ Ideal.inertiaDeg_above_dvd (R := ℤ) (q := 𝔭) (r := P.1))⟩
  -- there are exactly `[L : F]` primes of `𝓞 L` above `𝔭`, by the fundamental identity in `L/F`
  have hcard𝔭 : Nat.card (𝔭.primesOver (𝓞 L)) = Module.finrank F L := by
    haveI : Fintype (𝔭.primesOver (𝓞 L)) :=
      (Algebra.QuasiFinite.finite_primesOver (R := 𝓞 F) (S := 𝓞 L) 𝔭).fintype
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card (𝔭.primesOver (𝓞 L))
        = ∑ _x : 𝔭.primesOver (𝓞 L), (1 : ℕ) := Fintype.card_eq_sum_ones
      _ = ∑ x : 𝔭.primesOver (𝓞 L), x.1.ramificationIdx (𝓞 F) * x.1.inertiaDeg (𝓞 F) :=
          Finset.sum_congr rfl fun x _ => by rw [(hef𝔭 x).1, (hef𝔭 x).2, mul_one]
      _ = Module.finrank (𝓞 F) (𝓞 L) :=
          Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) 𝔭 (𝓞 L)
      _ = Module.finrank F L := (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L).symm
  exact ⟨hcard𝔭, hef𝔭⟩

end Work.Tower.Unramified
