import Mathlib
import Submission.Work.Tower.Unramified.SplitsCompletelyNF

/-!
# Complete splitting is detected on the primes of the base

If a rational prime `q` splits completely in the number field `F`, and every prime `𝔭` of `𝓞 F`
above `q` splits completely in the extension `L/F`, then `q` splits completely in `L`.

The proof works with the counting normal form `SplitsCompletelyNF` of `SplitsCompletely`:
* for a prime `P` of `𝓞 L` above `q`, its contraction `𝔭 = P ∩ 𝓞 F` is a prime of `𝓞 F` above `q`,
  so `e(𝔭/q) = f(𝔭/q) = 1` by `hF` and `e(P/𝔭) = f(P/𝔭) = 1` by `hrel`; multiplicativity of the
  ramification index and inertia degree in towers (`Ideal.ramificationIdx_tower`,
  `Ideal.inertiaDeg_tower`) then gives `e(P/q) = f(P/q) = 1`;
* the fundamental identity `∑_{P | q} e(P/q) f(P/q) = [L : ℚ]`
  (`Ideal.sum_ramification_inertia_eq_finrank`) then shows that the primes of `𝓞 L` above `q`
  number `[L : ℚ]`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

theorem splitsCompletelyNF_of {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] (q : ℕ) (hq : Nat.Prime q)
    (hF : Work.Tower.Unramified.SplitsCompletelyNF q F)
    (hrel : ∀ 𝔭 : Ideal (NumberField.RingOfIntegers F), 𝔭.IsPrime →
        (q : NumberField.RingOfIntegers F) ∈ 𝔭 →
        Work.Tower.Unramified.SplitsCompletelyInNF F L 𝔭) :
    Work.Tower.Unramified.SplitsCompletelyNF q L := by
  classical
  -- The rational prime ideal `(q) ⊆ ℤ`.
  let pZ : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hpZprime : pZ.IsPrime := by
    rw [show pZ = Ideal.span {(q : ℤ)} from rfl]
    exact isPrime_span_singleton_int hq
  -- The primes of `𝓞 L` above `(q)` form a finite set.
  have hfinL : Fintype (pZ.primesOver (𝓞 L)) := (Algebra.QuasiFinite.finite_primesOver pZ).fintype
  -- Every prime of `𝓞 L` above `(q)` has ramification index and inertia degree `1` over `ℤ`.
  have hef : ∀ P : pZ.primesOver (𝓞 L),
      P.1.ramificationIdx ℤ = 1 ∧ P.1.inertiaDeg ℤ = 1 := by
    intro P
    have hPp : P.1.IsPrime := P.2.1
    have hPL : P.1.LiesOver pZ := P.2.2
    -- the contraction of `P` to `𝓞 F`
    let 𝔭 : Ideal (𝓞 F) := P.1.under (𝓞 F)
    have h𝔭p : 𝔭.IsPrime := Ideal.IsPrime.under (𝓞 F) P.1
    have h𝔭L : 𝔭.LiesOver pZ :=
      Ideal.LiesOver.tower_bot (𝔓 := P.1) (P := P.1.under (𝓞 F)) (p := pZ)
    -- `q` lies in `𝔭`
    have hqmem : (q : 𝓞 F) ∈ 𝔭 := by
      have h1 : algebraMap ℤ (𝓞 F) ((q : ℤ)) ∈ 𝔭 :=
        (Ideal.mem_of_liesOver (P := 𝔭) (p := pZ) ((q : ℤ))).mp
          (Ideal.subset_span (Set.mem_singleton (q : ℤ)))
      simpa using h1
    -- `e(𝔭/q) = f(𝔭/q) = 1` and `e(P/𝔭) = f(P/𝔭) = 1`
    have hF𝔭 := hF.2 ⟨𝔭, h𝔭p, h𝔭L⟩
    have hrel𝔭 := hrel 𝔭 h𝔭p hqmem
    have hP𝔭 : P.1.LiesOver 𝔭 := Ideal.over_under P.1
    have hPe : P.1.ramificationIdx (𝓞 F) = 1 := (hrel𝔭.2 ⟨P.1, hPp, hP𝔭⟩).1
    have hPf : P.1.inertiaDeg (𝓞 F) = 1 := (hrel𝔭.2 ⟨P.1, hPp, hP𝔭⟩).2
    refine ⟨?_, ?_⟩
    · rw [Ideal.ramificationIdx_tower (q := 𝔭) (r := P.1), hF𝔭.1, hPe, one_mul]
    · rw [Ideal.inertiaDeg_tower (q := 𝔭) (r := P.1), hF𝔭.2, hPf, one_mul]
  -- The fundamental identity reads `∑_{P | q} e f = [L : ℚ]`, and each summand is `1`.
  have hsum : ∑ P : pZ.primesOver (𝓞 L), P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ
      = Fintype.card (pZ.primesOver (𝓞 L)) := by
    have h1 : ∀ P : pZ.primesOver (𝓞 L), P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ = 1 :=
      fun P => by rw [(hef P).1, (hef P).2, one_mul]
    rw [Finset.sum_congr rfl (fun P _ => h1 P), Finset.sum_const, Finset.card_univ]
    simp
  have hcard : Nat.card (pZ.primesOver (𝓞 L)) = Module.finrank ℚ L := by
    rw [Nat.card_eq_fintype_card, ← hsum,
      Ideal.sum_ramification_inertia_eq_finrank (p := pZ) (S := 𝓞 L)]
    exact (IsFractionRing.finrank_eq ℤ ℚ (𝓞 L) L).symm
  exact ⟨hcard, hef⟩

end Work.Tower.Unramified
