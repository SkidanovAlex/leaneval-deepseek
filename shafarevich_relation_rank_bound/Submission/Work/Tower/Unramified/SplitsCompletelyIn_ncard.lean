import Mathlib
import Submission.Work.Tower.Unramified.Basic

namespace Work.Tower.Unramified

open NumberField

/-- **A completely split prime has exactly `[L : F]` primes over it.**

The definition `Work.Tower.SplitsCompletelyIn F L 𝔭` of "`𝔭` splits completely in `L/F`" lists
`[L : F]` pairwise distinct primes of `𝓞 L` lying over `𝔭`.  The fundamental identity
`∑_{𝔔 | 𝔭} e(𝔔) f(𝔔) = [L : F]` of ramification theory says that the total number of primes
lying over `𝔭` (counted with the ramification index and inertia degree) is `[L : F]`; since each
prime over `𝔭` contributes at least `1`, the listing is exhaustive and the set of primes over
`𝔭` has cardinality exactly `[L : F]`. -/
theorem SplitsCompletelyIn_ncard {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h : Work.Tower.SplitsCompletelyIn F L 𝔭) :
    (𝔭.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank F L := by
  classical
  obtain ⟨𝔔, hprime, hlies, hinj, _hres⟩ := h
  have hn : 0 < Module.finrank F L := Module.finrank_pos
  by_cases hbot : 𝔭 = ⊥
  · -- `𝔭 = ⊥`: the hypothesis already forces `[L : F] = 1`, and `⊥` is the only prime over `⊥`.
    have hfeq : Module.finrank F L = 1 := by
      have hsub : Subsingleton (Fin (Module.finrank F L)) :=
        ⟨fun i j => hinj (by
          have hi : 𝔔 i ∈ (⊥ : Ideal (𝓞 F)).primesOver (𝓞 L) := by
            rw [← hbot]; exact ⟨hprime i, hlies i⟩
          have hj : 𝔔 j ∈ (⊥ : Ideal (𝓞 F)).primesOver (𝓞 L) := by
            rw [← hbot]; exact ⟨hprime j, hlies j⟩
          rw [Ideal.primesOver_bot] at hi hj
          rw [Set.mem_singleton_iff] at hi hj
          rw [hi, hj])⟩
      have h1 : Module.finrank F L ≤ 1 := by
        have := Fintype.card_le_one_iff_subsingleton.mpr hsub
        simpa using this
      omega
    rw [hbot, hfeq, Ideal.primesOver_bot, Set.ncard_singleton]
  · -- `𝔭 ≠ ⊥`: `𝔭` is maximal, so the fundamental identity applies.
    haveI : 𝔭.IsPrime := Ideal.isPrime_of_liesOver (𝔔 ⟨0, hn⟩) 𝔭
    haveI : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal ‹𝔭.IsPrime› hbot
    have hfr : Module.finrank F L = Module.finrank (𝓞 F) (𝓞 L) :=
      IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L
    have hsum : ∑ q : 𝔭.primesOver (𝓞 L),
        q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = Module.finrank F L := by
      rw [Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) 𝔭 (𝓞 L), ← hfr]
    have hone : (∑ _q : 𝔭.primesOver (𝓞 L), (1 : ℕ)) = Fintype.card (𝔭.primesOver (𝓞 L)) := by
      simp
    -- Upper bound: every prime over `𝔭` contributes at least `1` to the fundamental identity.
    have hcard_le : Fintype.card (𝔭.primesOver (𝓞 L)) ≤ Module.finrank F L := by
      rw [← hsum, ← hone]
      refine Finset.sum_le_sum fun q _ => ?_
      have h1 : 0 < q.1.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos q.1 (𝓞 F)
      have h2 : 0 < q.1.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos q.1 (𝓞 F)
      have : 0 < q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) := Nat.mul_pos h1 h2
      omega
    -- Lower bound: the `[L : F]` primes supplied by the hypothesis are distinct.
    have hφ : Function.Injective (fun i : Fin (Module.finrank F L) =>
        (⟨𝔔 i, ⟨hprime i, hlies i⟩⟩ : 𝔭.primesOver (𝓞 L))) := by
      intro i j hij
      exact hinj (Subtype.ext_iff.mp hij)
    have hle_card : Module.finrank F L ≤ Fintype.card (𝔭.primesOver (𝓞 L)) := by
      simpa using Fintype.card_le_of_injective _ hφ
    have hcard : Fintype.card (𝔭.primesOver (𝓞 L)) = Module.finrank F L :=
      le_antisymm hcard_le hle_card
    rw [← Set.fintypeCard_eq_ncard (𝔭.primesOver (𝓞 L)), hcard]

end Work.Tower.Unramified
