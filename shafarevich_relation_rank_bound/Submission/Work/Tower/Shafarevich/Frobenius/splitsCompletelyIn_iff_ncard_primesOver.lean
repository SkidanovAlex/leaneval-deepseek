import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent
import Submission.Work.Tower.Unramified.splitsCompletelyIn_bot_iff_finrank
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_NF
import Submission.Work.Tower.Glue.exists_galois_closure_split

namespace Work.Tower.Shafarevich.Frobenius

open NumberField

/-- **Complete splitting is detected by the number of primes above `𝔭`.**

The forward direction is `Work.Tower.Unramified.SplitsCompletelyIn_ncard`.  Conversely, if the
primes of `𝓞 L` above `𝔭` number exactly `[L : F]`, the fundamental identity
`∑_{P | 𝔭} e(P) f(P) = [L : F]` forces each summand to be `1`, so every prime over `𝔭` has
ramification index and inertia degree `1`; this is the normal form
`SplitsCompletelyInNF`, which gives `SplitsCompletelyIn` by
`splitsCompletelyIn_of_NF`.  The degenerate case `𝔭 = ⊥` forces `[L : F] = 1` and is handled
by `splitsCompletelyIn_bot_iff_finrank`.  (The Galois hypothesis is not needed.) -/
theorem splitsCompletelyIn_iff_ncard_primesOver {F L : Type} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (𝔭 : Ideal (NumberField.RingOfIntegers F)) [Fact 𝔭.IsPrime] :
    Work.Tower.SplitsCompletelyIn F L 𝔭 ↔
      (𝔭.primesOver (NumberField.RingOfIntegers L)).ncard = Module.finrank F L := by
  classical
  constructor
  · intro h
    exact Work.Tower.Unramified.SplitsCompletelyIn_ncard h
  · intro hcard
    rcases eq_or_ne 𝔭 ⊥ with hbot | h𝔭
    · -- Degenerate case `𝔭 = ⊥`: the only prime over `⊥` is `⊥`, so the count gives
      -- `[L : F] = 1`, which characterises complete splitting at `⊥`.
      subst hbot
      rw [Ideal.primesOver_bot, Set.ncard_singleton] at hcard
      exact Work.Tower.Unramified.splitsCompletelyIn_bot_iff_finrank.mpr hcard.symm
    · -- Main case: `𝔭` is a nonzero prime, hence maximal, and the fundamental identity applies.
      haveI : 𝔭.IsMaximal := (Fact.out : 𝔭.IsPrime).isMaximal h𝔭
      haveI : Fintype (𝔭.primesOver (𝓞 L)) :=
        (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
      have hsum : ∑ P : 𝔭.primesOver (𝓞 L),
          P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) = Module.finrank F L := by
        rw [Ideal.sum_ramification_inertia_eq_finrank (R := 𝓞 F) 𝔭 (𝓞 L),
          Work.Tower.Unramified.finrank_ringOfIntegers_self]
      have hcarduniv : (Finset.univ : Finset (𝔭.primesOver (𝓞 L))).card =
          Module.finrank F L := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact hcard
      refine Work.Tower.Unramified.splitsCompletelyIn_of_NF (Fact.out : 𝔭.IsPrime) h𝔭
        ⟨?_, fun P => ?_⟩
      · rw [Nat.card_coe_set_eq]
        exact hcard
      · -- Each of the `[L : F]` summands `e(P) f(P) ≥ 1` of the sum `[L : F]` must be `1`.
        have hone : ∀ x ∈ (Finset.univ : Finset (𝔭.primesOver (𝓞 L))),
            1 ≤ x.1.ramificationIdx (𝓞 F) * x.1.inertiaDeg (𝓞 F) := fun x _ =>
          Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Ideal.ramificationIdx_pos x.1 (𝓞 F)).ne'
            (Ideal.inertiaDeg_pos x.1 (𝓞 F)).ne')
        have hsum' : ∑ x ∈ (Finset.univ : Finset (𝔭.primesOver (𝓞 L))),
            x.1.ramificationIdx (𝓞 F) * x.1.inertiaDeg (𝓞 F)
              = (Finset.univ : Finset (𝔭.primesOver (𝓞 L))).card := by
          rw [hcarduniv, ← hsum]
        exact (mul_eq_one_iff_of_one_le
            (Nat.one_le_iff_ne_zero.mpr (Ideal.ramificationIdx_pos P.1 (𝓞 F)).ne')
            (Nat.one_le_iff_ne_zero.mpr (Ideal.inertiaDeg_pos P.1 (𝓞 F)).ne')).mp
          (Work.Tower.Glue.sum_eq_card_imp_eq_one _ _
            hone hsum' P (Finset.mem_univ P))

end Work.Tower.Shafarevich.Frobenius
