import Mathlib
import Submission.Work.Tower.Defs

/-!
# A prime that has `[L' : F]` primes above it with residue degree one splits completely

This is a supporting lemma for the Frattini-layer step of the tower construction
(Section 3 of the paper): if a prime `𝔭` of `𝓞 F` has at least `[L' : F]` distinct
primes of `𝓞 L'` above it, all of residue degree one, then `𝔭` splits completely in
`L'/F`.

The content is the fundamental identity `∑ e(q) * f(q) = [L' : F]`, valid for any
prime `𝔭` of `𝓞 F` (it is not needed that `𝔭` be maximal or nonzero: the sum runs
over the primes of `𝓞 L'` lying over `𝔭`).  Each term is positive, so there are at
most `[L' : F]` primes above `𝔭`; combined with the hypothesis that there are at
least `[L' : F]` gives that the elements of `s` are exactly *all* the primes above
`𝔭`, and there are `[L' : F]` of them.
-/

set_option linter.style.haveILetI false

namespace Work.Tower.FrattiniLayer

open NumberField

theorem splitsCompletelyIn_of_finset {F L' : Type*} [Field F] [NumberField F] [Field L']
    [NumberField L'] [Algebra F L'] [FiniteDimensional F L']
    (𝔭 : Ideal (NumberField.RingOfIntegers F)) (s : Finset (Ideal (NumberField.RingOfIntegers L')))
    (hs : ∀ P ∈ s, P.IsPrime ∧ P.LiesOver 𝔭 ∧
      Nonempty ((NumberField.RingOfIntegers L') ⧸ P ≃+* (NumberField.RingOfIntegers F) ⧸ 𝔭))
    (hcard : Module.finrank F L' ≤ s.card) :
    Work.Tower.SplitsCompletelyIn F L' 𝔭 := by
  classical
  -- `L'` is nontrivial over `F`, and `s` is nonempty by the cardinality hypothesis.
  have hpos : 0 < Module.finrank F L' := Module.finrank_pos
  have hne : s.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hpos hcard)
  obtain ⟨P₀, hP₀⟩ := hne
  -- Since some prime of `𝓞 L'` lies over `𝔭`, the ideal `𝔭` is prime.
  have hp : 𝔭.IsPrime := by
    haveI : P₀.IsPrime := (hs P₀ hP₀).1
    haveI : P₀.LiesOver 𝔭 := (hs P₀ hP₀).2.1
    rw [Ideal.over_def P₀ 𝔭, Ideal.under_def]
    exact Ideal.comap_isPrime
      (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L')) P₀
  -- Number of primes above `𝔭` is at most `[L' : F]`, by the fundamental identity.
  have hle : s.card ≤ Module.finrank F L' := by
    haveI : Fintype (𝔭.primesOver (NumberField.RingOfIntegers L')) :=
      (Algebra.QuasiFinite.finite_primesOver 𝔭).fintype
    have hsum : ∑ q : 𝔭.primesOver (NumberField.RingOfIntegers L'),
        q.1.ramificationIdx (NumberField.RingOfIntegers F) *
        q.1.inertiaDeg (NumberField.RingOfIntegers F) =
        Module.finrank F L' := by
      haveI : 𝔭.IsPrime := hp
      rw [Ideal.sum_ramification_inertia_eq_finrank 𝔭 (NumberField.RingOfIntegers L')]
      exact (IsFractionRing.finrank_eq (NumberField.RingOfIntegers F) F
        (NumberField.RingOfIntegers L') L').symm
    rw [← hsum]
    -- `s` injects into the primes above `𝔭`.
    have hle_card : s.card ≤ Fintype.card (𝔭.primesOver (NumberField.RingOfIntegers L')) := by
      rw [← Fintype.card_coe s]
      refine Fintype.card_le_of_injective
        (fun x : ↥s =>
          (⟨x.1, (hs x.1 x.2).1, (hs x.1 x.2).2.1⟩ :
            𝔭.primesOver (NumberField.RingOfIntegers L'))) ?_
      intro a b hab
      exact Subtype.ext
        (congrArg (fun x : 𝔭.primesOver (NumberField.RingOfIntegers L') => x.1) hab)
    refine le_trans hle_card ?_
    -- Each summand `e(q) * f(q)` is positive, so the number of summands is at most the sum.
    rw [← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun q _ => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos q.1 (NumberField.RingOfIntegers F)).ne'
      (Ideal.inertiaDeg_pos q.1 (NumberField.RingOfIntegers F)).ne'))
  have hfin : Module.finrank F L' = s.card := le_antisymm hcard hle
  -- The elements of `s`, indexed by `Fin [L' : F]`, are the required primes.
  refine ⟨fun i => ((s.equivFin.symm (Fin.cast hfin i) : ↥s) : Ideal (NumberField.RingOfIntegers L')),
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hs _ (s.equivFin.symm (Fin.cast hfin i)).2).1
  · intro i
    exact (hs _ (s.equivFin.symm (Fin.cast hfin i)).2).2.1
  · intro i j hij
    exact Fin.cast_injective hfin (s.equivFin.symm.injective (Subtype.val_injective hij))
  · intro i
    exact (hs _ (s.equivFin.symm (Fin.cast hfin i)).2).2.2

end Work.Tower.FrattiniLayer
