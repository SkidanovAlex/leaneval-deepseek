import Submission.Work.DSROOTS.Basic
import Submission.Work.DSROOTS.RootExt
import Submission.Work.DSROOTS.AndreStepOfM2

/-!
# DSROOTS: the `ROOTS` node of the MIX2 route, delivered

`DSMap.Mix2.area_ROOTS_proved` has exactly the type of the frozen node `DSMap.Mix2.area_ROOTS`
(checked below by `rfl`): the `p`-power roots of all elements `t i` of a finite index type, after
a perfectoid extension with the same `ϖ`-tower which is faithfully flat modulo `p`.

The proof is `Work.DSROOTS.exists_roots_of_andreStep` (the iterated construction,
`Submission/Work/DSROOTS/RootExt.lean`) applied to the one-step André lemma
`Work.DSROOTS.andreStep_of_M2` (`Submission/Work/DSROOTS/andreStep_of_M2.lean`, from
`DSMap.Mix.area_M2'`), plus the bridge `Work.DSROOTS.FFp.iff` back to the
`Module.FaithfullyFlat`-on-quotients form of the frozen statement.

The conditional form `area_ROOTS_of_andreStep` isolates the single external input: it is
`DSMap.Mix.area_M2'` and nothing else.  It is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only), so the iteration and the bridge below add no
axioms; the `sorryAx` in `area_ROOTS_proved` is exactly the leaf `area_M2'` of the lead's file,
as prescribed by the MIX2 design ("M2′ as hypothesis").
-/

set_option linter.style.haveILetI false

namespace DSMap.Mix2

open DSMap DSMap.Mix Work.DSROOTS

universe a

/-- The `ROOTS` statement in the frozen `Module.FaithfullyFlat` form, from the one-step André
hypothesis. -/
theorem area_ROOTS_of_andreStep (p : ℕ) (h : Work.DSROOTS.AndreStep.{a} p) (W : Type a)
    [CommRing W] (Q : PerfectoidData p W) {ι : Type a} [Finite ι] (t : ι → W) :
    ∃ (W' : Type a) (_ : CommRing W') (_ : Algebra W W') (Q' : PerfectoidData p W'),
      (∀ k, Q'.ϖ k = algebraMap W W' (Q.ϖ k)) ∧
      Module.FaithfullyFlat (W ⧸ Ideal.span {(p : W)})
        (W' ⧸ (Ideal.span {(p : W)}).map (algebraMap W W')) ∧
      ∃ tr : ι → ℕ → W', (∀ i, tr i 0 = algebraMap W W' (t i)) ∧
        ∀ i k, tr i (k + 1) ^ p = tr i k := by
  obtain ⟨W', hCR, f, Q', hϖ, hff, tr, htr⟩ := Work.DSROOTS.exists_roots_of_andreStep h W Q t
  letI : CommRing W' := hCR
  letI : Algebra W W' := f.toAlgebra
  refine ⟨W', hCR, f.toAlgebra, Q', ?_, ?_, tr, ?_, ?_⟩
  · intro k
    rw [hϖ k]
    rfl
  · exact (Work.DSROOTS.FFp.iff (R := W) (S := W') p).mp hff
  · intro i
    exact (htr i).1
  · intro i k
    exact (htr i).2 k

/-- **The delivered `ROOTS` node**: compatible `p`-power roots of finitely many elements of a
perfectoid ring, after a perfectoid extension with the same `ϖ`-tower which is faithfully flat
modulo `p`.  (André's lemma `DSMap.Mix.area_M2'` is applied once per element.) -/
theorem area_ROOTS_proved (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W] (Q : PerfectoidData p W)
    {ι : Type a} [Finite ι] (t : ι → W) :
    ∃ (W' : Type a) (_ : CommRing W') (_ : Algebra W W') (Q' : PerfectoidData p W'),
      (∀ k, Q'.ϖ k = algebraMap W W' (Q.ϖ k)) ∧
      Module.FaithfullyFlat (W ⧸ Ideal.span {(p : W)})
        (W' ⧸ (Ideal.span {(p : W)}).map (algebraMap W W')) ∧
      ∃ tr : ι → ℕ → W', (∀ i, tr i 0 = algebraMap W W' (t i)) ∧
        ∀ i k, tr i (k + 1) ^ p = tr i k :=
  area_ROOTS_of_andreStep p (Work.DSROOTS.andreStep_of_M2' p) W Q t

end DSMap.Mix2

/-- the delivered node has exactly the type of the frozen `area_ROOTS` -/
example : @DSMap.Mix2.area_ROOTS_proved = @DSMap.Mix2.area_ROOTS := rfl
