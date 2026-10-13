import Submission.Work.DSMap.Gaps
import Submission.Work.DSROOTS.Main
import Submission.Work.DSFinal.M2

/-! # DSFinal.Roots — LEAD-OWNED final wiring (curric-46, 10-14)

`area_ROOTS` rebased on the single-polynomial André lemma `DSMap.Gaps.area_M2pos1` (via
`m2pos1_any` on `X - C s`, natDegree 1) instead of the FALSE `DSMap.Mix.area_M2'`.
The iteration is DSROOTS's clean `DSMap.Mix2.area_ROOTS_of_andreStep`. -/

set_option linter.style.haveILetI false

namespace Work.DSFinal

open DSMap

universe a

/-- André's one-element step from `Gaps.m2pos1_any` applied to `X - C s`. -/
theorem andreStep_final (p : ℕ) [Fact p.Prime] : Work.DSROOTS.AndreStep.{a} p := by
  intro W _ Q s
  obtain ⟨B, _, _, Q', hϖ, hFF, r, hr0, hr⟩ := Work.DSFinal.m2pos1_any_final p W Q
    (Polynomial.X - Polynomial.C s) (Polynomial.monic_X_sub_C s)
    (fun h => by haveI := h; rw [Polynomial.natDegree_X_sub_C]; exact Nat.one_pos)
  refine ⟨B, _, algebraMap W B, Q', hϖ, (Work.DSROOTS.FFp.iff p).mpr hFF, r, ?_, hr⟩
  simp only [Polynomial.aeval_X, Polynomial.aeval_C, map_sub, sub_eq_zero] at hr0
  rw [hr0]

/-- **ROOTS**, with the frozen statement of `DSMap.Mix2.area_ROOTS`, citing only `area_M2pos1`. -/
theorem area_ROOTS_final (p : ℕ) [Fact p.Prime] (W : Type a) [CommRing W] (Q : PerfectoidData p W)
    {ι : Type a} [Finite ι] (t : ι → W) :
    ∃ (W' : Type a) (_ : CommRing W') (_ : Algebra W W') (Q' : PerfectoidData p W'),
      (∀ k, Q'.ϖ k = algebraMap W W' (Q.ϖ k)) ∧
      Module.FaithfullyFlat (W ⧸ Ideal.span {(p : W)})
        (W' ⧸ (Ideal.span {(p : W)}).map (algebraMap W W')) ∧
      ∃ tr : ι → ℕ → W', (∀ i, tr i 0 = algebraMap W W' (t i)) ∧
        ∀ i k, tr i (k + 1) ^ p = tr i k :=
  DSMap.Mix2.area_ROOTS_of_andreStep p (andreStep_final p) W Q t

example : @area_ROOTS_final.{a} = @DSMap.Mix2.area_ROOTS.{a} := rfl

end Work.DSFinal
