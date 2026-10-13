import Submission.Work.DSROOTS.Basic

/-!
# DSROOTS: André's lemma (`area_M2'`) in root-system form

`Work.DSROOTS.andreStep_of_M2'` is the one-step input of the `ROOTS` node: André's lemma
(`DSMap.Mix.area_M2'`) applied to the monic polynomial `Polynomial.X - Polynomial.C s`, which
produces a compatible system of `p`-power roots of `s`, together with the bridge
`Work.DSROOTS.FFp.iff` from the `Module.FaithfullyFlat`-on-quotients form to the ring-hom form
`FFp`.

This is the only place in the `DSROOTS` area where the frozen leaf `DSMap.Mix.area_M2'` is used.
`Work.DSROOTS.andreStep_of_M2` (`Submission/Work/DSROOTS/andreStep_of_M2.lean`) is an independent
copy of the same argument, delivered in parallel by a colleague from the interface of
`Basic.lean` alone.
-/

set_option linter.style.haveILetI false

namespace Work.DSROOTS

open DSMap DSMap.Mix

universe a

/-- André's lemma (`DSMap.Mix.area_M2'`) in root-system form: applying it to `X - C s` gives a
perfectoid extension, faithful modulo `p`, in which `s` has a compatible system of `p`-power
roots. -/
theorem andreStep_of_M2' (p : ℕ) [Fact p.Prime] : Work.DSROOTS.AndreStep.{a} p := by
  intro W _ Q s
  obtain ⟨W', _, _, Q', hϖ, hFF, hroots⟩ := DSMap.Mix.area_M2' p W Q
  obtain ⟨tr, htr0, htr⟩ := hroots (Polynomial.X - Polynomial.C s) (Polynomial.monic_X_sub_C s)
  refine ⟨W', _, algebraMap W W', Q', hϖ, (Work.DSROOTS.FFp.iff p).mpr hFF, tr, ?_, htr⟩
  simp only [Polynomial.aeval_X, Polynomial.aeval_C, map_sub, sub_eq_zero] at htr0
  rw [htr0]

end Work.DSROOTS
