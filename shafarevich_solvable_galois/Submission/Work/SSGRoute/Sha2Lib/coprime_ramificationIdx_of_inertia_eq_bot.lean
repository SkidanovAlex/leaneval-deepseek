import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.ramificationIdx_of_inertia_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coprimality of the ramification index from vanishing inertia (the `ramificationIdx'` form)

`Work.SSGRoute.Sha2Lib.ramificationIdx_eq_one_of_inertia_eq_bot` gives
`q'.ramificationIdx (𝓞 K) = 1` from `Ideal.inertia (↥L ≃ₐ[K] ↥L) q'.asIdeal = ⊥`.  The consumers —
`Work.SSGRoute.PTdualControl.LevelCocycleDatum` and the `SSGcrux` lane's
`Work.SSGRoute.SSGcrux.concentratedLevelData` — spell the coprimality clause with
`q.asIdeal.ramificationIdx' q'.asIdeal`, so this file records the bridge: the `ramificationIdx'`
form is the `ramificationIdx` form (`Ideal.ramificationIdx'_eq_ramificationIdx`), and `1` is coprime
to everything.

This is the `hcop` conjunct of `concentratedLevelData` (see
`Submission/Work/SSGRoute/PING_sha2image_transport_proved_2026-10-05.md` §12), in exactly the
call-site shape.
-/

open scoped NumberField

namespace Work.SSGRoute.Sha2Lib

/-- **`Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p` from vanishing inertia.** -/
theorem coprime_ramificationIdx'_of_inertia_eq_bot (p : ℕ) {k K L : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [Field L] [NumberField L]
    [Algebra K L] [Algebra k L] [IsScalarTower k K L] [IsGalois K L] [FiniteDimensional K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hlies : q'.asIdeal.LiesOver q.asIdeal)
    (h : Ideal.inertia (L ≃ₐ[K] L) q'.asIdeal = ⊥) :
    Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p := by
  haveI := hlies
  haveI := q.isPrime
  haveI := q'.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := q.asIdeal) (q := q'.asIdeal) q.ne_bot,
    ramificationIdx_eq_one_of_inertia_eq_bot (F := K) (K := L) q.asIdeal q'.asIdeal h]
  exact Nat.coprime_one_left p

end Work.SSGRoute.Sha2Lib
