import Mathlib
import Submission.NK.NUV2.ARL.localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Unramified local units are norms (in the `localNormSubgroup` vocabulary)

`NK.NUV2.ARL.localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one` states that at a prime
`q | Q` with ramification index `1` every local unit of `K_Q` is the norm of a local unit of `L_q`.
Here this is rewritten as a statement about the local norm *subgroup*
`NK.CFTLib.IdeleHasse.localNormSubgroup K L (ofFinite Q)` (the subgroup used by the one-place
faithfulness `ZDataMup.oddArtin_onePlace` of the idèlic Artin map), i.e.

  `localUnits K (ofFinite Q) ≤ localNormSubgroup K L (ofFinite Q)`.

This is the local ingredient of the p. 16 computation: at every finite place outside `Σ` the level
`↥K(√X)` of the diagonal computation is unramified, so every local unit (and every even power of a
uniformiser) is a norm, whence the corresponding local factor `oTheta X (σz) v` is `1` by
`ZConstruction.oTheta_eq_one_iff_localNorm`.
-/

namespace Work.SSGRoute.ZConstruction

set_option maxHeartbeats 800000

/-- **Unramified local units are norms.** -/
theorem localUnits_le_localNormSubgroup_of_ramificationIdx_eq_one {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite Q) := by
  intro a ha
  obtain ⟨u, _hu, hnorm⟩ :=
    NK.NUV2.ARL.localUnits_le_imageLocalNormFinite_of_ramificationIdx_eq_one Q q hq hunr a ha
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
  exact Subgroup.mem_iSup_of_mem ⟨q, hq⟩ (MonoidHom.mem_range.mpr ⟨u, hnorm⟩)

end Work.SSGRoute.ZConstruction
