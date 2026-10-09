import Mathlib
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.GlobalCFT.Norm.NormTransAux
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bookkeeping for places in a tower

Transitivity of `NK.GlobalCFT.Place.LiesOver` in a tower `K ⊆ L ⊆ M`, and the resulting
computation of the place of `K` below a place of `M` through the intermediate field `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NK.GlobalCFT

namespace NK.NUV2.ChebAux.Transfer

variable {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- **Transitivity of `Place.LiesOver` in a tower.** -/
theorem place_liesOver_trans {v : NK.GlobalCFT.Place K} {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h1 : NK.GlobalCFT.Place.LiesOver w' w)
    (h2 : NK.GlobalCFT.Place.LiesOver w v) : NK.GlobalCFT.Place.LiesOver w' v := by
  rcases NK.GlobalCFT.Place.liesOver_iff w' w |>.mp h1 with
    ⟨w1, w2, hw'eq, hweq, hww⟩ | ⟨q, Q, hw'eq, hweq, hq⟩
  · rcases NK.GlobalCFT.Place.liesOver_iff w v |>.mp h2 with
      ⟨w2', v', hweq2, hveq, hwv⟩ | ⟨Q', Q2, hweq2, hveq, hQ⟩
    · have hw2eq : w2 = w2' :=
        NK.GlobalCFT.Place.ofInfinite_inj.mp (hweq.symm.trans hweq2)
      rw [hw'eq, hveq]
      exact NK.GlobalCFT.Place.liesOver_ofInfinite
        (Norm.liesOver_trans hww (hw2eq.symm ▸ hwv))
    · exact absurd (hweq.symm.trans hweq2) (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w2 Q')
  · rcases NK.GlobalCFT.Place.liesOver_iff w v |>.mp h2 with
      ⟨w2', v', hweq2, hveq, hwv⟩ | ⟨Q', Q2, hweq2, hveq, hQ⟩
    · exact absurd (hweq.symm.trans hweq2).symm
        (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w2' Q)
    · have hQeq : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp (hweq.symm.trans hweq2)
      have hq' : q.asIdeal.LiesOver Q'.asIdeal := hQeq ▸ hq
      haveI := hq'
      haveI := hQ
      rw [hw'eq, hveq]
      exact NK.GlobalCFT.Place.liesOver_ofFinite
        (Ideal.LiesOver.trans q.asIdeal Q'.asIdeal Q2.asIdeal)

/-- **The place of `K` below a place of `M`, computed through the intermediate field `L`.** -/
theorem placeUnder_eq_placeUnder {v : NK.GlobalCFT.Place K} {w : NK.GlobalCFT.Place L}
    {w' : NK.GlobalCFT.Place M} (h1 : NK.GlobalCFT.Place.LiesOver w' w)
    (h2 : NK.GlobalCFT.Place.LiesOver w v) :
    NK.GlobalCFT.Norm.globalCFT_placeUnder (K := K) (L := M) w' = v :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
    (NK.GlobalCFT.Norm.liesOver_globalCFT_placeUnder w') (place_liesOver_trans h1 h2)

end NK.NUV2.ChebAux.Transfer
