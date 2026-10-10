import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.eb_loc_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open CategoryTheory NumberField

/-- **Local degree of the place of `L` below `ŵ`.**  For a finite Galois extension `L/k` of number
fields and a finite place `r` of `L` lying over the finite place `v₀` of `k`, the stabiliser
`Stab_{Gal(L/k)}(r)` has cardinality the local degree `[L_r : k_{v₀}] = e(r|v₀)·f(r|v₀)`.

Proof: `Work.SSGRoute.eb_stab_card_aux k k L r v₀ h` identifies the cardinality with
`Module.finrank (v₀.adicCompletion k) (r.adicCompletion L)`, and
`Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg v₀ r h`
identifies that finrank with `ramificationIdx * inertiaDeg` (note the `.symm`). -/
theorem eb_crux_ncard_eq_ef (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : r.asIdeal.LiesOver v₀.asIdeal) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite r)) =
      r.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
        r.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
  rw [eb_stab_card_aux k k L r v₀ h]
  exact (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    (K := k) (L := L) v₀ r h).symm

end Work.SSGRoute
