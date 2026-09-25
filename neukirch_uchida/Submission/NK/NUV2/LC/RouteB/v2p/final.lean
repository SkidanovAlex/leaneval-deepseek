import Mathlib
import Submission.NK.NUV2.LC.RouteB.v2.assembly
import Submission.NK.NUV2.LC.RouteB.v2.locL_unitsLevelMap_fibre
import Submission.NK.NUV2.LC.RouteB.locL_kummerLevel_of_locLevel_eq_zero
import Submission.NK.NUV2.LC.RouteB.v2p.propagation

/-!
# The Hasse principle at an open level in the `μ_p` vocabulary (fibre world assembly)

This module assembles the `μ_p`-form `NK.NUV2.LC.RouteB.v2p.muLevel_dies_of_loc_eq_zero` of the
Hasse principle at an open level from the (proved) pieces

* `NK.NUV2.LC.RouteB.v2p.locL_unitsLevelMap_eq_zero` — the propagation under inflation;
* `NK.NUV2.LC.RouteB.v2.locL_unitsLevelMap_fibre` — the independence of the localisation on the
  places above a common place;
* `NK.NUV2.LC.RouteB.locL_kummerLevel_of_locLevel_eq_zero` — the fine/local dictionary,

via the general assembly `NK.NUV2.LC.RouteB.v2.muLevel_dies_of_loc_eq_zero_assembly`.

All the pieces live in the *fibre* world (`locUnits_tower_fibre` / `RouteBDeps`), so they can be
imported together; the propagation is a renamed copy in `v2p/propagation.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open CategoryTheory

namespace NK.NUV2.LC.RouteB.v2p

/-- **The `μ_p`-form of the Hasse principle at an open level**, assembled from the propagation, the
fibre and the dictionary. -/
theorem muLevel_dies_of_loc_eq_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (L : FiniteGaloisIntermediateField K K')
    (c : NK.HassePrinciple.MuLevelH2 (K := K) (K' := K') p V L)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L
          (NK.NUV2.ABHN.levelCompare p V L c)) A = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      NK.HassePrinciple.muLevelMap (K := K) (K' := K') p V
        ((FiniteGaloisIntermediateField.le_iff L M).mp hLM) c = 0 :=
  NK.NUV2.LC.RouteB.v2.muLevel_dies_of_loc_eq_zero_assembly p hp hp2 ζ hζ V hV
    { prop := fun L M hLM hF b {w} {w'} hw hb =>
        NK.NUV2.LC.RouteB.v2p.locL_unitsLevelMap_eq_zero V L M hLM hF b hw hb
      fib := fun L M hLM hF b {w} {w₁} {w₂} h₁ h₂ =>
        NK.NUV2.LC.RouteB.v2.locL_unitsLevelMap_fibre V L M hLM hF b h₁ h₂
      dict := fun L hF c A q hA h =>
        NK.NUV2.LC.RouteB.locL_kummerLevel_of_locLevel_eq_zero p V L hF c A q hA h }
    L c h

end NK.NUV2.LC.RouteB.v2p
