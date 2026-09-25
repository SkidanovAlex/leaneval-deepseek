import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.NUV2.LC.RouteB.muLift
import Submission.NK.NUV2.LC.RouteB.kummerMap_locUnits
import Submission.NK.NUV2.LC.units_finite_support
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.NUV2.ABHN.h2Twist_muColim_equiv
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.NUV2.LC.RouteB.v2p.final

/-!
# Route B, the `brauerTwist` form of the Hasse principle at an open level

This file proves `NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero_v2` by reducing it to the `μ_p`
form `NK.NUV2.LC.RouteB.v2p.muLevel_dies_of_loc_eq_zero` (proved in the *fibre* world, assembled
from the propagation, the fibre lemma and the local dictionary), via the equivalence
`NK.NUV2.LC.RouteB.level_kills_of_muLevel` of `level_kills_aux.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace NK.NUV2.LC.RouteB

/-- Route B, the `brauerTwist` form of the Hasse principle at an open level; equivalent to
`NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero` via `NK.NUV2.ABHN.levelCompare`.

NOTE for the prover: the auxiliary fibre statement (two places of `M` over the same place of `L`
have simultaneously vanishing `locUnits` of the tower image) is in
`Submission/Work/NUV2/LC/RouteB/locUnits_tower_fibre.lean` as
`NK.NUV2.LC.RouteB.locUnits_tower_fibre`, but that module **cannot be imported together with
`locUnits_tower_eq_zero`** (both define `NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits`).
Reprove the fibre statement (or a private copy of it) inside this file, or reorganise.
Suggested route: enlarge `L` so that `Gal(K'/L) ≤ V`; `b := (unitsLift V M) ((kummerLevel p V M) c)`
with `c := (NK.NUV2.ABHN.levelCompare p V M).symm a`; finite support `units_finite_support`; for
the finitely many bad places the hypothesis plus `NK.HasseTwist.loc_ofLevel_eq_zero_iff` gives a
killing level (via `kummerMap_locUnits` and the compatibility of the Kummer map with `unitsLift` /
`muLift`); take the finite sup of levels, apply
`NK.GlobalCFTdeep.hbnUnits ↥(levelBase V M) ↥M`, and convert back with
`NK.HassePrinciple.kummerColim_injective` / `kummerLevel_kernel_dies`. -/
theorem level_kills_of_loc_eq_zero_v2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.BrauerTwist.LevelH2 (K := K) (K' := K') p V L)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L a) A = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      NK.BrauerTwist.levelMap p V hLM a = 0 := by
  exact NK.NUV2.LC.RouteB.level_kills_of_muLevel p hp hp2 ζ hζ V hV
    (fun L c h =>
      NK.NUV2.LC.RouteB.v2p.muLevel_dies_of_loc_eq_zero p hp hp2 ζ hζ V hV L c h)
    L a h


end NK.NUV2.LC.RouteB
