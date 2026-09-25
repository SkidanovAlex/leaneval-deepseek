import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.NUV2.LC.units_finite_support
import Submission.NK.NUV2.ABHN.h2Twist_muColim_equiv
import Submission.NK.NUV2.LC.LocalLevelSystem
import Submission.NK.HasseTwist.Defs
import Submission.NK.BrauerTwist.levelMap_locLevel_apply
import Submission.NK.NUV2.LC.RouteB.level_kills_of_loc_eq_zero_v2
import Submission.NK.HasseTwist.Obstruction
import Submission.NK.NUV2.LC.RouteB.level_kills_aux

namespace NK.NUV2.LC.RouteB

theorem level_kills_of_loc_eq_zero (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (ζ : K') (hζ : IsPrimitiveRoot ζ p)
    (V : Subgroup Gal(K'/K)) (hV : NK.NUV2.LC.RouteB.IsMuOpen (K := K) (K' := K') ζ V)
    (L : FiniteGaloisIntermediateField K K')
    (a : NK.BrauerTwist.LevelH2 (K := K) (K' := K') p V L)
    (h : ∀ A : NK.BrauerTwist.OverFinitePrime K K',
      NK.BrauerTwist.H2Twist.loc p V
        (NK.BrauerTwist.H2Twist.ofLevel p V L a) A = 0) :
    ∃ (M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M),
      NK.BrauerTwist.levelMap p V hLM a = 0 :=
  -- the same statement is proved (sorry-free) in `level_kills_of_loc_eq_zero_v2` as the
  -- `brauerTwist` form of the `μ_p` fibre statement; this file only records the interface.
  level_kills_of_loc_eq_zero_v2 p hp hp2 ζ hζ V hV L a h

end NK.NUV2.LC.RouteB
