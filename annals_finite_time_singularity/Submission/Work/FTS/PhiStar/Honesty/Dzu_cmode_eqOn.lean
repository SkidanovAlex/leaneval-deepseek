import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.smoothCptQ_hkMem
import Submission.Work.FTS.ClassCHon.Zpz.cmode_Dz
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.DzIterCpt.DzIter_contDiff_of_forall
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.cmode_hasDerivAt_pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The mode coefficient commutes with the factor of `z`**: for a source `H` the
coefficient of `D_z H = z ∂_z H` is the coefficient of `∂_z H` multiplied by `z`.

This is the purely `θ`-integrated statement `pwF m H z = numW m (∂_z H) z` (for which
`Zpz/Defs.lean` shows the two sides are literally the same term) combined with the identity
`cmode m G z = numW m G z / D_m` of `Zpz/Basic.lean`. -/
theorem cmode_Dz_eq (j : ℕ) (H : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.cmode j (Work.Spaces.Dz H) z
      = z * Work.FTS.PhiStar.Series.cmode j (Work.Spaces.pz H) z := by
  have hpw : Work.FTS.ClassCHon.Zpz.pwF j H z
      = Work.FTS.ClassCHon.Zpz.numW j (Work.Spaces.pz H) z := rfl
  rw [Work.FTS.ClassCHon.Zpz.cmode_eq_numW_div j (Work.Spaces.Dz H) z,
    Work.FTS.ClassCHon.Zpz.cmode_eq_numW_div j (Work.Spaces.pz H) z,
    Work.FTS.ClassCHon.Zpz.numW_Dz j H z, hpw]
  ring

theorem Dzu_cmode_eqOn {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) (t j : ℕ) :
    Set.EqOn (Work.FTS.EllExist.Honesty.Dzu t (Work.FTS.PhiStar.Series.cmode j G))
      (fun z => Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter t G) z) (Set.Ioi 0) := by
  -- every `D_z`-iterate of a jointly `C^∞` source is jointly `C^∞`
  have hsm : ∀ k : ℕ, ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.DzIter k G)) :=
    fun k => Work.FTS.PhiStar.Honesty.DzIterCpt.DzIter_contDiff_of_forall hG.smooth k
  -- the induction on the number of `z∂_z` applications
  have key : ∀ t : ℕ, ∀ z : ℝ, 0 < z →
      Work.FTS.EllExist.Honesty.Dzu t (Work.FTS.PhiStar.Series.cmode j G) z
        = Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter t G) z := by
    intro t
    induction t with
    | zero => intro z _; rfl
    | succ t ih =>
        intro z hz
        -- the two sides agree on a neighbourhood of `z`, so the derivatives agree there
        have heq : Work.FTS.EllExist.Honesty.Dzu t (Work.FTS.PhiStar.Series.cmode j G)
            =ᶠ[𝓝 z] fun s => Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter t G) s := by
          filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
          exact ih s hs
        have hder : deriv (Work.FTS.EllExist.Honesty.Dzu t
              (Work.FTS.PhiStar.Series.cmode j G)) z
            = Work.FTS.PhiStar.Series.cmode j (Work.Spaces.pz (Work.Spaces.DzIter t G)) z := by
          rw [heq.deriv_eq]
          exact (Work.FTS.PhiStar.Honesty.CptQSmooth.cmode_hasDerivAt_pz (hsm t) j z).deriv
        show z * deriv (Work.FTS.EllExist.Honesty.Dzu t
              (Work.FTS.PhiStar.Series.cmode j G)) z
          = Work.FTS.PhiStar.Series.cmode j (Work.Spaces.DzIter (t + 1) G) z
        rw [hder,
          show Work.Spaces.DzIter (t + 1) G = Work.Spaces.Dz (Work.Spaces.DzIter t G) from rfl]
        exact (cmode_Dz_eq j (Work.Spaces.DzIter t G) z).symm
  exact fun z hz => key t z hz

end Work.FTS.PhiStar.Honesty
