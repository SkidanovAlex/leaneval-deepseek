import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Gen.summand_le_easy
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowMulAsm
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulExpansion
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulTermSmall
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.mulTermLarge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The level-six `A · f` coefficient row.**  The slot pairing of the product `A · f` against
the datum `f` is bounded by `C·α^{-3}` times the two `L²`-prices of the coefficient `A`
(`K0`, `K4`) against the `ℋ⁶`-energy of `f`, plus the `ℋ⁶`-price `K6` against the
`a`-priori bound `M` of `Xn α f`.

Assembled in `rowMulAsm` from the Leibniz expansion `mulExpansion` and the two per-summand
bounds `mulTermSmall` (`a₁ + b₁ ≤ 2`) and `mulTermLarge` (`3 ≤ a₁ + b₁`). -/
theorem rowMulCoef : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * f z θ) f|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
  rowMulAsm mulExpansion mulTermSmall mulTermLarge

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
