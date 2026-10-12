import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairGCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowDirChi` — the **weighted** Dirichlet content of a state

`FINDING_PotPairRows_exists.md` §SESSION 11 records an obstruction of the route as designed: the
statement `pairEnergy` of `L1Tails` is **`χ_ℓ`-weighted in its first variable**

    pairEnergy ℓ G = ∫_{box}∫_{box} ( Σ_j ‖∂_j(χ_ℓ(w)·G w y)‖² + ℓ⁻²‖χ_ℓ(w)·G w y‖² ),

so it vanishes on fibres supported where `χ_ℓ = 0` (the *corners* of the box cube), whereas the
bound `pairG_dir_leB` routes it through the **unweighted** state content `pinDir`.  The hypotheses
of `PotPairRows` do *not* bound `pinDir`: a state concentrated in a corner of the cube (where
`wLoc = 0` and `fsT`'s windowed words vanish) satisfies `IsLowB` with `pinDir/normB ≍ 1/δ² → ∞`.

The fix is the **weighted** content `pinDirChi` below — the Dirichlet energy of the state weighted
by `χ_ℓ(x_i)² ≍` FS's localisation window, which *is* controlled by the kinetic form
(`mainWord = (1-εT)bsOneBody ℓ (fsKinCoeff c₁) u + …` and `bsOneBody ℓ (·²) u = ∫Σ(∂(bsWin·bsQ ψ))²`).
Everything here is a definition.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **The `χ_ℓ`-weighted Dirichlet content of an `n`-body state**: the sum over the slots `i` and
the coordinate directions `j` of `∫_{abox}χ_ℓ(x_i)²·‖∂_{i,j}Θ‖²`.  At the honest pin
`Θ = boxRestrictC ℓ Φ`, `pinDirChi ℓ Φ ≤ pinDir ℓ Φ` (since `0 ≤ χ_ℓ ≤ 1`), and it is the quantity
that the weighted `pairEnergy` of the row's fibres is bounded by. -/
noncomputable def pinDirChi {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, ∑ i : Fin n, ∑ j : Fin 3,
    (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 * ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2

/-- `pinDirChi` is nonnegative. -/
theorem pinDirChi_nonneg {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) : 0 ≤ pinDirChi ℓ Θ :=
  integral_nonneg fun x => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (sq_nonneg _) (by positivity)

end Work.BoseBoxFock
