import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sliding box on the good set has volume at least `(μ^{-1/3})³`

FS `final_v2.tex` `thm:aprioriHLambda` slides the small boxes
`B(u) = dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` over the *good set*

    G = {u : ∀ j, |((ℓd)•u)_j| ≤ ½ℓ(1+d) − μ^{-1/3}} ,

which is exactly the set of `u` for which every coordinate of `B(u)` is at
least `μ^{-1/3}` long (`Geom.goodSet_shortSide`).  Consequently

    boxMass ℓ d u = |B(u)| ≥ (μ^{-1/3})³       (u ∈ G, μ^{-1/3} ≤ ℓd) ,

i.e. `μ·|B(u)| ≥ 1`, the standing hypothesis of the fixed-`n` small-box bound
`thm:smallbox`.

The proof is the coordinatewise product formula for the box volume
(`BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1`, valid for `0 < d ≤ 1`)

    |B(u)| = ∏_j max 0 (shortSide ℓ d u j) ,

combined with `shortSide ℓ d u j ≥ μ^{-1/3} > 0` on the good set: every factor
of the product is at least `μ^{-1/3}`, and there are three factors.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixB1

theorem boxMass_ge_deltaScale_of_goodSet {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hμ : 0 < μ) (hreg : μ ^ (-(1 / 3 : ℝ)) ≤ ℓ * d) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet ℓ d μ) :
    (μ ^ (-(1 / 3 : ℝ))) ^ 3 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  -- `-(1/3)` and `-1/3` are the same real number, so the regime hypothesis and
  -- the corpus statement of `goodSet` speak about the same `μ^{-1/3}`.
  have hexp : (-(1 / 3 : ℝ)) = (-1 / 3 : ℝ) := by norm_num
  have hreg' : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d := by rw [← hexp]; exact hreg
  have hδpos : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  -- the shortest side of `B(u)` is at least `μ^{-1/3}`
  have hside : ∀ j : Fin 3,
      μ ^ (-1 / 3 : ℝ) ≤ Work.SmallBoxSliding.shortSide ℓ d u j :=
    fun j => Work.SmallBoxSliding.goodSet_shortSide hreg' hu j
  rw [hexp, Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓ hd hd1 u]
  -- every factor of the product `∏_j max 0 (shortSide …)` is at least `μ^{-1/3}`
  calc (μ ^ (-1 / 3 : ℝ)) ^ 3
      = ∏ _j : Fin 3, μ ^ (-1 / 3 : ℝ) := by
        rw [Fin.prod_univ_three]; ring
    _ ≤ ∏ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide ℓ d u j) :=
        Finset.prod_le_prod₀ (fun _ _ => hδpos.le)
          (fun j _ => le_trans (hside j) (le_max_right 0 _))

end Work.BoseFixB1
