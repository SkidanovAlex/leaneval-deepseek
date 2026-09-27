import Mathlib
import Submission.Work.Mostow.cuspThinRegion_eq_parDisp

/-!
# Definitions for the cusp-stabiliser cocompactness argument

The Margulis region at a cusp `ξ` is
`cuspThinRegion Γ ξ ε = {u | some parabolic q ∈ Γ fixing ξ moves u by < ε}`, and by
`Work.Mostow.cuspThinRegion_eq_parDisp` it is also the sublevel set

`u ∈ cuspThinRegion Γ ξ ε ↔ lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε`.

Hence for every flat point `y ∈ ξ^⊥` there is a *threshold* (frontier) point on the horosphere
of `ξ` whose flat coordinate is `y` and which sits exactly on the boundary of the region:
this is `frontierPt Γ ξ ε y`, the point of level `cEps ε / parDisp Γ ξ y` with flat coordinate
`y`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- **The frontier (threshold) point** of the Margulis region `cuspThinRegion Γ ξ ε` above the
flat point `y ∈ ξ^⊥`: the point of the horosphere of `ξ` whose level is `cEps ε / parDisp Γ ξ y`
and whose flat coordinate is `y`.  Its defining property is
`lev ξ (frontierPt Γ ξ ε y) * parDisp Γ ξ (yc ξ (frontierPt Γ ξ ε y)) = cEps ε`. -/
def frontierPt (Γ : Subgroup (PO n 1)) (ξ : E n) (ε : ℝ) (y : E n) : E n :=
  hptOf ξ y (cEps ε / parDisp Γ ξ y)

/-- The flat coordinate of a frontier point is the point it was built from. -/
lemma yc_frontierPt {Γ : Subgroup (PO n 1)} {ξ y : E n} (hξ : ξ ∈ Sph n) {ε : ℝ}
    (hy : inner ℝ y ξ = 0) (hpos : 0 < cEps ε / parDisp Γ ξ y) :
    yc ξ (frontierPt Γ ξ ε y) = y :=
  (hptOf_level ξ hξ _ hpos y hy).2

/-- The level of a frontier point is `cEps ε / parDisp`. -/
lemma lev_frontierPt {Γ : Subgroup (PO n 1)} {ξ y : E n} (hξ : ξ ∈ Sph n) {ε : ℝ}
    (hy : inner ℝ y ξ = 0) (hpos : 0 < cEps ε / parDisp Γ ξ y) :
    lev ξ (frontierPt Γ ξ ε y) = cEps ε / parDisp Γ ξ y :=
  (hptOf_level ξ hξ _ hpos y hy).1

/-- The defining property of the frontier point: it lies exactly on the threshold of the
Margulis region, `lev ξ u * parDisp Γ ξ (yc ξ u) = cEps ε`. -/
lemma frontierPt_threshold {Γ : Subgroup (PO n 1)} {ξ y : E n} (hξ : ξ ∈ Sph n) {ε : ℝ}
    (hy : inner ℝ y ξ = 0) (hpos : 0 < cEps ε / parDisp Γ ξ y) :
    lev ξ (frontierPt Γ ξ ε y) * parDisp Γ ξ (yc ξ (frontierPt Γ ξ ε y)) = cEps ε := by
  rw [lev_frontierPt hξ hy hpos, yc_frontierPt hξ hy hpos]
  have hne : parDisp Γ ξ y ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hpos
    exact absurd hpos (lt_irrefl 0)
  rw [div_mul_cancel₀ _ hne]

end

end Work.Mostow
