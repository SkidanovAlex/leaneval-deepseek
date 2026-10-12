import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

/-!
# `volume (interiorSet ℓ d μ) < ⊤`

The sliding-localisation interior
`I₋ = interiorSet ℓ d μ = {u | ∀ j, |((ℓ*d)•u).ofLp j| ≤ ½ℓ(1+d) − 2μ^{-1/3}}`
(`Work.SmallBoxSliding.interiorSet`, FS `thm:aprioriHLambda`) is a bounded set:
its defining inequalities are coordinatewise bounds on the linear image
`w = (ℓ*d)•u` of `u`, so for `ℓ*d > 0` it sits inside the centred cube
`acube (2R)` with `R := max (½ℓ(1+d) − 2μ^{-1/3}) 0 / (ℓ*d)`; when
`½ℓ(1+d) − 2μ^{-1/3} < 0` the defining bounds are unsatisfiable and `I₋ = ∅`
(and `R = 0` handles this case uniformly).  Hence `volume I₋ ≤ (2R)³ < ⊤`.

This is the finiteness input needed to turn the sliding integrals over `I₋`
into integrals against a finite measure (cf. `BoseFixB1.perBoxF_integrated`).
-/

/-- The interior set of the sliding localisation has finite volume. -/
theorem interiorSet_lt_top {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.SmallBoxSliding.interiorSet ℓ d μ) < ⊤ := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  -- the outer coordinate bound and the resulting box radius
  set C : ℝ := (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) with hCdef
  set R : ℝ := max C 0 / (ℓ * d) with hRdef
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (le_max_right _ _) hld.le
  -- `I₋` is contained in the centred cube `acube (2R)`
  have hsub : Work.SmallBoxSliding.interiorSet ℓ d μ ⊆ Submission.BoseGases.acube (2 * R) := by
    intro u hu
    rw [Work.SmallBoxSliding.mem_interiorSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    -- coordinate bound: `(ℓd)·|u_j| ≤ C`
    have h1 : (ℓ * d) * |u.ofLp j| ≤ C := by
      have h := hu j
      rw [hCdef]
      simpa [abs_of_pos hℓ, abs_of_pos hd] using h
    -- hence `|u_j| ≤ R`
    have h2 : |u.ofLp j| ≤ R := by
      rw [hRdef, le_div_iff₀ hld]
      calc |u.ofLp j| * (ℓ * d) = (ℓ * d) * |u.ofLp j| := by ring
        _ ≤ C := h1
        _ ≤ max C 0 := le_max_left _ _
    have h3 := abs_le.mp h2
    simp only [Set.mem_Icc]
    constructor <;> linarith [h3.1, h3.2]
  exact lt_of_le_of_lt (MeasureTheory.measure_mono hsub)
    (Submission.BoseGases.acube_lt_top (2 * R) (by linarith))

end Work.BoseFixB1.WB
