import Mathlib.Analysis.Normed.Order.Lattice

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Topology.Charts

/-- **Openness of a chart-arc**: in a topological space `X`, let `U` be an
OPEN set with an arc chart `ψ : (0,1) ≃ₜ {x : X // x ∈ U}` (the subtype
`{t : ℝ // t ∈ Ioo 0 1}` is the open unit interval).  The image under the
chart coercion `t ↦ (ψ t : X)` of the coordinate strip
`{t | lo < (t : ℝ) < hi}` is OPEN in `X`.  Proof: the strip is open in
the unit-interval subtype (preimage of the open real interval `(lo,hi)`
under the continuous value map); `ψ` is a homeomorphism so its image is
open in the subtype `{x // x ∈ U}`; and since `U` is open, the subtype
embedding `(↑) : {x // x ∈ U} → X` is an open map (an open set of the
subtype is `val ⁻¹' O ∩ U` for some open `O`, whose value-image is
`O ∩ U`, open in `X`) — compose the three open-map steps. -/
theorem chartArc_isOpen {X : Type*} [TopologicalSpace X] (U : Set X)
    (hUopen : IsOpen U) (ψ : {t : ℝ // t ∈ Set.Ioo 0 1} ≃ₜ {x : X // x ∈ U})
    (lo hi : ℝ) :
    IsOpen ((fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => ((ψ t : {x : X // x ∈ U}) : X)) ''
      {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo lo hi}) := by
  -- The coordinate strip is open in the unit-interval subtype:
  -- it is the preimage of the open real interval `Ioo lo hi` under the
  -- (continuous) value map `t ↦ (t : ℝ)`.
  have hS : IsOpen
      ({t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo lo hi} :
        Set {t : ℝ // t ∈ Set.Ioo 0 1}) := by
    exact IsOpen.preimage (f := fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => (t : ℝ))
      continuous_subtype_val (isOpen_Ioo : IsOpen (Set.Ioo lo hi))
  -- The value map out of the open set `U` is an open map ...
  have hval : IsOpenMap (fun y : {x : X // x ∈ U} => (y : X)) := by
    exact hUopen.isOpenMap_subtype_val
  -- ... and the homeomorphism `ψ` is an open map; composing them gives an
  -- open map from the unit-interval subtype straight into `X`.
  have hF : IsOpenMap
      (fun t : {t : ℝ // t ∈ Set.Ioo 0 1} => ((ψ t : {x : X // x ∈ U}) : X)) := by
    exact hval.comp ψ.isOpenMap
  exact hF {t : {t : ℝ // t ∈ Set.Ioo 0 1} | (t : ℝ) ∈ Set.Ioo lo hi} hS

end Commons.Topology.Charts