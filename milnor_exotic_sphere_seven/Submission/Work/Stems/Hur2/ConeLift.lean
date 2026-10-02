import Submission.Work.Stems.Hur2.ConeFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Descending a homotopy along the cone map

Since `coneMap` is a quotient map and `coneMap_fibre` says exactly that a homotopy `H` which is
constant on `{1} × I` and identifies the two ends of every horizontal segment factors through it,
`H` descends to a continuous map `K : I² → X` with `K (coneMap p) = H p`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- **The descent.**  A homotopy constant on the fibres of `coneMap` (as witnessed by `hwrap` and
`hcentre`) descends to the square. -/
theorem exists_lift_coneMap {X : Type} [TopologicalSpace X]
    (H : C(unitInterval × unitInterval, X))
    (hwrap : ∀ s : unitInterval, H (s, 0) = H (s, 1))
    (hcentre : ∀ t : unitInterval, H (1, t) = H (1, 0)) :
    ∃ K : C(IC 2, X), ∀ p : IC 1 × IC 1, K (coneMap p) = H (p.1 0, p.2 0) := by
  let g : C(IC 1 × IC 1, X) := ⟨fun p => H (p.1 0, p.2 0), by fun_prop⟩
  have hfac : Function.FactorsThrough g coneMap :=
    fun a b hab => coneMap_fibre (fun s t => H (s, t)) hwrap hcentre hab
  refine ⟨isQuotientMap_coneMap.lift g hfac, ?_⟩
  intro p
  have hcomp := isQuotientMap_coneMap.lift_comp g hfac
  exact congrFun (congrArg DFunLike.coe hcomp) p

end

end Work.Stems.Hur2
