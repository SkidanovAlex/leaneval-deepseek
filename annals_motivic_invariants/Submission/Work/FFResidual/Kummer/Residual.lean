/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Kummer.Model
import Submission.Work.FFResidual.Kummer.exists_hasReductionPlace_kummerOrder
import Submission.Work.ClassBCD.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field residual at a place of the function field: the Kummer case

Let `P` be a place of the function field `𝕜` over its field of constants `𝔽` (with uniformizer `π`),
let `𝔽` contain a primitive fifth root of unity `ζ` (so `char 𝔽 ≠ 5`), and let `c ∈ 𝔽` be a good
Tate parameter (`Δ ≠ 0`, `j ≠ 1728`).  Then the **residual** `Work.ClassBCD.FunctionFieldResidual`
of the function-field classes (b), (c), (d) of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, Theorem 1.2 (1), holds at `𝕜`:

  `nonempty_functionFieldResidual` — `Nonempty (FunctionFieldResidual 𝔽 𝕜)`.

The concrete data is the constant Tate model `E(c) = y² + (1-c)xy - cy = x³ - cx²` with its point
`(0,0)` of order `5` base changed to `𝕜`, together with the **Kummer extension** `𝕜(s)`, `s ^ 5 = π`
of `𝕜` at the place (cyclic quintic, generator `s ↦ ζ s`), and the **place obstruction**: the
reduction map on the points of `E` at the local model `R[s] ⊆ 𝕜(s)` (a discrete valuation ring with
fraction field `𝕜(s)`, at which `E` has good reduction and on whose residue field the generator acts
trivially) is additive and Galois-invariant and does not kill the marker.

Consequently the arithmetic half `HasPointlessTwist 𝕜` follows
(`nonempty_hasPointlessTwist_of_hasFunctionFieldPlace`), and the class statements of the area are
`Main.hasPointlessTwist_functionField_*_of_place`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The function-field residual at a place, in the Kummer case.**  If `𝔽` contains a primitive
fifth root of unity `ζ` and `c ∈ 𝔽` is a good Tate parameter, then the place `P` of the function
field `𝕜` produces the residual `FunctionFieldResidual 𝔽 𝕜`. -/
theorem nonempty_functionFieldResidual (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 𝕜) := by
  classical
  haveI hGR : WeierstrassCurve.HasGoodReduction P.KummerOrder
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top) :=
    Work.FFResidual.Kummer.hasGoodReduction_kummerOrder (P := P) c hΔ hj
  obtain ⟨d, hplace⟩ :=
    Work.FFResidual.Kummer.exists_hasReductionPlace_kummerOrder (P := P) c hΔ hj ζ hζ
      (Work.FFResidual.Kummer.modelPreserves_kummerOrder P ζ hζ)
      (Work.FFResidual.Kummer.modelResidueTrivial_kummerOrder (P := P) ζ hζ)
  let L : Work.PointlessTwist.CyclicExtension 𝕜 5 := P.kummerCyclicExtension ζ hζ
  letI hAlgL : Algebra 𝔽 L.L := (show Algebra 𝔽 P.Top from inferInstance)
  haveI hTowerL : IsScalarTower 𝔽 𝕜 L.L :=
    IsScalarTower.of_algebraMap_eq (R := 𝔽) (S := 𝕜) (A := L.L) (fun x => rfl)
  let data : Work.ClassBCD.ConstantTwistData 𝔽 𝕜 c :=
    { hΔ := hΔ
      hj := hj
      d := d
      L := L
      decEqL := Classical.decEq L.L
      algebraL := hAlgL
      towerL := hTowerL }
  refine ⟨{ decF := inferInstance
            decK := Classical.decEq 𝕜
            c := c
            data := data
            place := hplace }⟩

/-- **The arithmetic half of the classes (b), (c), (d) at a place of the function field**: the
residual gives `HasPointlessTwist 𝕜`. -/
theorem nonempty_hasPointlessTwist_of_place (P : FunctionFieldPlace 𝔽 𝕜) (ζ : 𝔽)
    (hζ : IsPrimitiveRoot ζ 5) (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq 𝕜, @Work.PointlessTwist.HasPointlessTwist 𝕜 _ dec :=
  (P.nonempty_functionFieldResidual ζ hζ c hΔ hj).some.exists_hasPointlessTwist

end FunctionFieldPlace

end

end Work.FFResidual
