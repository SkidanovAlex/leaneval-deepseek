/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.CharP.Model
import Submission.Work.FFResidual.CharP.exists_hasReductionPlace_asOrder

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The function-field residual at a place: the Artin–Schreier case (characteristic five)

Let `P` be a place of a function field `𝕜` of characteristic `5` over its field of constants `𝔽`
(with uniformizer `π`), and let `c ∈ 𝔽` be a good Tate parameter.  Then the residual of the
function-field classes (b), (c), (d) of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, Theorem 1.2 (1), holds at `𝕜`:

  `nonempty_functionFieldResidual_charP` — `Nonempty (FunctionFieldResidual 𝔽 𝕜)`.

The cyclic quintic extension of `𝕜` is the **Artin–Schreier** extension of the *place at infinity*
`𝕜(s)`, `s ^ 5 - s = π⁻¹` (`FunctionFieldPlace.asCyclicExtension`), whose local model is the
Eisenstein order `R[w]`, `w = s⁻¹`; the place obstruction is
`Work.FFResidual.CharP.exists_hasReductionPlace_asOrder`.  No primitive fifth root of unity is
needed, which is what makes the characteristic-`5` cases of the classes accessible.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-- **The function-field residual at a place, in characteristic five.** -/
theorem nonempty_functionFieldResidual_charP (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    Nonempty (Work.ClassBCD.FunctionFieldResidual 𝔽 𝕜) := by
  classical
  haveI hGR : WeierstrassCurve.HasGoodReduction P.AsOrder
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop) :=
    Work.FFResidual.CharP.hasGoodReduction_asOrder (P := P) c hΔ hj
  obtain ⟨d, hplace⟩ :=
    Work.FFResidual.CharP.exists_hasReductionPlace_asOrder (P := P) c hΔ hj
      (Work.FFResidual.CharP.modelPreserves_asOrder P)
      (Work.FFResidual.CharP.modelResidueTrivial_asOrder P)
  let L : Work.PointlessTwist.CyclicExtension 𝕜 5 := P.asCyclicExtension
  letI hAlgL : Algebra 𝔽 L.L := (show Algebra 𝔽 P.AsTop from inferInstance)
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

/-- **The arithmetic half of the classes (b), (c), (d) at a place in characteristic five.** -/
theorem nonempty_hasPointlessTwist_of_place_charP (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5]
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) :
    ∃ dec : DecidableEq 𝕜, @Work.PointlessTwist.HasPointlessTwist 𝕜 _ dec :=
  (P.nonempty_functionFieldResidual_charP c hΔ hj).some.exists_hasPointlessTwist

end FunctionFieldPlace

end

end Work.FFResidual
