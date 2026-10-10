import Mathlib
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotT

/-- **The element `w·w·x` at the point at infinity is a unit congruent to `1`.**

For any field `L` and any Weierstrass curve `E/L`: let `x = genX E`, `y = genY E`, `u = 1/x = infU E`,
`w = y/x² = infW E`, and `h = 1 + a₂u + a₄u² + a₆u³ ∈ L[u,w]` (so that `u·h = w² + a₁uw + a₃u²w`).
Then `w²·x` lies in the local ring `infPlace E` of the point at infinity and satisfies `w²x - 1 ∈ 𝔪`,
the maximal ideal of `infPlace E`; equivalently `w²x` is a unit of the discrete valuation ring
`infPlace E` that reduces to `1` in the residue field `L`.

Indeed `w²x = h - a₁w - a₃uw`, `h - 1 = a₂u + a₄u² + a₆u³`, and `u, w ∈ 𝔪`.

Route: `Work.MotC2.InfPlaceCore.coe_U_mul_H_eq` gives the chart relation `u·h = w·(w + a₁u + a₃u²)`;
multiplying it by `x` (using `Work.MotC2.infU_mul_genX`) gives the function field identity
`x·w² = h - a₁w - a₃uw` (`Work.MotC2.PoleSetup.genX_mul_infW_sq` states exactly this). The membership
is then proved with `Subtype.ext` (the goal becomes an equation in `Func E`): `InfPlaceCore.H_sub_one_mem`
says `H - 1 ∈ infIdealR E` and `IsLocalization.AtPrime.map_eq_maximalIdeal`/`Ideal.mem_map_of_mem` turn
this into the statement that the image of `H` in `↥(infPlace E)` differs from `1` by an element of the
maximal ideal, while `Ideal.mem_map_of_mem` applied to `Ideal.subset_span` handles the images of
`U E` and `W E` (both in `infIdealR E = ⟨U E, W E⟩`). -/
theorem infW_genX_sub_one_mem {L : Type} [Field L] (E : WeierstrassCurve L) :
    ((⟨Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2,
        Work.MotC2.genX_mul_infW_sq_mem_infPlace E⟩ : ↥(Work.MotC2.infPlace E)) - 1) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E) := by
  -- The chart element `T = (h - 1) - a₁·w - a₃·(u·w)` of `infCoordRing E = L[u,w]`; its image in
  -- `L(E)` is `x·w² - 1`, and it lies in the ideal `infIdealR E = ⟨u, w⟩`.
  let T : ↥(Work.MotC2.infCoordRing E) :=
    Work.MotC2.InfPlaceCore.H E - 1 -
      (algebraMap L ↥(Work.MotC2.infCoordRing E)) E.a₁ * Work.MotC2.InfPlaceCore.W E -
      (algebraMap L ↥(Work.MotC2.infCoordRing E)) E.a₃ * Work.MotC2.InfPlaceCore.U E *
        Work.MotC2.InfPlaceCore.W E
  have hT : T ∈ Work.MotC2.infIdealR E := by
    change (Work.MotC2.InfPlaceCore.H E - 1 -
      (algebraMap L ↥(Work.MotC2.infCoordRing E)) E.a₁ * Work.MotC2.InfPlaceCore.W E -
      (algebraMap L ↥(Work.MotC2.infCoordRing E)) E.a₃ * Work.MotC2.InfPlaceCore.U E *
        Work.MotC2.InfPlaceCore.W E) ∈ Work.MotC2.infIdealR E
    have hH : Work.MotC2.InfPlaceCore.H E - 1 ∈ Work.MotC2.infIdealR E :=
      Work.MotC2.InfPlaceCore.H_sub_one_mem E
    have hW : Work.MotC2.InfPlaceCore.W E ∈ Work.MotC2.infIdealR E :=
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hU : Work.MotC2.InfPlaceCore.U E ∈ Work.MotC2.infIdealR E :=
      Ideal.subset_span (Set.mem_insert _ _)
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hH (Ideal.mul_mem_left _ _ hW))
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hU))
  -- The two sides agree in `L(E)`: both equal `x·w² - 1`, by `genX_mul_infW_sq`.
  have hkey : ((⟨Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2,
        Work.MotC2.genX_mul_infW_sq_mem_infPlace E⟩ : ↥(Work.MotC2.infPlace E)) - 1)
      = (algebraMap ↥(Work.MotC2.infCoordRing E) ↥(Work.MotC2.infPlace E)) T := by
    apply Subtype.ext
    show Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2 - 1 = (T : Work.MotC2.Func E)
    simp only [T, Work.MotC2.InfPlaceCore.coe_H, Work.MotC2.InfPlaceCore.coe_W,
      Work.MotC2.InfPlaceCore.coe_U, Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one,
      Subalgebra.coe_algebraMap]
    rw [Work.MotC2.genX_mul_infW_sq E]
    first | refl_ring1 | ring
  -- `↥(infPlace E)` is the localization of `infCoordRing E` at `⟨u, w⟩`; the maximal ideal is the
  -- extension of `infIdealR E`, so the image of `T` lies in it.
  haveI hloc : IsLocalization.AtPrime ↥(Work.MotC2.infPlace E) (Work.MotC2.infIdealR E) :=
    Work.MotC2.PoleAux.instIsLocalizationInfPlace E
  rw [hkey, ← IsLocalization.AtPrime.map_eq_maximalIdeal (Work.MotC2.infIdealR E)
    ↥(Work.MotC2.infPlace E)]
  exact Ideal.mem_map_of_mem _ hT

end Work.MotT
