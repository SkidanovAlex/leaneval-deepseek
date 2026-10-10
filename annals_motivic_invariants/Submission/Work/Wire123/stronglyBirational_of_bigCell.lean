import Mathlib
import Submission.Work.Wire123.BigCell
import Submission.Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion_over
import Submission.Work.CY3.isoOver_stronglyBirational
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `stronglyBirational_of_bigCell` — the paper's `lem:GP-strongly-rational`

If `X` contains a big cell `U ≅ 𝔸ⁿ` whose complement is a single rational divisor `D`, then `X` is
strongly birational to `ℙⁿ`: the birational map

  `φ : X ⤏ U ≅ 𝔸ⁿ ⟶ ℙⁿ`

has `c(φ) = [ℙⁿ⁻¹] − [D] = 0`, the two exceptional divisors (the complement divisor `x` on the
`X`-side and the hyperplane at infinity `y` on the `ℙⁿ`-side) cancelling because they have the same
birational class (`ResEquiv 𝕜 x y`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

theorem stronglyBirational_of_bigCell {𝕜 : Type} [Field 𝕜] {n : ℕ} (hn : 1 ≤ n)
    (D : Work.Wire123.BigCell 𝕜 n) :
    Work.CY3.StronglyBirational 𝕜 D.X (Work.CY3.ProjectiveSpace 𝕜 n) := by
  -- the birational map `X ⤏ U` that contracts the complement divisor `x`
  obtain ⟨φ₁, hφ₁over, hφ₁ex, hφ₁exs⟩ :=
    Work.CrauderKatz.BlowUp.exists_birationalMap_exDiv_singleton_of_openImmersion_over
      (𝕜 := 𝕜) (X := D.U) (Y := D.X) (ι := D.j) D.dense
      ((AlgebraicGeometry.Scheme.Hom.isOver_iff (S := Spec (.of 𝕜))).mp D.isOver_j)
      D.x D.hx D.x_notMem D.uniq
  -- the chart `𝔸ⁿ ⤏ ℙⁿ`, whose only exceptional divisor is the hyperplane at infinity `y`
  obtain ⟨γ, hγover, hγex, hγexs⟩ := D.chart
  -- the big cell identification `U ≅ 𝔸ⁿ`, as a birational map
  let φ₂ : D.U.BirationalMap (Work.CY3.Affine 𝕜 n) := (PartialIso.ofIso D.e).toBirationalMap
  have hφ₂over : φ₂.IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_toBirationalMap (PartialIso.ofIso D.e)
      (Work.CY3.partialIsoOfIso_isOver D.e D.isOver_e)
  refine ⟨φ₁.trans (φ₂.trans γ), ?_, ?_⟩
  · haveI : φ₁.IsOver (Spec (.of 𝕜)) := hφ₁over
    haveI : φ₂.IsOver (Spec (.of 𝕜)) := hφ₂over
    haveI : γ.IsOver (Spec (.of 𝕜)) := hγover
    haveI : (φ₂.trans γ).IsOver (Spec (.of 𝕜)) :=
      Work.Motivic.pseudoReg_isOver_trans φ₂ γ
    exact Work.Motivic.pseudoReg_isOver_trans φ₁ (φ₂.trans γ)
  · intro W _ w
    haveI : φ₁.IsOver (Spec (.of 𝕜)) := hφ₁over
    haveI : φ₂.IsOver (Spec (.of 𝕜)) := hφ₂over
    haveI : γ.IsOver (Spec (.of 𝕜)) := hγover
    haveI : (φ₂.trans γ).IsOver (Spec (.of 𝕜)) :=
      Work.Motivic.pseudoReg_isOver_trans φ₂ γ
    have hsum : cInv 𝕜 w (φ₁.trans (φ₂.trans γ)) = cInv 𝕜 w φ₁ + cInv 𝕜 w γ := by
      rw [Work.Motivic.cInv_add (𝕜 := 𝕜) w φ₁ (φ₂.trans γ),
        Work.Motivic.cInv_add (𝕜 := 𝕜) w φ₂ γ,
        Work.LLink.cInv_eq_zero_of_isPseudoIso 𝕜 w (PartialIso.ofIso D.e)
          (Work.CY3.partialIsoOfIso_isPseudoIso D.e)]
      first | refl_ring1 | ring
    rw [hsum]
    by_cases hxw : ResEquiv 𝕜 D.x w
    · have hyw : ResEquiv 𝕜 D.y w :=
        Work.Motivic.ResEquiv.trans (Work.Motivic.ResEquiv.symm D.resEquiv) hxw
      have hx1 : cInv 𝕜 w φ₁ = -1 := by
        rw [← Work.LLink.cInv_congr_of_resEquiv (𝕜 := 𝕜) D.x hxw φ₁]
        show (excCount 𝕜 D.x φ₁.symm : ℤ) - excCount 𝕜 D.x φ₁ = -1
        rw [Work.LLink.excCount_eq_one_of_exDiv_eq_singleton (𝕜 := 𝕜) (X := D.X) (Y := D.U)
              (Z := D.X) D.x φ₁ hφ₁ex (Work.Motivic.ResEquiv.refl 𝕜 D.x),
            Work.LLink.excCount_eq_zero_of_exDiv_eq_empty (𝕜 := 𝕜) (X := D.U) (Y := D.X)
              (Z := D.X) D.x φ₁.symm hφ₁exs]
        norm_num
      have hy1 : cInv 𝕜 w γ = 1 := by
        rw [← Work.LLink.cInv_congr_of_resEquiv (𝕜 := 𝕜) D.y hyw γ]
        show (excCount 𝕜 D.y γ.symm : ℤ) - excCount 𝕜 D.y γ = 1
        rw [Work.LLink.excCount_eq_one_of_exDiv_eq_singleton (𝕜 := 𝕜)
              (X := Work.CY3.ProjectiveSpace 𝕜 n) (Y := Work.CY3.Affine 𝕜 n)
              (Z := Work.CY3.ProjectiveSpace 𝕜 n) D.y γ.symm hγexs
              (Work.Motivic.ResEquiv.refl 𝕜 D.y),
            Work.LLink.excCount_eq_zero_of_exDiv_eq_empty (𝕜 := 𝕜)
              (X := Work.CY3.Affine 𝕜 n) (Y := Work.CY3.ProjectiveSpace 𝕜 n)
              (Z := Work.CY3.ProjectiveSpace 𝕜 n) D.y γ hγex]
        norm_num
      rw [hx1, hy1]
      norm_num
    · have hyw : ¬ ResEquiv 𝕜 D.y w := fun h => hxw (Work.Motivic.ResEquiv.trans D.resEquiv h)
      have hx1 : cInv 𝕜 w φ₁ = 0 := by
        have ha : excCount 𝕜 w φ₁ = 0 :=
          Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton (𝕜 := 𝕜) (X := D.X) (Y := D.U)
            (Z := W) w φ₁ hφ₁ex hxw
        have hb : excCount 𝕜 w φ₁.symm = 0 :=
          Work.LLink.excCount_eq_zero_of_exDiv_eq_empty (𝕜 := 𝕜) (X := D.U) (Y := D.X)
            (Z := W) w φ₁.symm hφ₁exs
        show (excCount 𝕜 w φ₁.symm : ℤ) - excCount 𝕜 w φ₁ = 0
        rw [ha, hb]
        norm_num
      have hy1 : cInv 𝕜 w γ = 0 := by
        have ha : excCount 𝕜 w γ = 0 :=
          Work.LLink.excCount_eq_zero_of_exDiv_eq_empty (𝕜 := 𝕜)
            (X := Work.CY3.Affine 𝕜 n) (Y := Work.CY3.ProjectiveSpace 𝕜 n) (Z := W) w γ hγex
        have hb : excCount 𝕜 w γ.symm = 0 :=
          Work.LLink.excCount_eq_zero_of_exDiv_eq_singleton (𝕜 := 𝕜)
            (X := Work.CY3.ProjectiveSpace 𝕜 n) (Y := Work.CY3.Affine 𝕜 n) (Z := W) w γ.symm
            hγexs hyw
        show (excCount 𝕜 w γ.symm : ℤ) - excCount 𝕜 w γ = 0
        rw [ha, hb]
        norm_num
      rw [hx1, hy1]
      norm_num

end

end Work.Wire123
