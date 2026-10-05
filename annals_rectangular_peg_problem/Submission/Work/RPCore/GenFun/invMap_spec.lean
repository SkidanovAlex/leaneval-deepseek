import Mathlib
import Submission.Work.RPCore.GenFun.Basic
import Submission.Work.RPCore.GenFun.add_bijective_of_lipschitzWith_lt_one
import Submission.Work.RPCore.GenFun.fderiv_invMap

/-!
# The global inverse of `gproj ψ` for a near-identity map `ψ`

For a `C^3` map `ψ : PS → PS` with `‖fderiv ψ x - 1‖ ≤ 1/4` everywhere, the projection
`gproj ψ x = (x.1, (ψ x).2)` is a global `C^3` diffeomorphism of `PS`:

* `gproj ψ = id + gdisp ψ`, and `gdisp ψ` is Lipschitz with constant `1/4 < 1`, so `gproj ψ`
  is a bijection (`add_bijective_of_lipschitzWith_lt_one`);
* the set-theoretic inverse `invMap ψ = Function.invFun (gproj ψ)` is therefore a two-sided
  inverse;
* since the strict derivative of `gproj ψ` at every point is invertible, the inverse function
  theorem shows that `invMap ψ` is `C^3` with derivative
  `(fderiv (gproj ψ) (invMap ψ y))⁻¹ = ↑(dgequivLin (fderiv ψ (invMap ψ y)) _).symm`.

This file proves the inverse function theorem statement in the form needed by the
generating-function construction (`exists_type2GF`).
-/

set_option autoImplicit false

noncomputable section

open Work.RPV

open scoped NNReal Topology

namespace Work.RPCore.GenFun

/-- `invMap ψ` is `C^3` when `gproj ψ` is a bijection whose strict derivative is invertible
everywhere. -/
theorem contDiff_invMap (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ PS‖ ≤ 1 / 4)
    (hbij : Function.Bijective (gproj ψ)) : ContDiff ℝ 3 (invMap ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hleft : ∀ x : PS, invMap ψ (gproj ψ x) = x :=
    fun x => Function.leftInverse_invFun hbij.1 x
  have hright : gproj ψ (invMap ψ y) = y := Function.rightInverse_invFun hbij.2 y
  have hA : ‖fderiv ℝ ψ (invMap ψ y) - ContinuousLinearMap.id ℝ PS‖ ≤ 1 / 4 := hnear _
  have hf' : HasFDerivAt (gproj ψ)
      (↑(dgequivLin (fderiv ℝ ψ (invMap ψ y)) hA) : PS →L[ℝ] PS) (invMap ψ y) := by
    rw [coe_dgequivLin]
    exact hasFDerivAt_gproj ψ hψ _
  have hcd : ContDiffAt ℝ 3 (gproj ψ) (invMap ψ y) := (contDiff_gproj hψ).contDiffAt
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  -- The inverse function theorem at `x = invMap ψ y`: the local inverse of `gproj ψ` is `C^3`.
  have hlinv : ContDiffAt ℝ 3
      (hcd.localInverse (f' := dgequivLin (fderiv ℝ ψ (invMap ψ y)) hA) hf' hn)
      (gproj ψ (invMap ψ y)) :=
    hcd.to_localInverse (f' := dgequivLin (fderiv ℝ ψ (invMap ψ y)) hA) hf' hn
  -- `invMap ψ` agrees with that local inverse near `gproj ψ (invMap ψ y)`.
  have hgg : ∀ᶠ z in 𝓝 (invMap ψ y), invMap ψ (gproj ψ z) = z :=
    Filter.Eventually.of_forall hleft
  have hloc := (hcd.hasStrictFDerivAt' hf' hn).localInverse_unique hgg
  have hloc' : invMap ψ =ᶠ[𝓝 (gproj ψ (invMap ψ y))]
      (hcd.localInverse (f' := dgequivLin (fderiv ℝ ψ (invMap ψ y)) hA) hf' hn) := by
    simp only [ContDiffAt.localInverse]
    exact hloc
  rw [hright] at hlinv hloc'
  exact hlinv.congr_of_eventuallyEq hloc'

/-- `gproj ψ` is bijective as soon as `gdisp ψ` is Lipschitz with constant `< 1`. -/
theorem bijective_gproj_of_lipschitz (ψ : PS → PS)
    (hgd : LipschitzWith (1 / 4 : NNReal) (gdisp ψ)) : Function.Bijective (gproj ψ) := by
  have hbij_add : Function.Bijective (fun x : PS => x + gdisp ψ x) :=
    add_bijective_of_lipschitzWith_lt_one hgd (by norm_num)
  have h : gproj ψ = fun x : PS => x + gdisp ψ x := funext (gproj_eq_add_gdisp ψ)
  rw [h]
  exact hbij_add

theorem invMap_spec (ψ : Work.RPV.PS → Work.RPV.PS) (hψ : ContDiff ℝ 3 ψ)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ Work.RPV.PS‖ ≤ 1 / 4) :
    Function.Bijective (Work.RPCore.GenFun.gproj ψ) ∧
    (∀ x : Work.RPV.PS, Work.RPCore.GenFun.invMap ψ (Work.RPCore.GenFun.gproj ψ x) = x) ∧
    (∀ y : Work.RPV.PS, Work.RPCore.GenFun.gproj ψ (Work.RPCore.GenFun.invMap ψ y) = y) ∧
    ContDiff ℝ 3 (Work.RPCore.GenFun.invMap ψ) ∧
    (∀ y : Work.RPV.PS, fderiv ℝ (Work.RPCore.GenFun.invMap ψ) y =
      ↑((Work.RPCore.GenFun.dgequivLin (fderiv ℝ ψ (Work.RPCore.GenFun.invMap ψ y))
        (hnear (Work.RPCore.GenFun.invMap ψ y))).symm)) := by
  have hgd : LipschitzWith (1 / 4 : NNReal) (gdisp ψ) := lipschitzWith_gdisp ψ hψ hnear
  have hbij : Function.Bijective (gproj ψ) := bijective_gproj_of_lipschitz ψ hgd
  exact ⟨hbij,
    fun x => Function.leftInverse_invFun hbij.1 x,
    fun y => Function.rightInverse_invFun hbij.2 y,
    contDiff_invMap ψ hψ hnear hbij,
    fun y => fderiv_invMap ψ hψ hnear hbij y⟩

end Work.RPCore.GenFun
