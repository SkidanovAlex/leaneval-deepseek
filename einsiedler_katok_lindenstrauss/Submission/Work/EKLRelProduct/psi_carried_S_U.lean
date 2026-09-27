import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.psiNu_uMargEqPsiMap
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `Work.EKLRelProduct.psi_carried_S_U`

The `U`-factor `psi` of the local product structure at the point `x` of the `n`-th flower is
carried by its source set `S_U hf n x` (`USIDE_PLAN.md`).

This is purely a matter of pushing sets around:

* `Work.EKLRelProduct.psiNu_uMargEqPsiMap` identifies the `U`-marginal `uMarg` with the
  pushforward of `psi` along the reparametrisation `shiftMap t u` (`t = hT (co n x)`,
  `u = hU (co n x)`):
  `uMarg hf νH n x = (psi hf νH n x).map (shiftMap t u)`.
* `S_U hf n x` is *by definition* `(shiftMap t u) ⁻¹' (V R ∩ U)`.
* Hence `psi … (S_U hf n x)ᶜ = uMarg … (V hf.R ∩ U)ᶜ`, and the latter vanishes by
  `Work.EKLRelProduct.uSide_uMarg_carried` (the `U`-marginal of the `H`-plaque measure is carried
  by the `U`-ball `V R ∩ U`).
-/

open MeasureTheory

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract Work.EKLProd

theorem psi_carried_S_U {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) :
    Work.EKLRelProduct.psi hf νH n x (Work.EKLRelProduct.S_U hf n x)ᶜ = 0 := by
  classical
  -- the `U`-ball `V R ∩ U` is Borel
  have hS : @MeasurableSet SL3 (borel SL3) (V hf.R ∩ (U : Set SL3)) :=
    ((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet.inter
      hUc.measurableSet
  have hsm : Measurable (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))) :=
    (measurableEmbedding_shiftMap _ _).measurable
  -- `uMarg` is `psi` reparametrised by `shiftMap t u`
  have h1 := psiNu_uMargEqPsiMap hTH hUH hnorm hcop hdisj hHc hTc hUc hf n νH hx
  -- `S_U` is by definition the `shiftMap`-preimage of the `U`-ball
  have hSet : Work.EKLRelProduct.S_U hf n x
      = shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x)) ⁻¹' (V hf.R ∩ (U : Set SL3)) := by
    ext g
    simp [Work.EKLRelProduct.S_U]
  calc Work.EKLRelProduct.psi hf νH n x (Work.EKLRelProduct.S_U hf n x)ᶜ
      = ((Work.EKLRelProduct.psi hf νH n x).map
            (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))))
          (V hf.R ∩ (U : Set SL3))ᶜ := by
        rw [Measure.map_apply hsm hS.compl, hSet, Set.preimage_compl]
    _ = (Work.EKLRelProduct.uMarg hf νH n x) (V hf.R ∩ (U : Set SL3))ᶜ := by rw [h1]
    _ = 0 := uSide_uMarg_carried hTH hUH hcop hdisj hf νH n hx hS

end Work.EKLRelProduct
