import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.psiEqNuU
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLRelProduct.map_snd_prodFlowerLambdaTP_eq_uMarg
import Submission.Work.EKLRelProduct.psi_carried_S_U

namespace Work.EKLRelProduct

/-! Route (for the prover).

`Work.EKLProd.atomId hf n νH νU x` unfolds to
`atomShU hf n νU x = c • atomMargU hf n νH x`, `0 < c ≠ ⊤`.

* `Work.EKLRelProduct.uShift_restrict_eq_shiftMap` gives
  `atomShU hf n νU x = ((νU x).restrict (S_U hf n x)).map (shiftMap t u)` with
  `t = hT T U (hf.co n x)`, `u = hU T U (hf.co n x)`.
* `Work.EKLRelProduct.map_snd_prodFlowerLambdaTP_eq_uMarg` gives
  `(prodFlowerΛTP hf n νH x).map Prod.snd = uMarg hf νH n x`, so that
  `atomMargU hf n νH x = (uMarg hf νH n x).restrict (V hf.R ∩ U)`.
* `Work.EKLRelProduct.psiNu_uMargEqPsiMap` gives `uMarg hf νH n x = (psi ...).map shiftMap`,
  and `Work.EKLRelProduct.measure_map_restrict` turns both restrictions into pushforwards:
  `(psi ...).restrict (V R ∩ U) = ((psi ...).restrict S_U).map shiftMap`.
* `psi` is carried by `S_U`: `uMarg` is carried by `V R ∩ U`
  (`Work.EKLRelProduct.uSide_uMarg_carried`) and `S_U` is *by definition*
  `shiftMap t u ⁻¹' (V hf.R ∩ U)`, so push forward by `shiftMap`
  (`Work.EKLRelProduct.psi_carried_S_U`).
* Cancel the pushforward with `(measurableEmbedding_shiftMap t u).map_injective`, obtaining
  `(νU x).restrict (S_U) = c • psi ...`, hence `psi ... = c⁻¹ • (νU x).restrict (S_U)`
  (use `ENNReal.inv_ne_zero`, `ENNReal.inv_ne_top`, `ENNReal.inv_mul_cancel`).

DO NOT import `Submission.Work.EKLProd.prodFlower_atom_product` (it imports the requester's
file, so importing it would create an import cycle); re-prove the helper above if needed.
Also `open scoped ENNReal` is convenient. -/

open MeasureTheory

set_option linter.unusedVariables false

noncomputable section

open Work.EKLContract Work.EKLProd

theorem psi_eq_smul_nuU_restrict_of_atomId {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : Work.EKLContract.X3} (hxZ : x ∈ hf.Z n)
    (hId : Work.EKLProd.atomId hf n νH νU x) :
    ∃ cU : ENNReal, 0 < cU ∧ cU ≠ ⊤ ∧
      Work.EKLRelProduct.psi hf νH n x
        = cU • (νU x).restrict (Work.EKLRelProduct.S_U hf n x) := by
  classical
  obtain ⟨c, hc0, hct, hIdEq⟩ := hId
  -- the `U`-ball `V R ∩ U` is Borel
  have hSmeas : MeasurableSet (V hf.R ∩ (U : Set SL3)) :=
    (((Work.EKLContract.Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1).measurableSet).inter
      hUc.measurableSet
  -- `S_U` is *by definition* the `shiftMap t u`-preimage of the `U`-ball
  have hSUx : (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))) ⁻¹'
      (V hf.R ∩ (U : Set SL3)) = S_U hf n x := rfl
  -- the two sides of the identification `atomId x` are `shiftMap`-pushforwards of the two
  -- measures that occur in the conclusion
  have hL : atomShU hf n νU x
      = ((νU x).restrict (S_U hf n x)).map
          (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))) := by
    rw [atomShU, uShift_restrict_eq_shiftMap]
  have hR : atomMargU hf n νH x
      = ((psi hf νH n x).restrict (S_U hf n x)).map
          (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))) := by
    rw [atomMargU,
      map_snd_prodFlowerLambdaTP_eq_uMarg hTH hUH hnorm hcop hdisj hHc hTc hUc hf n νH hxZ,
      psiNu_uMargEqPsiMap hTH hUH hnorm hcop hdisj hHc hTc hUc hf n νH hxZ,
      measure_map_restrict (psi hf νH n x) (measurableEmbedding_shiftMap _ _).measurable hSmeas,
      hSUx]
  -- the identification, transported along the (injective) `shiftMap`-pushforward
  have hEq : ((νU x).restrict (S_U hf n x)).map
        (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x)))
      = (c • (psi hf νH n x).restrict (S_U hf n x)).map
          (shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))) := by
    rw [← hL, hIdEq, hR,
      MeasureTheory.Measure.map_smul _ (measurableEmbedding_shiftMap _ _).measurable.aemeasurable]
  have hcancel : (νU x).restrict (S_U hf n x)
      = c • (psi hf νH n x).restrict (S_U hf n x) :=
    (measurableEmbedding_shiftMap (hT T U (hf.co n x)) (hU T U (hf.co n x))).map_injective hEq
  -- `psi x` is carried by `S_U`, so the restriction on the right is `psi x` itself
  have hcarried := psi_carried_S_U hTH hUH hnorm hcop hdisj hHc hTc hUc hf n νH hxZ
  have hres : (psi hf νH n x).restrict (S_U hf n x) = psi hf νH n x :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem (s := S_U hf n x)
      (by rw [MeasureTheory.ae_iff]; exact hcarried)
  have hmain : psi hf νH n x = c⁻¹ • ((νU x).restrict (S_U hf n x)) := by
    have h1 : c • psi hf νH n x = (νU x).restrict (S_U hf n x) := by
      rw [hcancel, hres]
    calc psi hf νH n x = (1 : ENNReal) • psi hf νH n x := (one_smul _ _).symm
      _ = (c⁻¹ * c) • psi hf νH n x := by rw [ENNReal.inv_mul_cancel hc0 hct]
      _ = c⁻¹ • (c • psi hf νH n x) := (smul_smul _ _ _).symm
      _ = c⁻¹ • (νU x).restrict (S_U hf n x) := by rw [h1]
  exact ⟨c⁻¹, lt_of_le_of_ne zero_le (Ne.symm (ENNReal.inv_ne_zero.mpr hct)),
    ENNReal.inv_ne_top.mpr hc0, hmain⟩

end

end Work.EKLRelProduct
