import Mathlib
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair
import Submission.Work.EKLProd.ProdFlowerLemmas

namespace Work.EKLRelProduct

open MeasureTheory Work.EKLContract Work.EKLProd

/-- The group-theoretic identity behind the reparametrisation of the `U`-marginal: for `a, b ∈ H`,
writing `a = tₐ uₐ`, `b = t_b u_b` for the chosen `T`-`U` decompositions, the `U`-part of the
product `a * b = (tₐ t_b) · ((t_b⁻¹ uₐ t_b) u_b)` is `t_b⁻¹ * uₐ * t_b * u_b = shiftMap t_b u_b uₐ`. -/
private theorem hU_mul_eq_shiftMap_aux {H T U : Subgroup SL3}
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {a b : SL3} (ha : a ∈ H) (hb : b ∈ H) :
    hU T U (a * b) = shiftMap (hT T U b) (hU T U b) (hU T U a) := by
  have hexa : ∃ g ∈ T, ∃ u ∈ U, a = g * u := hcop a ha
  have hexb : ∃ g ∈ T, ∃ u ∈ U, b = g * u := hcop b hb
  have hdeca : hT T U a * hU T U a = a := hT_mul_hU hexa
  have hdecb : hT T U b * hU T U b = b := hT_mul_hU hexb
  have htaT : hT T U a ∈ T := hT_mem hexa
  have htbT : hT T U b ∈ T := hT_mem hexb
  have hubU : hU T U b ∈ U := hU_mem hexb
  have hconjU : ((hT T U b)⁻¹ * hU T U a) * hT T U b ∈ U := by
    have h := hnorm (hT T U b)⁻¹ (T.inv_mem htbT) (hU T U a) (hU_mem hexa)
    simpa using h
  have hbU : shiftMap (hT T U b) (hU T U b) (hU T U a) ∈ U := by
    unfold shiftMap
    exact U.mul_mem hconjU hubU
  have hkey : (hT T U a * hT T U b) * shiftMap (hT T U b) (hU T U b) (hU T U a)
      = a * b := by
    calc (hT T U a * hT T U b) * shiftMap (hT T U b) (hU T U b) (hU T U a)
        = hT T U a * (hT T U b * shiftMap (hT T U b) (hU T U b) (hU T U a)) := by
          rw [mul_assoc]
      _ = hT T U a * (hU T U a * (hT T U b * hU T U b)) := by
          rw [← shiftMap_mul]
      _ = hT T U a * (hU T U a * b) := by rw [hdecb]
      _ = (hT T U a * hU T U a) * b := by rw [mul_assoc]
      _ = a * b := by rw [hdeca]
  exact hU_eq_of_factor hdisj (T.mul_mem htaT htbT) hbU hkey

/-- **The `U`-marginal `uMarg` is `psi` reparametrised by `shiftMap`.** For `y ∈ hf.Z n`,

`uMarg hf νH n y = (psi hf νH n y).map (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)))`.

Route: `uMarg hf νH n y = ((νH y)|_{shape (mH n) H y}).map (w ↦ hU T U (hf.co n (w • y)))` and
`psi hf νH n y = ((νH y)|_{shape (mH n) H y}).map (w ↦ hU T U w)`. For `w ∈ shape (mH n) H y`
one has `w ∈ H`, `hf.co n (w • y) = w * hf.co n y` (`hf.co_smul`), and — writing
`w = t_w u_w`, `hf.co n y = t_y u_y` with the decompositions from `hcop`, and using `hnorm` —
`hU T U (w * hf.co n y) = t_y⁻¹ * u_w * t_y * u_y`, which is exactly
`shiftMap t_y u_y (hU T U w)` (`shiftMap t u₀ g = t⁻¹ * g * t * u₀`). Hence the two maps
agree `(νH y)|_{shape}`-a.e. (`Measure.map_congr`), and `Measure.map_map`
(with `Measurable (fun w => hU T U w)`, obtained from the PROVED
`Work.EKLRelProduct.measurable_hT_hU_pair` by `Measurable.snd`) finishes. -/
theorem psiNu_uMargEqPsiMap {H T U : Subgroup Work.EKLContract.SL3} {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) {y : Work.EKLContract.X3} (hy : y ∈ hf.Z n) :
    Work.EKLRelProduct.uMarg hf νH n y
      = (Work.EKLRelProduct.psi hf νH n y).map
          (Work.EKLRelProduct.shiftMap (Work.EKLProd.hT T U (hf.co n y)) (Work.EKLProd.hU T U (hf.co n y))) := by
  classical
  -- the shape is measurable, being `O ∩ H` with `O` open and `H` closed
  have hSymeas : MeasurableSet (shape (hf.mH n) H y) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 y hy).2.2.1
    rw [hOsh]; exact hOo.measurableSet.inter hHc.measurableSet
  have hcoH : hf.co n y ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n y hy)
  -- the pointwise identity on the shape
  have hpt : ∀ w ∈ shape (hf.mH n) H y,
      hU T U (hf.co n (w • y))
        = shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) (hU T U w) := by
    intro w hw
    rw [hf.co_smul n y hy w hw.1 hw.2]
    exact hU_mul_eq_shiftMap_aux hnorm hcop hdisj hw.1 hcoH
  -- hence the two maps of the two pushforwards agree a.e.
  have hae : (fun w : SL3 => hU T U (hf.co n (w • y)))
      =ᵐ[(νH y).restrict (shape (hf.mH n) H y)]
      (fun w : SL3 => shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y)) (hU T U w)) := by
    filter_upwards [ae_restrict_mem hSymeas] with w hw
    exact hpt w hw
  have hUmeas : Measurable (fun w : SL3 => hU T U w) :=
    measurable_snd.comp (measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc)
  have hsmeas : Measurable (shiftMap (hT T U (hf.co n y)) (hU T U (hf.co n y))) :=
    (measurableEmbedding_shiftMap _ _).measurable
  rw [uMarg, psi, Measure.map_map hsmeas hUmeas]
  exact Measure.map_congr hae

end Work.EKLRelProduct
