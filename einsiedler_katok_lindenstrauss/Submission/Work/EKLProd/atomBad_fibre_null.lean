import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLProd.prodFlower_nuU_fibre
import Submission.Work.EKLProd.prodFlower_fibre_cov
import Submission.Work.EKLRelProduct.psiEqNuU
import Submission.Work.EKLRelProduct.uSide
import Submission.Work.EKLRelProduct.psiNu_uMargEqPsiMap
import Submission.Work.EKLRelProduct.uAvg_eq
import Submission.Work.EKLRelCross.SL3criterion
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLC6Core.shape_mass_pos

/-!
# `Work.EKLProd.atomBad_fibre_null`

The bad set `atomBad` of the `(8.12c)` identification is invisible for the `H`-leafwise
measure along the `H`-shape of every product-box flower.

The mathematical content is the combination of the two halves of Pisa (8.12c) already
formalised in this directory:

* `Work.EKLProd.prodFlower_nuU_fibre` identifies, for `(μ.restrict (Z n))`-a.e. base point `x`
  and `νH x`-a.e. `h` in the `H`-shape, the (8.12c)-translate of the `U`-leafwise measure at
  `h • x` with the `U`-marginal of the plaquette measure of the *base point* `x`;
* `Work.EKLProd.prodFlower_fibre_cov` shows that the plaquette measure is `νH x`-invariant along
  the shape up to a constant, so the `U`-marginal of the plaquette measure at `h • x` is
  proportional to the one at `x`.

Putting the two together, for `νH x`-a.e. `h` in the shape the two measures `atomShU` and
`atomMargU` are proportional, so the countable criterion `SL3Criterion` holds
(`SL3Criterion_of_smul` below, which needs no local finiteness) and `atomBad` is false at
`h • x`.  The pointwise statement transfers to the measure-theoretic one by `ae_iff`,
`ae_restrict_iff'` and `Measure.restrict_apply'`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- **Proportionality implies the countable criterion** — the easy direction of
`Work.EKLRelCross.SL3criterion`, without any local finiteness hypothesis: only `m1 ≠ 0` is
needed, in order to find a member of the π-system `SL3fam` carrying positive `m1`-mass. -/
private lemma SL3Criterion_of_smul {m1 m2 : MeasureTheory.Measure Work.EKLContract.SL3}
    {c : ENNReal} (hc : c ≠ 0) (h1nz : m1 ≠ 0) (h : m2 = c • m1) :
    Work.EKLRelCross.SL3Criterion m1 m2 := by
  have huniv : m1 Set.univ ≠ 0 := MeasureTheory.Measure.measure_univ_ne_zero.mpr h1nz
  obtain ⟨n, hn⟩ := MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null
    (s := fun n : ℕ => Work.EKLRelCross.SL3fam (n, ∅))
    (by rwa [Work.EKLRelCross.iUnion_SL3fam_empty])
  refine ⟨(n, ∅), hn, ?_, ?_⟩
  · rw [h, MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos hc (ne_of_gt hn)
  · intro p
    rw [h, MeasureTheory.Measure.smul_apply, smul_eq_mul,
      MeasureTheory.Measure.smul_apply, smul_eq_mul]
    ring

/-- The `(8.12c)`-translate `atomShU` of the `U`-leafwise measure, written with the conjugated
coordinate map of `Work.EKLRelProduct.uShift` spelled out. -/
private lemma atomShU_eq_map_conj {H T U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (y : Work.EKLContract.X3) :
    atomShU hf n νU y = ((νU y).map (fun u : Work.EKLContract.SL3 =>
      (hT T U (hf.co n y))⁻¹ * u * (hT T U (hf.co n y)) * (hU T U (hf.co n y)))).restrict
        (V hf.R ∩ (U : Set Work.EKLContract.SL3)) := by
  have hfun : (fun u : Work.EKLContract.SL3 =>
        Work.EKLRelProduct.gconj (hT T U (hf.co n y))⁻¹ u * (hU T U (hf.co n y)))
      = (fun u : Work.EKLContract.SL3 =>
          (hT T U (hf.co n y))⁻¹ * u * (hT T U (hf.co n y)) * (hU T U (hf.co n y))) := by
    funext u
    simp only [Work.EKLRelProduct.gconj]
    rw [inv_inv]
  rw [atomShU, Work.EKLRelProduct.uShift, hfun]

/-- The `U`-marginal `atomMargU` is `SL3`-equivariant up to a constant: the `(T,U)`-joint law of
the plaquette measure at `h • x` is a multiple of the one at `x` (`prodFlowerΛTP`), and taking
the second marginal and restricting commutes with scaling. -/
private lemma atomMargU_smul {H T U : Subgroup Work.EKLContract.SL3}
    {μ : MeasureTheory.Measure Work.EKLContract.X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    {x : Work.EKLContract.X3} {h : Work.EKLContract.SL3} {c : ENNReal}
    (hc : prodFlowerΛTP hf n νH (h • x) = c • prodFlowerΛTP hf n νH x) :
    atomMargU hf n νH (h • x) = c • atomMargU hf n νH x := by
  rw [atomMargU, atomMargU, hc, MeasureTheory.Measure.map_smul,
    MeasureTheory.Measure.restrict_smul] <;> try fun_prop

/-- Scaling bookkeeping: if `A = c • M` and `D = c' • M` with `0 < c < ⊤`, then
`D = (c' * c⁻¹) • A`. -/
private lemma smul_of_eq_smul_of_eq_smul {A D M : MeasureTheory.Measure Work.EKLContract.SL3}
    {c c' : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hA : A = c • M) (hD : D = c' • M) :
    D = (c' * c⁻¹) • A := by
  have hM : M = c⁻¹ • A := by
    rw [hA, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  rw [hD, hM, smul_smul]

theorem atomBad_fibre_null (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise)
    (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ)
    {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H)
    (hT : Work.EKLContract.IsHoro T) (hU : Work.EKLContract.IsHoro U)
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH)
    {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT)
    {νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XU : Set Work.EKLContract.X3} (hνU : Work.EKLContract.IsLeafwise μ U νU XU)
    (t : Fin 3 → ℝ)
    (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹)
      Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂(μ.restrict (hf.Z n)),
      (νH x) {h : Work.EKLContract.SL3 | h ∈ Work.EKLContract.shape (hf.mH n) H x ∧
        h • x ∈ Work.EKLProd.atomBad hf n XH XU νH νU} = 0 := by
  classical
  -- the two halves of (8.12c)
  have hfib := prodFlower_nuU_fibre hX3 hLeaf hBirk hmu hH hT hU hTH hUH hnorm hcop hdisj hf
    hνH hνT hνU n t hcent hcontr
  have hcov := prodFlower_fibre_cov hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj hf hνH n
  have hZmeas : MeasurableSet (hf.Z n) := (hf.plaqH n).1 (hf.Z n) (hf.plaqH n).2.2.1
  filter_upwards [hfib, hcov, MeasureTheory.ae_restrict_mem hZmeas] with x hfx hcx hxZ
  -- the `H`-shape is measurable
  have hSmeas : MeasurableSet (Work.EKLContract.shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOsh]
    exact hOo.measurableSet.inter hH.1.measurableSet
  -- ## the two a.e. proportionalities, read on the restricted measure
  have hA : ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        atomShU hf n νU (h • x) = c • atomMargU hf n νH x := by
    filter_upwards [hfx] with h hh
    obtain ⟨c, hc0, hct, hceq⟩ := hh
    exact ⟨c, hc0, hct, by rw [atomShU_eq_map_conj]; exact hceq⟩
  have hB : ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        prodFlowerΛTP hf n νH (h • x) = c • prodFlowerΛTP hf n νH x := hcx
  -- ## pointwise: `atomBad` is false wherever the two proportionalities hold
  have hae : ∀ᵐ h ∂((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x)),
      ¬ (h • x ∈ Work.EKLProd.atomBad hf n XH XU νH νU) := by
    filter_upwards [hA, hB] with h hhA hhB
    intro hbad
    obtain ⟨_hyZ, _hyH, _hyU, hshUne, _hmargUne, hnotcrit⟩ := hbad
    obtain ⟨c, hc0, hct, hAc⟩ := hhA
    obtain ⟨c', hc'0, _hc't, hBc⟩ := hhB
    have hD : atomMargU hf n νH (h • x) = (c' * c⁻¹) • atomShU hf n νU (h • x) :=
      smul_of_eq_smul_of_eq_smul hc0 hct hAc (atomMargU_smul hf n νH hBc)
    exact hnotcrit (SL3Criterion_of_smul (ENNReal.mul_pos hc'0 (ENNReal.inv_ne_zero.mpr hct)).ne'
      hshUne hD)
  -- ## transfer to the measure-theoretic statement
  have hgoal0 : ((νH x).restrict (Work.EKLContract.shape (hf.mH n) H x))
      {h : Work.EKLContract.SL3 | ¬ ¬ (h • x ∈ Work.EKLProd.atomBad hf n XH XU νH νU)} = 0 :=
    MeasureTheory.ae_iff.mp hae
  have hset : {h : Work.EKLContract.SL3 |
        ¬ ¬ (h • x ∈ Work.EKLProd.atomBad hf n XH XU νH νU)}
      = {h : Work.EKLContract.SL3 | h • x ∈ Work.EKLProd.atomBad hf n XH XU νH νU} := by
    ext h
    simp
  rw [hset] at hgoal0
  rw [MeasureTheory.Measure.restrict_apply' hSmeas] at hgoal0
  rw [Set.inter_comm] at hgoal0
  exact hgoal0

end Work.EKLProd
