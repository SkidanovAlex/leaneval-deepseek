import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelProduct.measurable_hT_hU_pair

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

namespace Work.EKLProd

open Work.EKLContract

/-! Route (for the prover).

Write `M := (νH x).restrict (shape (hf.mH n) H x)`, `a := M univ = (νH x) (shape (hf.mH n) H x)`
(note `M` is a restriction, so `M univ` is that mass) and `σ := (prodFlowerΛTP hf n νH x).map Prod.snd`.

* `prodFlowerΛTP hf n νH x = M.map (fun w => (hT T U (w * hf.co n x), hU T U (w * hf.co n x)))`
  (unfold `prodFlowerΛTP`, `prodFlowerΛ`; compositions of `Measure.map`). The map is measurable:
  `(w ↦ (hT T U w, hU T U w))` is `Work.EKLRelProduct.measurable_hT_hU_pair`, and
  `w ↦ w * hf.co n x` is continuous. Hence `mass(prodFlowerΛTP) = a`.
* Similarly `mass σ = a` (`Prod.snd` measurable, total mass preserved by pushforward).
* If `prodFlowerκ hf n νT x = 0` then `hP1` gives `prodFlowerΛTP = 0.prod σ = 0`
  (`Measure.zero_prod`), contradicting `mass = a > 0` (`hmass.1`). Hence `prodFlowerκ ≠ 0`.
* By definition `prodFlowerκ hf n νT x = D⁻¹ • ((νT x).map (· * t)).restrict (V hf.R ∩ T)` with
  `t = hT T U (hf.co n x)` and `D = ((νT x).map (· * t)) (V hf.R ∩ T)`. Its mass is
  `D⁻¹ * D ≠ 0`; if `D = 0` then the measure in the scalar product is `0` so the result is `0`,
  and if `D = ⊤` then `D⁻¹ = 0` and the result is `0` — both contradict `prodFlowerκ ≠ 0`.
  So `0 < D` and `D ≠ ⊤`.
* Finally `D = (νT x) (S_T hf n x)`, because `S_T hf n x = (fun g => g * t) ⁻¹' (V hf.R ∩ T)`
  (definition of `S_T`; the two sets are equal by `Set.ext`/`rfl`-style unfolding).

`Measure.map_apply`/`Measure.map_apply_of_aemeasurable` on `univ` gives the total masses. -/
theorem S_T_mass_pos_and_lt_top_of_P1 {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {x : Work.EKLContract.X3} (hxZ : x ∈ hf.Z n)
    (hmass : 0 < (νH x) (Work.EKLContract.shape (hf.mH n) H x) ∧
      (νH x) (Work.EKLContract.shape (hf.mH n) H x) < ⊤)
    (hP1 : Work.EKLProd.prodFlowerΛTP hf n νH x =
      (Work.EKLProd.prodFlowerκ hf n νT x).prod
        ((Work.EKLProd.prodFlowerΛTP hf n νH x).map Prod.snd)) :
    0 < (νT x) (Work.EKLRelProduct.S_T hf n x) ∧
      (νT x) (Work.EKLRelProduct.S_T hf n x) < ⊤ := by
  classical
  have hφ : Measurable (fun w : SL3 => (hT T U w, hU T U w)) :=
    Work.EKLRelProduct.measurable_hT_hU_pair hTH hUH hnorm hcop hdisj hHc hTc hUc
  -- the total mass of the joint law `ΛTP` is the mass of the `H`-plaque measure
  have hmassTP : prodFlowerΛTP hf n νH x Set.univ = (νH x) (shape (hf.mH n) H x) := by
    rw [prodFlowerΛTP, prodFlowerΛ, Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ,
      Measure.map_apply (continuous_mul_const (hf.co n x)).measurable MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  -- if the normalised `T`-marginal `κ` vanished, `hP1` would force `ΛTP = 0`
  have hmassκ : (prodFlowerκ hf n νT x) Set.univ ≠ 0 := by
    intro h0
    haveI : IsFiniteMeasure (prodFlowerΛTP hf n νH x) := ⟨by rw [hmassTP]; exact hmass.2⟩
    haveI : IsFiniteMeasure ((prodFlowerΛTP hf n νH x).map Prod.snd) :=
      Measure.isFiniteMeasure_map _ _
    have hle := Measure.prod_prod_le (μ := prodFlowerκ hf n νT x)
      (ν := (prodFlowerΛTP hf n νH x).map Prod.snd) Set.univ Set.univ
    rw [Set.univ_prod_univ, h0, zero_mul] at hle
    have h2 : prodFlowerΛTP hf n νH x Set.univ ≤ 0 := by rw [hP1]; exact hle
    rw [hmassTP] at h2
    exact absurd hmass.1 (not_lt_of_ge h2)
  -- the mass of `κ` is `D⁻¹ * D`, `D` the mass of the translated `T`-ball
  have hκuniv : (prodFlowerκ hf n νT x) Set.univ
      = (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
          (V hf.R ∩ (T : Set SL3)))⁻¹
        * (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
          (V hf.R ∩ (T : Set SL3))) := by
    rw [prodFlowerκ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter]
  -- hence `D ≠ 0` and `D ≠ ⊤`
  have hDne : (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
          (V hf.R ∩ (T : Set SL3))) ≠ 0 ∧
      (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
          (V hf.R ∩ (T : Set SL3))) ≠ ⊤ := by
    constructor
    · intro h0
      exact hmassκ (by rw [hκuniv, h0, ENNReal.inv_zero, mul_zero])
    · intro htop
      exact hmassκ (by rw [hκuniv, htop, ENNReal.inv_top, zero_mul])
  -- that mass is the `νT x`-mass of the source set `S_T`
  have hST : (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
          (V hf.R ∩ (T : Set SL3))) = (νT x) (Work.EKLRelProduct.S_T hf n x) := by
    rw [Measure.map_apply (continuous_mul_const (hT T U (hf.co n x))).measurable
      ((Work.EKLComp.isOpen_V hf.R).measurableSet.inter hTc.measurableSet)]
    rfl
  exact ⟨hST ▸ (pos_iff_ne_zero.mpr hDne.1), hST ▸ (lt_top_iff_ne_top.mpr hDne.2)⟩


end Work.EKLProd
