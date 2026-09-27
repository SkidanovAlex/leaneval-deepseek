import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.prodFlower_nuT_class
import Submission.Work.EKLC6Core.shape_mass_pos

namespace Work.EKLProd

open MeasureTheory Work.EKLContract
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

/-- The atom of a σ-algebra is antitone in the σ-algebra. -/
theorem atom_subset {m₁ m₂ : MeasurableSpace X3} (h : m₁ ≤ m₂) (x : X3) :
    atom m₂ x ⊆ atom m₁ x := by
  rw [atom, atom]
  refine Set.sInter_subset_sInter ?_
  rintro s ⟨hs, hxs⟩
  exact ⟨MeasurableSpace.le_def.mp h s hs, hxs⟩

/-- Pointwise computation inside a `T`-strip of a product-box flower: for `r` in the `T`-ball
`V R ∩ T`, the `T`-part of the coordinate at the translate `(r γ⁻¹) • z` is `r`, where
`γ = hT T U (co n z)` is the `T`-part of the coordinate of `z`. -/
theorem prodFlower_co_box {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    {z : X3} (hz : z ∈ hf.Z n) {r : SL3} (hr : r ∈ V hf.R ∩ (T : Set SL3)) :
    hT T U (hf.co n ((r * (hT T U (hf.co n z))⁻¹) • z)) = r := by
  have hcoH : hf.co n z ∈ (H : Set SL3) := prodBox_subset_H hTH hUH (hf.co_mem n z hz)
  have hdec : ∃ a ∈ T, ∃ b ∈ U, hf.co n z = a * b := by
    obtain ⟨a, ha, b, hb, hab⟩ := hf.co_mem n z hz
    exact ⟨a, ha.2, b, hb.2, hab.symm⟩
  have hγT : hT T U (hf.co n z) ∈ T := hT_mem hdec
  have huT : r * (hT T U (hf.co n z))⁻¹ ∈ T := T.mul_mem hr.2 (T.inv_mem hγT)
  have hushape : r * (hT T U (hf.co n z))⁻¹ ∈ shape (hf.mT n) T z := by
    rw [prodFlower_shapeT_eq hTH hUH hcop hdisj hf n hz]
    exact ⟨r, hr, rfl⟩
  have hatomH : (r * (hT T U (hf.co n z))⁻¹) • z ∈ atom (hf.mH n) z :=
    atom_subset (hf.alignT n) z hushape.2
  rw [hf.co_smul n z hz (r * (hT T U (hf.co n z))⁻¹) (hTH huT) hatomH]
  rw [hT_mul_left hTH hcop hdisj huT hcoH]
  group

/-- The `ν`-mass of the `T`-shape of a product-box flower is the `ν`-mass of the `T`-ball,
transported by right translation with the `T`-part of the coordinate. -/
theorem prodFlower_slice_den {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (hTcl : IsClosed (T : Set SL3)) {z : X3} (hz : z ∈ hf.Z n) (ν : MeasureTheory.Measure SL3) :
    ν (shape (hf.mT n) T z)
      = (ν.map (fun r : SL3 => r * (hT T U (hf.co n z)))) (V hf.R ∩ (T : Set SL3)) := by
  have hBmeas : MeasurableSet (V hf.R ∩ (T : Set SL3)) :=
    (Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1.measurableSet.inter hTcl.measurableSet
  have hpre : (fun r : SL3 => r * (hT T U (hf.co n z))) ⁻¹' (V hf.R ∩ (T : Set SL3))
      = shape (hf.mT n) T z := by
    rw [prodFlower_shapeT_eq hTH hUH hcop hdisj hf n hz, Set.image_mul_right]
    simp
  rw [← hpre, ← Measure.map_apply (measurable_mul_const _) hBmeas]

/-- The `ν`-integral over the `T`-shape of a product-box flower of the `A`-indicator of the
`T`-part of the coordinate equals the `A ∩ (V R ∩ T)`-mass of the transported measure. -/
theorem prodFlower_slice_num {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (hTcl : IsClosed (T : Set SL3)) {A : Set SL3} (hA : MeasurableSet A)
    {z : X3} (hz : z ∈ hf.Z n) (ν : MeasureTheory.Measure SL3) :
    ∫ s in shape (hf.mT n) T z, A.indicator (fun _ => (1 : ℝ))
        (hT T U (hf.co n (s • z))) ∂ν
      = ((ν.map (fun r : SL3 => r * (hT T U (hf.co n z))))
          (A ∩ (V hf.R ∩ (T : Set SL3)))).toReal := by
  have hc : Measurable (fun s : SL3 => hT T U (hf.co n (s • z))) :=
    (hf.meas_tp n).comp (continuous_id.smul continuous_const).measurable
  have hstep := setIntegral_indicator_comp_eq_toReal (ν := ν) hc hA (shape (hf.mT n) T z)
  rw [hstep]
  have hBmeas : MeasurableSet (V hf.R ∩ (T : Set SL3)) :=
    (Lemmas.V_open_one hf.R (by linarith [hf.one_le_R])).1.measurableSet.inter hTcl.measurableSet
  have hAB : MeasurableSet (A ∩ (V hf.R ∩ (T : Set SL3))) := hA.inter hBmeas
  have hset : shape (hf.mT n) T z ∩ (fun s : SL3 => hT T U (hf.co n (s • z))) ⁻¹' A
      = (fun r : SL3 => r * (hT T U (hf.co n z))⁻¹) '' (A ∩ (V hf.R ∩ (T : Set SL3))) := by
    rw [prodFlower_shapeT_eq hTH hUH hcop hdisj hf n hz]
    ext s
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hsA⟩
      have hsA' : hT T U (hf.co n ((r * (hT T U (hf.co n z))⁻¹) • z)) ∈ A := by
        simpa only [Set.mem_preimage] using hsA
      rw [prodFlower_co_box hTH hUH hcop hdisj hf n hz hr] at hsA'
      exact ⟨r, ⟨hsA', hr⟩, rfl⟩
    · rintro ⟨r, ⟨hrA, hr⟩, rfl⟩
      refine ⟨⟨r, hr, rfl⟩, ?_⟩
      show hT T U (hf.co n ((r * (hT T U (hf.co n z))⁻¹) • z)) ∈ A
      rw [prodFlower_co_box hTH hUH hcop hdisj hf n hz hr]
      exact hrA
  congr 1
  rw [hset, Set.image_mul_right, inv_inv]
  rw [← Measure.map_apply (measurable_mul_const _) hAB]

/-- Pushing a measure forward by right translation commutes with the `T`-part cancellation. -/
theorem map_mul_smul_map_mul {ν0 ν : MeasureTheory.Measure SL3} {c : ENNReal} {a b : SL3}
    (h : ν = c • ν0.map (fun r => r * a)) :
    ν.map (fun r => r * b) = c • ν0.map (fun r => r * (a * b)) := by
  rw [h, Measure.map_smul, Measure.map_map (measurable_mul_const b) (measurable_mul_const a)] <;> try fun_prop
  rw [show (fun r : SL3 => r * b) ∘ (fun r : SL3 => r * a)
      = (fun r : SL3 => r * (a * b)) from by
    funext r
    simp only [Function.comp_apply]
    rw [mul_assoc]]

/-- A common non-zero scaling cancels in a ratio of `ℝ≥0∞`-masses. -/
theorem ratio_cancel {c X Y : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    ((c • X).toReal) / ((c • Y).toReal) = X.toReal / Y.toReal := by
  rw [smul_eq_mul, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul]
  exact mul_div_mul_left _ _ (ne_of_gt (ENNReal.toReal_pos hc0 hct))

/-- The pointwise (fibre-independence) form of `prodFlower_slice_avg`: assuming the covariance
of `νT` along the `H`-shape (the conclusion of `prodFlower_nuT_class`), the `νT`-slice average
at `h • x` equals the fixed expression at `x`. -/
theorem prodFlower_slice_avg_pt {H T U : Subgroup SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure X3} (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (hTcl : IsClosed (T : Set SL3)) {A : Set SL3} (hA : MeasurableSet A)
    {νT : X3 → MeasureTheory.Measure SL3} {x : X3} (hx : x ∈ hf.Z n)
    {h : SL3} (hh : h ∈ shape (hf.mH n) H x)
    (hcov : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      νT (h • x) = c • (νT x).map (fun g => g * (hT T U h)⁻¹)) :
    (∫ s in shape (hf.mT n) T (h • x),
        A.indicator (fun _ => (1 : ℝ)) (hT T U (hf.co n (s • (h • x)))) ∂(νT (h • x)))
      / ((νT (h • x)) (shape (hf.mT n) T (h • x))).toReal
    = (((νT x).map (fun g : SL3 => g * (hT T U (hf.co n x))))
        (A ∩ (V hf.R ∩ (T : Set SL3)))).toReal
      / (((νT x).map (fun g : SL3 => g * (hT T U (hf.co n x))))
        (V hf.R ∩ (T : Set SL3))).toReal := by
  have hzZ : h • x ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hx).1 hh.2
  have hden := prodFlower_slice_den hTH hUH hcop hdisj hf n hTcl hzZ (νT (h • x))
  have hnum := prodFlower_slice_num hTH hUH hcop hdisj hf n hTcl hA hzZ (νT (h • x))
  rw [hnum, hden]
  obtain ⟨c, hc0, hct, hceq⟩ := hcov
  have hco : hf.co n (h • x) = h * hf.co n x := hf.co_smul n x hx h hh.1 hh.2
  have hcancel : (hT T U h)⁻¹ * (hT T U (hf.co n (h • x))) = hT T U (hf.co n x) := by
    rw [hco]
    exact prodFlower_tpart_cancel hTH hUH hnorm hcop hdisj hf n hx hh
  have hmap : (νT (h • x)).map (fun r : SL3 => r * (hT T U (hf.co n (h • x))))
      = c • (νT x).map (fun r : SL3 => r * (hT T U (hf.co n x))) := by
    have h1 := map_mul_smul_map_mul (ν := νT (h • x)) (ν0 := νT x) (c := c)
      (b := hT T U (hf.co n (h • x))) hceq
    rw [h1, hcancel]
  rw [hmap, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
  exact ratio_cancel hc0 hct

theorem prodFlower_slice_avg (hX3 : Work.EKLContract.P_X3) (hLeaf : Work.EKLContract.P_Leafwise) (hBirk : Work.EKLContract.P_Birkhoff) {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] (hmu : Work.EKLContract.IsAInvariant μ) {H T U : Subgroup Work.EKLContract.SL3} (hH : Work.EKLContract.IsHoro H) (hT : Work.EKLContract.IsHoro T) (hTH : T ≤ H) (hUH : U ≤ H) (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1) (hf : Work.EKLProd.ProdFlowerFam H T U μ) {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) (n : ℕ) (t : Fin 3 → ℝ) (hcent : ∀ g ∈ T, Work.EKLContract.aDiag t * g = g * Work.EKLContract.aDiag t) (hcontr : ∀ u ∈ U, Filter.Tendsto (fun k : ℕ => Work.EKLContract.aDiag t ^ k * u * (Work.EKLContract.aDiag t ^ k)⁻¹) Filter.atTop (nhds 1)) {A : Set Work.EKLContract.SL3} (hA : MeasurableSet A) : ∀ᵐ x ∂(μ.restrict (hf.Z n)), ∀ᵐ h ∂(νH x).restrict (Work.EKLContract.shape (hf.mH n) H x), (∫ s in Work.EKLContract.shape (hf.mT n) T (h • x), A.indicator (fun _ => (1 : ℝ)) (Work.EKLProd.hT T U (hf.co n (s • (h • x)))) ∂(νT (h • x))) / ((νT (h • x)) (Work.EKLContract.shape (hf.mT n) T (h • x))).toReal = (((νT x).map (fun g : Work.EKLContract.SL3 => g * (Work.EKLProd.hT T U (hf.co n x)))) (A ∩ (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3)))).toReal / (((νT x).map (fun g : Work.EKLContract.SL3 => g * (Work.EKLProd.hT T U (hf.co n x)))) (Work.EKLContract.V hf.R ∩ (T : Set Work.EKLContract.SL3))).toReal := by
  have hZmeas : MeasurableSet (hf.Z n) :=
    (MeasurableSpace.le_def.mp (hf.plaqH n).1) (hf.Z n) (hf.plaqH n).2.2.1
  filter_upwards [prodFlower_nuT_class hX3 hLeaf hBirk hmu hH hT hTH hUH hnorm hcop hdisj
      hf hνH hνT n t hcent hcontr, MeasureTheory.ae_restrict_mem hZmeas]
    with x hxbad hxZ
  have hP' : ∀ᵐ h ∂(νH x), h ∈ shape (hf.mH n) H x →
      (∀ g ∈ T, g⁻¹ * h ∈ U → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        νT (h • x) = c • (νT x).map (fun g' => g' * g⁻¹)) := by
    have hgood : ∀ᵐ h ∂(νH x),
        ¬(h ∈ shape (hf.mH n) H x ∧ ¬(∀ g ∈ T, g⁻¹ * h ∈ U → ∃ c : ENNReal,
          c ≠ 0 ∧ c ≠ ⊤ ∧ νT (h • x) = c • (νT x).map (fun g' => g' * g⁻¹))) := by
      apply MeasureTheory.ae_iff.mpr
      refine measure_mono_null ?_ hxbad
      intro h hh
      by_contra hcon
      exact hh hcon
    refine Filter.Eventually.mono hgood ?_
    intro h hh hS
    by_contra hq
    exact hh ⟨hS, hq⟩
  have hSmeas : MeasurableSet (shape (hf.mH n) H x) := by
    obtain ⟨O, hOo, hOsh⟩ := ((hf.plaqH n).2.2.2 x hxZ).2.2.1
    rw [hOsh]
    exact hOo.measurableSet.inter hH.1.measurableSet
  rw [MeasureTheory.ae_restrict_iff' hSmeas]
  refine Filter.Eventually.mono hP' ?_
  intro h hPh hS
  obtain ⟨g, hgT, u, huU, hgu⟩ := hcop h hS.1
  have hdec : Work.EKLProd.hT T U h * Work.EKLProd.hU T U h = h :=
    hT_mul_hU ⟨g, hgT, u, huU, hgu⟩
  have hpart : (Work.EKLProd.hT T U h)⁻¹ * h ∈ U := by
    have h1 : (Work.EKLProd.hT T U h)⁻¹ * h = Work.EKLProd.hU T U h := by
      have h3 := (congrArg (fun x : SL3 => (Work.EKLProd.hT T U h)⁻¹ * x) hdec).symm
      rw [h3]
      group
    rw [h1]
    exact hU_mem ⟨g, hgT, u, huU, hgu⟩
  exact prodFlower_slice_avg_pt (νT := νT) (x := x) hTH hUH hnorm hcop hdisj hf n hT.1 hA
    hxZ hS (hPh hS (Work.EKLProd.hT T U h) (hT_mem ⟨g, hgT, u, huU, hgu⟩) hpart)

end

end Work.EKLProd
