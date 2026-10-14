import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzTools.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two interface statements -/

/-- **Interface (1): Carathéodory measurability in `(s,θ)`.**  For a measurable `s`-set `A` and a
function `g` that is, for each `s ∈ A`, continuous in `θ` on the open interval and zero off it,
and whose `s`-slices are a.e. strongly measurable, the uncurried `g` is a.e. strongly measurable
for `(volume.restrict A).prod volume`. -/
def CarathTheta : Prop :=
  ∀ {A : Set ℝ}, MeasurableSet A → ∀ {g : ℝ → ℝ → ℝ},
    (∀ s ∈ A, ContinuousOn (fun θ : ℝ => g s θ) (Set.Ioo 0 (Real.pi / 2))) →
    (∀ s ∈ A, ∀ θ : ℝ, θ ∉ Set.Ioo 0 (Real.pi / 2) → g s θ = 0) →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), AEStronglyMeasurable (fun s : ℝ => g s θ)
      (volume.restrict A)) →
    AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2) ((volume.restrict A).prod volume)

/-- **Interface (2): the exchange identity** `D_z^j D_θ^i (∫_s H s) = ∫_s D_z^j D_θ^i (H s)`,
with the measurability hypothesis restricted to the orders `≤ n`. -/
def ExchMixed : Prop :=
  ∀ {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ},
    a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T → a ≤ b → 0 ≤ C →
    (∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s)) →
    (∀ (j i : ℕ), j + i ≤ n → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T))) →
    (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (j i : ℕ), j + i ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) →
    (Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0) →
    {j i : ℕ} → j + i ≤ n →
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
        = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ

/-! ## Elementary helpers -/

/-- At `z = 0` the `ℋ^k`-integrand vanishes identically (all weights carry a factor `w 0 = 0`). -/
lemma HkIntegrand_fst_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
  simp

/-- The Bochner integral of a pointwise nonnegative function is dominated by the Lebesgue
integral of its `ofReal`-transform (the identity holds when the function is integrable, and
both sides collapse to `0 ≤ _` otherwise). -/
lemma ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : 0 ≤ f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall hf)]
  · rw [MeasureTheory.integral_undef h]
    simp

/-- The product of the restrictions to `Iz` and `Iθ` is the restriction of the planar measure
to the open quadrant (the two differ only by null coordinate lines). -/
lemma prod_restrict_Iz_Iθ_eq_Q0 :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict Work.FTS.EllipticEst.Q0 := by
  simp only [Work.Spaces.Iz, Work.Spaces.Iθ, Work.FTS.EllipticEst.Q0]
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Measure.restrict_congr_set ?_
  exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioi_ae_eq_Ici.symm
    MeasureTheory.Ioo_ae_eq_Icc.symm

/-- `θ ↦ sin(2θ)^c` is a.e. strongly measurable for the restriction to `Iθ`. -/
lemma sin_two_rpow_aesm_Iθ (c : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c)
      (volume.restrict Work.Spaces.Iθ) := by
  have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hIθ]
  have hc : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  refine (hc.rpow_const ?_).aestronglyMeasurable measurableSet_Ioo
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- `θ ↦ w z / sin(2θ)^{η/2}` is a.e. strongly measurable for the restriction to `Iθ`. -/
lemma wdivsin_aesm_Iθ (z : ℝ) :
    AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (volume.restrict Work.Spaces.Iθ) :=
  AEStronglyMeasurable.div₀ aestronglyMeasurable_const
    (sin_two_rpow_aesm_Iθ (Work.Spaces.eta / 2))

/-- `θ ↦ Wt α z θ` is a.e. strongly measurable for the restriction to `Iθ`. -/
lemma Wt_aesm_Iθ (α z : ℝ) :
    AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have h : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    funext fun θ => rfl
  rw [h]
  exact (sin_two_rpow_aesm_Iθ (-(Work.Spaces.gam α / 2))).const_mul _

/-- Lift an a.e. strongly measurable function of one variable to the product with the second
coordinate. -/
lemma aesm_comp_snd {μ ν : Measure ℝ} [SFinite ν] {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd

/-- Pointwise finite sums of a.e. strongly measurable functions are a.e. strongly measurable. -/
lemma aesm_finsetSum_apply {ι X : Type*} [MeasurableSpace X] {s : Finset ι}
    {f : ι → X → ℝ} {μ : Measure X} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a : X => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

/-- The open quadrant is conull for the product of the restrictions to `Iz` and `Iθ`. -/
lemma ae_mem_Q0 :
    ∀ᵐ q ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      q ∈ Work.FTS.EllipticEst.Q0 := by
  rw [prod_restrict_Iz_Iθ_eq_Q0]
  exact ae_restrict_mem Work.FTS.EllipticEst.isOpen_Q0.measurableSet

/-- The weight `Wt` is continuous on the open quadrant, hence its uncurried version is a.e.
strongly measurable for the product of the restricted measures. -/
lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      = fun q : ℝ × ℝ =>
        Work.Spaces.w q.1 * (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α / 2)) :=
    funext fun q => rfl
  rw [hfun]
  refine ContinuousOn.mul ?_ ?_
  · have h2 : (fun q : ℝ × ℝ => Work.Spaces.w q.1)
        = fun q : ℝ × ℝ => (1 + q.1) ^ 2 / q.1 ^ 2 := funext fun q => rfl
    rw [h2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun q hq => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hq).1)
  · have hc : ContinuousOn (fun q : ℝ × ℝ => Real.sin (2 * q.2))
        Work.FTS.EllipticEst.Q0 := by fun_prop
    refine hc.rpow_const ?_
    intro q hq
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hq
    exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [Real.pi_pos])))

lemma aesm_Wt_Q0 (α : ℝ) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_Wt_Q0 α)

lemma aesm_wdivsin_Q0 :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ Work.FTS.EllipticEst.continuousOn_wdivsin_Q0

/-! ## Joint measurability in `(s,θ)` at a fixed `z` -/

/-- For a fixed `z > 0`, the map `(s,θ) ↦ D_z^j D_θ^i (H s) z θ` is a.e. strongly measurable
for the product of the horizon measure with the restriction to `Iθ`. -/
lemma perz_aesm_slot {T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} (hcar : CarathTheta)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {z : ℝ} (hz : 0 < z) {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i (H p.1) z p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict Work.Spaces.Iθ)) := by
  classical
  set g : ℝ → ℝ → ℝ :=
    fun s θ => if θ ∈ Set.Ioo 0 (Real.pi / 2) then Work.Spaces.mixed j i (H s) z θ else 0
  have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hprod : (volume.restrict (Set.Icc (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      = (volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [hIθ]
  have hmain : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume) :=
    hcar measurableSet_Icc (g := g) ?_ ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
        ((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict Work.Spaces.Iθ)) :=
      hmain.mono_measure
        (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
    have h1' : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2)
        ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
          (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
      rw [hprod]
      exact h1
    rw [← hprod]
    refine h1'.congr ?_
    change ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo 0 (Real.pi / 2)))),
      g p.1 p.2 = Work.Spaces.mixed j i (H p.1) z p.2
    have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo 0 (Real.pi / 2)))), p.2 ∈ Set.Ioo 0 (Real.pi / 2) := by
      rw [Measure.ae_prod_iff_ae_ae
        (p := fun p : ℝ × ℝ => p.2 ∈ Set.Ioo 0 (Real.pi / 2))
        (measurableSet_Ioo.preimage measurable_snd)]
      refine Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hae] with p hp
    simp only [g]
    rw [ite_eq_left hp]
  · intro s hs
    have hcont0 : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((hsm s hs).mixed j i).continuousOn.comp
        ((continuous_const.prodMk continuous_id).continuousOn)
        (fun θ hθ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩)
    refine hcont0.congr ?_
    intro θ hθ
    simp only [g]
    rw [ite_eq_left hθ]
  · intro s hs θ hθ
    simp only [g]
    rw [ite_eq_right hθ]
  · intro θ hθ
    have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ⟩
    refine (hmeas j i hji z θ hzθ).congr ?_
    filter_upwards with s
    simp only [g]
    rw [ite_eq_left hθ]

/-- For a fixed `z > 0`, the map `(s,θ) ↦ HkIntegrand α k (H s) z θ` is a.e. strongly
measurable for the product of the horizon measure with the restriction to `Iθ`. -/
lemma perz_aesm_HkIntegrand {T : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hcar : CarathTheta)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {z : ℝ} (hz : 0 < z) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) z p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume.restrict Work.Spaces.Iθ)) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  set ν : Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hWt : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Wt α z p.2) (μ.prod ν) :=
    aesm_comp_snd (Wt_aesm_Iθ α z)
  have hW : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.w z / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (μ.prod ν) :=
    aesm_comp_snd (wdivsin_aesm_Iθ z)
  have hslot : ∀ (j i : ℕ), j + i ≤ k →
      AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i (H p.1) z p.2) (μ.prod ν) :=
    fun j i hji => perz_aesm_slot hcar hsm hmeas hz hji
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (H p.1) z p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i (H p.1) z p.2
                * (Work.Spaces.w z / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k
                  then (Work.Spaces.mixed j i (H p.1) z p.2 * Work.Spaces.Wt α z p.2) ^ 2
                  else 0) := by
    funext p
    rfl
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · refine aesm_finsetSum_apply (fun i hi => ?_)
    have hik : i + 0 ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have h0 := hslot i 0 hik
    refine (h0.mul hW).pow 2 |>.congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply, Pi.pow_apply, Work.Spaces.mixed_zero_right]
  · refine aesm_finsetSum_apply (fun i hi => aesm_finsetSum_apply (fun j hj => ?_))
    by_cases hij : 1 ≤ i ∧ i + j ≤ k
    · have hthis : (fun p : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H p.1) z p.2 * Work.Spaces.Wt α z p.2) ^ 2 else 0))
          = fun p : ℝ × ℝ =>
            (Work.Spaces.mixed j i (H p.1) z p.2 * Work.Spaces.Wt α z p.2) ^ 2 :=
        funext fun p => ite_eq_left hij
      rw [hthis]
      refine ((hslot j i (by omega)).mul hWt).pow 2 |>.congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Pi.pow_apply]
    · have hthis : (fun p : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H p.1) z p.2 * Work.Spaces.Wt α z p.2) ^ 2 else 0))
          = fun p : ℝ × ℝ => (0 : ℝ) :=
        funext fun p => ite_eq_right hij
      rw [hthis]
      exact aestronglyMeasurable_const

end Work.FTS.EpsEngine.PerzTools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_omegaInd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `Ω_n`-coefficient estimate for the cut-off product `χ_n(z)ζ_n(θ) − 1`

For `n ≥ 2` the product `chiR n z * zetaR n θ` of the two cut-offs equals `1` on the closed
rectangle `[2/n, n] × [2/n, π/2 − 2/n]`, and `Ω_n` is exactly the complement of that
rectangle.  Hence *every* mixed derivative `mixed b a (χ_n ζ_n − 1)` with `a + b ≥ 1` is
supported in `Ω_n`: on the plateau every derivative vanishes (`hpz`, `hpθ`, i.e. flatness of
the two cut-offs at the boundary of their plateau), and off `Ω_n` the estimate of
`cutCoeff_omegaInd` is an equality `0 ≤ 0`.

The pointwise estimate

  `(D_z^bD_θ^a (χ_n ζ_n − 1))² ≤ (1 + K b²)(1 + L a²) · 1_{Ω_n}`

then follows from the two uniform derivative bounds `|D_z^b χ_N| ≤ K b`, `|D_θ^a ζ_N| ≤ L a`.

The proof is in three layers.

* A *separation of variables* identity: on a product `f(z)·g(θ)` of a radial and an angular
  factor the mixed derivative splits,
  `D_z^b D_θ^a (f·g)(z,θ) = (D_z^b f)(z,θ) · (D_θ^a g)(z,θ)`
  — this is `mixed_sep_product`.
* The constant `−1` is invisible to the mixed operator as soon as `a + b ≥ 1`
  (`mixed_sub_const`), because `D_θ^r` resp. `D_z^r` kill constants for `r ≥ 1`
  (`DthIter_sub_const`, `DzIter_sub_const`).
* Each factor may be evaluated at a *fixed* dummy point (`θ = 0` resp. `z = 0`), where the
  hypotheses `hKb`, `hLb`, `hpz`, `hpθ` speak.  Outside `Ω_n` both factors vanish by
  `hpz`/`hpθ` (the trivial dummy independence `DzIter_radial_theta_indep`,
  `DthIter_angular_z_indep` moves the point), inside `Ω_n` the first is bounded by `K b`
  and the second by `L a`.

Nothing beyond elementary `deriv` calculus is used: `deriv_sub_const`, `deriv_const_mul_field`
and the definitional (eta) equality of `fun x => h x` with `h`.
-/

noncomputable section

namespace Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces

open Work.FTS.PhiStar.Honesty.CptApp

/-! ## The constant `−1` is killed by any derivative of order at least one -/

/-- `D_θ^r` of `G − c` is `D_θ^r G` for `r ≥ 1`. -/
theorem DthIter_sub_const (r : ℕ) (c : ℝ) (G : ℝ → ℝ → ℝ) (hr : 1 ≤ r) :
    Work.Spaces.DthIter r (fun z θ : ℝ => G z θ - c) = Work.Spaces.DthIter r G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero =>
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' : ℝ => G z θ' - c) θ
        = Real.sin (2 * θ) * deriv (fun θ' : ℝ => G z θ') θ
      rw [deriv_sub_const]
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 from by omega]
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih]

/-- `D_z^r` of `G − c` is `D_z^r G` for `r ≥ 1`. -/
theorem DzIter_sub_const (r : ℕ) (c : ℝ) (G : ℝ → ℝ → ℝ) (hr : 1 ≤ r) :
    Work.Spaces.DzIter r (fun z θ : ℝ => G z θ - c) = Work.Spaces.DzIter r G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction k with
  | zero =>
      funext z θ
      show z * deriv (fun z' : ℝ => G z' θ - c) z = z * deriv (fun z' : ℝ => G z' θ) z
      rw [deriv_sub_const]
  | succ k ih =>
      rw [show 1 + (k + 1) = (1 + k) + 1 from by omega]
      rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih]

/-- `mixed b a` of `F − 1` is `mixed b a F` as soon as `a + b ≥ 1`. -/
theorem mixed_sub_const (b a : ℕ) (hab : 1 ≤ a + b) (F : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => F z θ - 1) = Work.Spaces.mixed b a F := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0]
    show Work.Spaces.DzIter b (fun z θ : ℝ => F z θ - 1) = Work.Spaces.DzIter b F
    exact DzIter_sub_const b 1 F (by omega)
  · show Work.Spaces.DzIter b (Work.Spaces.DthIter a (fun z θ : ℝ => F z θ - 1))
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a F)
    rw [DthIter_sub_const a 1 F (by omega)]

/-! ## The mixed derivatives of `χ_n(z)ζ_n(θ) − 1` -/

/-- For `a + b ≥ 1` the mixed derivative of `χ_n(z)ζ_n(θ) − 1` is the product of the two
one-dimensional derivatives at the same point. -/
theorem mixed_chiR_zetaR_sub_one (n b a : ℕ) (hab : 1 ≤ a + b) (z θ : ℝ) :
    Work.Spaces.mixed b a (fun z θ : ℝ => chiR n z * zetaR n θ - 1) z θ
      = Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ := by
  rw [mixed_sub_const b a hab (fun z θ : ℝ => chiR n z * zetaR n θ)]
  exact mixed_sep_product b a (chiR n) (zetaR n) z θ

/-! ## The estimate -/

theorem cutCoeff_omegaInd (K L : ℕ → ℝ)
    (hKb : ∀ (N b : ℕ) (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z θ| ≤ K b)
    (hLb : ∀ (N a : ℕ) (z θ : ℝ),
      |Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) z θ| ≤ L a)
    (hpz : ∀ (N b : ℕ) (z : ℝ), 2 ≤ N → 1 ≤ b → 2 / (N : ℝ) ≤ z → z ≤ (N : ℝ) →
      Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z 0 = 0)
    (hpθ : ∀ (N a : ℕ) (θ : ℝ), 2 ≤ N → 1 ≤ a → 2 / (N : ℝ) ≤ θ →
      θ ≤ Real.pi / 2 - 2 / (N : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) 0 θ = 0)
    (n a b : ℕ) (hn : 2 ≤ n) (hab : 1 ≤ a + b) (z θ : ℝ) :
    (Work.Spaces.mixed b a
        (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
      ≤ (1 + K b ^ 2) * (1 + L a ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
  rw [mixed_chiR_zetaR_sub_one n b a hab z θ]
  by_cases hOm : (z, θ) ∈ Omega n
  · -- inside `Ω_n`: the two factors are bounded by `K b`, `L a`
    rw [omegaInd_eq_one_iff.mpr hOm]
    have hXb : |Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ| ≤ K b := hKb n b z θ
    have hYb : |Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ| ≤ L a := hLb n a z θ
    have h1 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ) ^ 2 ≤ (K b) ^ 2 := by
      have hA1 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ ≤ K b :=
        le_trans (le_abs_self _) hXb
      have hA2 : -Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ ≤ K b :=
        le_trans (neg_le_abs _) hXb
      have hp1 : (0 : ℝ) ≤ Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ + K b := by
        linarith
      have hp2 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ - K b ≤ (0 : ℝ) := by
        linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp1 hp2]
    have h2 : (Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ) ^ 2 ≤ (L a) ^ 2 := by
      have hA1 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ ≤ L a :=
        le_trans (le_abs_self _) hYb
      have hA2 : -Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ ≤ L a :=
        le_trans (neg_le_abs _) hYb
      have hp1 : (0 : ℝ) ≤ Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ + L a := by
        linarith
      have hp2 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ - L a ≤ (0 : ℝ) := by
        linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hp1 hp2]
    have h3 : (Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ) ^ 2
          * (Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ) ^ 2
        ≤ (K b) ^ 2 * (L a) ^ 2 :=
      mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
    rw [mul_pow]
    nlinarith [h3, sq_nonneg (K b), sq_nonneg (L a)]
  · -- outside `Ω_n`: both factors vanish (`hpz`, `hpθ`)
    have hom0 : omegaInd n z θ = 0 := by
      unfold omegaInd
      rw [if_neg hOm]
    rw [hom0]
    have hz1 : 2 / (n : ℝ) ≤ z := not_lt.mp (fun hc => hOm (Or.inl hc))
    have hz2 : z ≤ (n : ℝ) := not_lt.mp (fun hc => hOm (Or.inr (Or.inl hc)))
    have hth1 : 2 / (n : ℝ) ≤ θ := not_lt.mp (fun hc => hOm (Or.inr (Or.inr (Or.inl hc))))
    have hth2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ) :=
      not_lt.mp (fun hc => hOm (Or.inr (Or.inr (Or.inr hc))))
    have hXY : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ
        * Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ = 0 := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · have ha : 1 ≤ a := by omega
        have hY0 : Work.Spaces.DthIter a (fun _ θ : ℝ => zetaR n θ) z θ = 0 := by
          rw [DthIter_angular_z_indep a (zetaR n) z θ]
          exact hpθ n a θ hn ha hth1 hth2
        rw [hb, hY0]
        simp
      · have hb1 : 1 ≤ b := hb
        have hX0 : Work.Spaces.DzIter b (fun z _ : ℝ => chiR n z) z θ = 0 := by
          rw [DzIter_radial_theta_indep b (chiR n) z θ]
          exact hpz n b z hn hb1 hz1 hz2
        rw [hX0]
        simp
    rw [hXY]
    simp

end Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.PlateauZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

theorem est_two_le_natCast_of {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn

theorem est_natCast_pos_of {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) := by
  have := est_two_le_natCast_of hn
  linarith


set_option autoImplicit false

/-! ## The abstract `D_z`-plateau lemma -/

/-- **`D_z`-iterates of a `θ`-independent function constant on an open interval.**

If `f : ℝ → ℝ` is `C^∞` and equal to the constant `c` on the open interval `(a,b)`, with
`a < b`, then for every `k ≥ 1` the `k`-th `D_z`-iterate of `(z,θ) ↦ f z` vanishes on the
closed interval `[a,b]` (at `θ = 0`, which is irrelevant because the function does not
depend on `θ`).

The iterates are `C^∞`, hence continuous, in `z`: the recursion is `g_{k+1} = z · g_k'` and
the derivative of a `C^∞` function is `C^∞`.  On `(a,b)` they vanish because `f` is locally
constant there; and `[a,b]` is the closure of `(a,b)`, so continuity propagates the
vanishing to the endpoints. -/
theorem DzIter_apply_zero_of_const_on_Ioo {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b c : ℝ} (hab : a < b) (hc : ∀ z ∈ Set.Ioo a b, f z = c) :
    ∀ k : ℕ, 1 ≤ k → ∀ z ∈ Set.Icc a b, Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0 = 0 := by
  -- Every iterate is `C^∞` in `z`, hence continuous.
  have hcont : ∀ k : ℕ,
      Continuous (fun z : ℝ => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0) := by
    intro k
    have hsm : ContDiff ℝ ∞ (fun z : ℝ => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0) := by
      induction k with
      | zero => simpa using hf
      | succ k ih =>
        have hd : ContDiff ℝ ∞
            (fun z : ℝ => deriv (fun z' => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z' 0) z) := by
          simpa [Function.iterate_one] using (ContDiff.iterate_deriv (𝕜 := ℝ) 1 ih)
        have hfun : (fun z : ℝ => Work.Spaces.DzIter (k + 1) (fun z _ : ℝ => f z) z 0)
            = fun z : ℝ =>
                z * deriv (fun z' => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z' 0) z := rfl
        rw [hfun]
        exact contDiff_id.mul hd
    exact hsm.continuous
  -- Vanishing on the open interval, by induction on the order.
  have hopen : ∀ m : ℕ, ∀ z ∈ Set.Ioo a b,
      Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0 := by
    intro m
    induction m with
    | zero =>
      intro z hz
      show z * deriv (fun z' => f z') z = 0
      have hev : (fun z' : ℝ => f z') =ᶠ[𝓝 z] (fun _ => c) := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with z' hz'
        exact hc z' hz'
      rw [hev.deriv_eq, deriv_const, mul_zero]
    | succ m ih =>
      intro z hz
      show z * deriv (fun z' => Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z' 0) z = 0
      have hev : (fun z' : ℝ => Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z' 0)
          =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with z' hz'
        exact ih z' hz'
      rw [hev.deriv_eq, deriv_const, mul_zero]
  -- The closed interval is the closure of the open one.
  intro k hk z hz
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  subst hm
  have hclosed : IsClosed {z : ℝ | Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0} :=
    isClosed_eq (hcont (m + 1)) continuous_const
  have hsub : Set.Ioo a b
      ⊆ {z : ℝ | Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0} :=
    fun z hz => hopen m z hz
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (ne_of_lt hab)] at hcl
  exact hcl hz

/-! ## The abstract `D_θ`-plateau lemma -/

/-- **`D_θ`-iterates of a `z`-independent function constant on an open interval.**

If `g : ℝ → ℝ` is `C^∞` and equal to the constant `c` on the open interval `(a,b)`, with
`a < b`, then for every `k ≥ 1` the `k`-th `D_θ`-iterate of `(z,θ) ↦ g θ` vanishes at `z = 0`
on the closed interval `[a,b]`.

This is the angular analogue of `DzIter_apply_zero_of_const_on_Ioo`: now the recursion of the
iterates `G_k(θ) = D_θ^k (fun _ θ => g θ) 0 θ` is `G_{k+1} = sin(2θ) · G_k'`, and the extra
factor `sin(2θ)` is again `C^∞`, so `G_k` is `C^∞` and the same continuity argument applies.
(The factor vanishes at the endpoints `θ = 0, π/2` of the angular interval, but that is
irrelevant here: `D_θ` is a product, not a quotient, and `[a,b]` is a plateau away from
`0` and `π/2`.) -/
theorem DthIter_apply_zero_of_const_on_Ioo {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {a b c : ℝ} (hab : a < b) (hc : ∀ θ ∈ Set.Ioo a b, g θ = c) :
    ∀ k : ℕ, 1 ≤ k → ∀ θ ∈ Set.Icc a b, Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ = 0 := by
  -- Every iterate is `C^∞` in `θ`, hence continuous.
  have hcont : ∀ k : ℕ,
      Continuous (fun θ : ℝ => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ) := by
    intro k
    have hsm : ContDiff ℝ ∞ (fun θ : ℝ => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ) := by
      induction k with
      | zero => simpa using hg
      | succ k ih =>
        have hd : ContDiff ℝ ∞
            (fun θ : ℝ => deriv (fun θ' => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ') θ) := by
          simpa [Function.iterate_one] using (ContDiff.iterate_deriv (𝕜 := ℝ) 1 ih)
        have hsin : ContDiff ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
        have hfun : (fun θ : ℝ => Work.Spaces.DthIter (k + 1) (fun _ θ : ℝ => g θ) 0 θ)
            = fun θ : ℝ =>
                Real.sin (2 * θ)
                  * deriv (fun θ' => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ') θ := rfl
        rw [hfun]
        exact hsin.mul hd
    exact hsm.continuous
  -- Vanishing on the open interval, by induction on the order.
  have hopen : ∀ m : ℕ, ∀ θ ∈ Set.Ioo a b,
      Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0 := by
    intro m
    induction m with
    | zero =>
      intro θ hθ
      show Real.sin (2 * θ) * deriv (fun θ' => g θ') θ = 0
      have hev : (fun θ' : ℝ => g θ') =ᶠ[𝓝 θ] (fun _ => c) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hc θ' hθ'
      rw [hev.deriv_eq, deriv_const, mul_zero]
    | succ m ih =>
      intro θ hθ
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ') θ = 0
      have hev : (fun θ' : ℝ => Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ')
          =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ'
      rw [hev.deriv_eq, deriv_const, mul_zero]
  -- The closed interval is the closure of the open one.
  intro k hk θ hθ
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  subst hm
  have hclosed : IsClosed {θ : ℝ | Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0} :=
    isClosed_eq (hcont (m + 1)) continuous_const
  have hsub : Set.Ioo a b
      ⊆ {θ : ℝ | Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0} :=
    fun θ hθ => hopen m θ hθ
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (ne_of_lt hab)] at hcl
  exact hcl hθ

/-! ## The plateau of the two cut-offs -/

theorem estPlateauZero :
    (∀ n : ℕ, 2 ≤ n → ∀ b : ℕ, 1 ≤ b → ∀ z : ℝ, 2 / (n : ℝ) ≤ z → z ≤ (n : ℝ) →
      Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z 0 = 0) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ a : ℕ, 1 ≤ a → ∀ θ : ℝ, 2 / (n : ℝ) ≤ θ
        → θ ≤ Real.pi / 2 - 2 / (n : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ) 0 θ = 0) := by
  constructor
  · -- the radial plateau `[2/n, n]` of `chiR n`,
    -- on whose interior `chiR n = 1` (`cutBasic.chiR_eq_one`)
    intro n hn b hb z hz1 hz2
    have hlt : 2 / (n : ℝ) < (n : ℝ) := by
      have h1 : 2 / (n : ℝ) ≤ 1 := (div_le_one (est_natCast_pos_of hn)).mpr (est_two_le_natCast_of hn)
      have h2 : (1 : ℝ) < (n : ℝ) := by
        have := est_two_le_natCast_of hn
        linarith
      linarith
    exact DzIter_apply_zero_of_const_on_Ioo (Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR_C n) hlt
      (fun z hz => chiR_eq_one hn (le_of_lt hz.1) (le_of_lt hz.2)) b hb z ⟨hz1, hz2⟩
  · -- the angular plateau `[2/n, π/2 - 2/n]` of `zetaR n`,
    -- on whose interior `zetaR n = 1` (`cutBasic.zetaR_eq_one`)
    intro n hn a ha θ hθ1 hθ2
    by_cases hn2 : n = 2
    · -- for `n = 2` the angular plateau is empty, so there is nothing to prove
      exfalso
      subst hn2
      norm_num at hθ1 hθ2
      linarith [Real.pi_lt_four]
    · have hn3 : 3 ≤ n := by omega
      have hlt : 2 / (n : ℝ) < Real.pi / 2 - 2 / (n : ℝ) := by
        have h1 : 2 / (n : ℝ) ≤ 2 / 3 := by
          rw [div_le_div_iff₀ (est_natCast_pos_of hn) (by norm_num : (0 : ℝ) < 3)]
          have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
          linarith
        linarith [Real.pi_gt_three]
      exact DthIter_apply_zero_of_const_on_Ioo (Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR_C n) hlt
        (fun θ hθ => zetaR_eq_one hn (le_of_lt hθ.1) (le_of_lt hθ.2)) a ha θ ⟨hθ1, hθ2⟩

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Arithmetic helpers

The seven rectangle integrals of `mixed_rect_L2_bounds` are bounded by rewriting each
integrand with `mixed_partials_of_smoothOpen` into a quotient of mixed derivatives (by
`z`, `sin 2θ`, `z²`, `sin²2θ`), and then comparing, on the rectangle, the reciprocals of
those factors with the constants `a^{-2}`, `m^{-2}`, `a^{-4}`, `(am)^{-2}`, `m^{-4}`
(`m` a positive lower bound for `sin 2θ` on `[c,d]`).  The three lemmas below are the
purely numerical steps. -/

/-- `(X / y)² ≤ (1 / p) · H` as soon as `X² ≤ H`, `0 ≤ H` and `0 < p ≤ y²`. -/
private lemma div_sq_le_one_div_mul {X H y p : ℝ} (hX : X ^ 2 ≤ H) (hH : 0 ≤ H) (hp : 0 < p)
    (hpy : p ≤ y ^ 2) : (X / y) ^ 2 ≤ (1 / p) * H := by
  have hy2 : 0 < y ^ 2 := lt_of_lt_of_le hp hpy
  have h1 : (X / y) ^ 2 = X ^ 2 / y ^ 2 := by rw [div_pow]
  rw [h1]
  calc X ^ 2 / y ^ 2 ≤ H / y ^ 2 := div_le_div_of_nonneg_right hX (le_of_lt hy2)
    _ ≤ H / p := div_le_div_of_nonneg_left hH hp hpy
    _ = (1 / p) * H := by ring

/-- `((A - B) / z²)² ≤ (4 / a⁴) · H` as soon as `A² ≤ H`, `B² ≤ H` and `0 < a ≤ z`. -/
private lemma div_sq_pow4_le {A B H z a : ℝ} (hz : a ≤ z) (ha : 0 < a)
    (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) : ((A - B) / z ^ 2) ^ 2 ≤ (4 / a ^ 4) * H := by
  have hzpos : 0 < z := lt_of_lt_of_le ha hz
  have hz4 : 0 < z ^ 4 := by positivity
  have ha4 : 0 < a ^ 4 := by positivity
  have h1 : ((A - B) / z ^ 2) ^ 2 = (A - B) ^ 2 / z ^ 4 := by rw [div_pow]; ring_nf
  rw [h1]
  have hAB : (A - B) ^ 2 ≤ 4 * H := by nlinarith [sq_nonneg (A - B), hA, hB]
  have hz4' : a ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ ha.le hz 4
  calc (A - B) ^ 2 / z ^ 4 ≤ (4 * H) / z ^ 4 := div_le_div_of_nonneg_right hAB (le_of_lt hz4)
    _ ≤ (4 * H) / a ^ 4 :=
        div_le_div_of_nonneg_left (by nlinarith [sq_nonneg (A - B)]) ha4 hz4'
    _ = (4 / a ^ 4) * H := by ring

/-- `((A - 2cB) / s²)² ≤ (12 / m⁴) · H` as soon as `A² ≤ H`, `B² ≤ H`, `|c| ≤ 1` and
`0 < m ≤ s`. -/
private lemma div_sq_pow4_cos_le {A B H s m c : ℝ} (hm : 0 < m) (hms : m ≤ s)
    (hc : |c| ≤ 1) (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) :
    ((A - 2 * c * B) / s ^ 2) ^ 2 ≤ (12 / m ^ 4) * H := by
  have hs : 0 < s := lt_of_lt_of_le hm hms
  have hm4 : 0 < m ^ 4 := by positivity
  have h1 : ((A - 2 * c * B) / s ^ 2) ^ 2 = (A - 2 * c * B) ^ 2 / s ^ 4 := by
    rw [div_pow]; ring_nf
  rw [h1]
  have hnum : (A - 2 * c * B) ^ 2 ≤ 6 * (A ^ 2 + B ^ 2) := by
    have h2 : |A - 2 * c * B| ≤ |A| + |2 * c * B| := by
      simpa [sub_eq_add_neg] using abs_add_le A (-(2 * c * B))
    have h3 : |2 * c * B| = 2 * |c| * |B| := by rw [abs_mul, abs_mul]; ring
    have h4 : 2 * |c| * |B| ≤ 2 * |B| := by nlinarith [abs_nonneg B]
    have h5 : |A - 2 * c * B| ≤ |A| + 2 * |B| := by rw [h3] at h2; linarith
    have h6 : (A - 2 * c * B) ^ 2 = |A - 2 * c * B| ^ 2 := by rw [sq_abs]
    rw [h6]
    nlinarith [abs_nonneg A, abs_nonneg B, abs_nonneg (A - 2 * c * B),
      sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
  have hs4 : m ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hm.le hms 4
  have hnn : 0 ≤ 6 * (A ^ 2 + B ^ 2) := by nlinarith [sq_nonneg A, sq_nonneg B]
  have hfinal : (6 * (A ^ 2 + B ^ 2)) / m ^ 4 ≤ (12 / m ^ 4) * H := by
    rw [div_le_iff₀ hm4]
    have he : (12 / m ^ 4) * H * m ^ 4 = 12 * H := by field_simp
    rw [he]
    nlinarith [hA, hB]
  calc (A - 2 * c * B) ^ 2 / s ^ 4 ≤ (6 * (A ^ 2 + B ^ 2)) / s ^ 4 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (6 * (A ^ 2 + B ^ 2)) / m ^ 4 := div_le_div_of_nonneg_left hnn hm4 hs4
    _ ≤ (12 / m ^ 4) * H := hfinal

theorem mixed_rect_L2_bounds {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hd : d < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → ∀ (F : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α 6 F →
      ∀ (j i : ℕ), j + i ≤ 4 →
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.mixed j i F z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 F) := by
  classical
  -- a positive lower bound for `sin 2θ` on `[c,d]`
  obtain ⟨m, hmpos, hmle⟩ := sin_two_lower_bound_rect (c := c) (d := d) hc hd
  -- the constant: the sum of the seven individual constants
  refine ⟨1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4,
    by positivity, ?_⟩
  have hKa : (0 : ℝ) ≤ 1 / a ^ 2 := by positivity
  have hKm : (0 : ℝ) ≤ 1 / m ^ 2 := by positivity
  have hKa4 : (0 : ℝ) ≤ 4 / a ^ 4 := by positivity
  have hKam : (0 : ℝ) ≤ 2 * (1 / (a ^ 2 * m ^ 2)) := by positivity
  have hKm4 : (0 : ℝ) ≤ 12 / m ^ 4 := by positivity
  have hKC1 : (1 : ℝ) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC2 : 1 / a ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC3 : 1 / m ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC4 : 4 / a ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC5 : 1 / (a ^ 2 * m ^ 2) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4
      + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4 := by linarith
  have hKC7 : 12 / m ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  intro α hα F hF hmem j i hji
  have hji6 : j + i ≤ 6 := by omega
  -- the six identities of `mixed_partials_of_smoothOpen`
  obtain ⟨hid1, hid2, hid3, hid4, hid5, hid6⟩ := mixed_partials_of_smoothOpen j i hF
  -- congruence of `pz`/`pth` on the open quadrant: replace `∂_z pz (mixed j i F)` by the
  -- quotient functions for which the identities are stated
  have hEqz : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed (j + 1) i F z θ / z)
      Work.FTS.EllipticEst.Q0 := fun p hp => hid1 p.1 p.2 hp
  have hEqθ : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ))
      Work.FTS.EllipticEst.Q0 := fun p hp => hid2 p.1 p.2 hp
  have hpzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have htzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have hpθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  have htθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  -- the pointwise facts on the rectangle
  have hmQ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    intro z hz θ hθ
    exact ⟨lt_of_lt_of_le ha hz.1, ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩⟩
  have hsinp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < Real.sin (2 * θ) := by
    intro z hz θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, hθ.1])
      (by linarith [hθ.2, hd, Real.pi_pos])
  have hHnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 6 F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 6 F z θ
  -- (P1) the mixed slot itself
  have p1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.mixed j i F z θ) ^ 2 ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have h := mixed_sq_le_HkIntegrand (F := F) α hα j i hji6 (lt_of_lt_of_le ha hz.1) (hsinp z hz θ hθ)
    simpa using h
  -- (P2) `∂_z`
  have p2 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / a ^ 2) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < a ^ 2 := by positivity
    have hy2 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    rw [hid1 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P3) `∂_θ`
  have p3 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / m ^ 2) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < m ^ 2 := by positivity
    have hy2 : m ^ 2 ≤ Real.sin (2 * θ) ^ 2 := pow_le_pow_left₀ hmpos.le (hmle θ hθ) 2
    rw [hid2 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P4) `∂_z∂_z`
  have p4 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (4 / a ^ 4) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand (F := F) α hα (j + 2) i (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    rw [hpzz z θ hQ, hid3 z θ hQ]
    exact div_sq_pow4_le hz.1 ha hA hB
  -- (P5) `∂_z∂_θ`
  have p5 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [hpθθ z θ hQ, hid4 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P6) `∂_θ∂_z`
  have p6 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand (F := F) α hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [htzz z θ hQ, hid5 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P7) `∂_θ∂_θ`
  have p7 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (12 / m ^ 4) * Work.Spaces.HkIntegrand α 6 F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 2) (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand (F := F) α hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    rw [htθθ z θ hQ, hid6 z θ hQ]
    rw [show Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ / (Real.sin (2 * θ)) ^ 2
        = (Work.Spaces.mixed j (i + 2) F z θ
            - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ)
          / (Real.sin (2 * θ)) ^ 2 from by ring]
    exact div_sq_pow4_cos_le hmpos (hmle θ hθ) (Real.abs_cos_le_one (2 * θ)) hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rect_integral_le_of_pointwise (K := 1) (α := α) (F := F)
      (g := Work.Spaces.mixed j i F) ha hab hc hd hmem (by norm_num) p1).trans
      (mul_le_mul_of_nonneg_right hKC1 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / a ^ 2) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.mixed j i F)) ha hab hc hd hmem hKa p2).trans
      (mul_le_mul_of_nonneg_right hKC2 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / m ^ 2) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.mixed j i F)) ha hab hc hd hmem hKm p3).trans
      (mul_le_mul_of_nonneg_right hKC3 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 4 / a ^ 4) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p4).trans
      (mul_le_mul_of_nonneg_right hKC4 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / (a ^ 2 * m ^ 2)) (α := α) (F := F)
      (g := Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p5).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 1 / (a ^ 2 * m ^ 2)) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p6).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α 6 F))
  · exact (rect_integral_le_of_pointwise (K := 12 / m ^ 4) (α := α) (F := F)
      (g := Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      ha hab hc hd hmem (by positivity) p7).trans
      (mul_le_mul_of_nonneg_right hKC7 (Work.Spaces.HkSq_nonneg α 6 F))

end Work.FTS.StrongEps.LocUnif
end
end
