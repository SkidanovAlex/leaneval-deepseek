/-
Copyright: work module for the Elgindi finite-time singularity project.

# The interval-integral `ℋ`-membership (per-`z` version): elementary measure theory

This module collects the measure-theoretic background for
`Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`.  Everything here is stated with two explicit
*interface hypotheses* (as `Prop`s):

* `CarathTheta` — the `(s,θ)`-Carathéodory measurability statement (proved elsewhere as
  `Work.FTS.EpsEngine.PerzTools.aesm_uncurry_restricted_theta`);
* `ExchMixed` — the exchange of `D_z^j D_θ^i` with the interval integral, with the measurability
  hypothesis restricted to the orders `≤ n`
  (proved elsewhere as `Work.FTS.EpsEngine.PerzTools.mixed_intervalIntegral_eq_gen_restricted`).

This keeps the present module independent of those two proofs.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E5G5.mixed_intervalIntegral_eq_gen
import Submission.Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted

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
