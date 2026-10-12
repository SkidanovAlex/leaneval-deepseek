import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Submission.Work.BoseFixB1B.CutFibreForms
import Submission.Work.BoseFixB1PInd.lintegral_abox_peel
import Submission.Work.BoseFixB1S.Gen.boxQIndAesm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.cutAmplitude_integrable`

Integrability in `p` of the windowed amplitude forms

`p ↦ (L³)⁻¹ ∫_{abox (n+1) L} ‖tBamp χ p Φ i x‖² dx` and its `‖p‖²`-weighted version,

where `Φ` is a state that is only *a.e. measurable* and *bounded* on the box, whose slot-`i`
fibres `z ↦ χ z·Φ(x_{i←z})` are smooth with a uniform bound `C` on the Dirichlet (first
derivative `L²`) energy.

## The argument

* For `x ∈ abox (n+1) L` the amplitude is the `p`-convention Fourier transform of the
  windowed fibre `u_x z = χ z·Φ(x_{i←z})` (`tBamp_eq_kinFT_update`); `u_x` is smooth with
  compact support (`hfib`, `hχcs`), so the fibre Plancherel identities apply:
  `∫⁻_p ofReal (‖kinFT u p‖²) = ofReal ((2π)³ ∫ u²)` and
  `∫⁻_p ofReal (‖p‖²‖kinFT u p‖²) = ofReal ((2π)³ ∫ Σ_k (∂_k u)²)` (proved here by
  `ofReal_integral_eq_lintegral_ofReal` together with the corpus' `plancherel_pconv` and
  `kinFT_energy_sum`).
* `tBamp χ · Φ i ·` is jointly a.e. strongly measurable in `(p,x)` for an only a.e. measurable
  `Φ` (`aesm_tBamp_joint`): the slot-update map is quasi-measure-preserving on the centred
  box (`qmp_update_abox_prod`, from the corpus' `Gen.qmp_update_abox_gen`), and
  `AEStronglyMeasurable.integral_prod_right'` integrates out `z` with no integrability
  hypothesis.
* Tonelli (`lintegral_lintegral_swap`) exchanges the `p`- and `x`-integrals; the pointwise
  fibre bounds `hdir` (weighted) and `hB` (unweighted, via `∫ u_x² ≤ B²∫χ²`) then bound the
  double lintegral by a finite constant, and `Integrable` follows from
  `HasFiniteIntegral` + a.e. strong measurability.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal ContDiff

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1  The amplitude as the Fourier transform of the windowed fibre -/

/-- **The windowed amplitude is the `p`-convention Fourier transform of the windowed
slot-`i` fibre.**  `tBamp χ p Φ i x = ∫_z χ z e^{−i⟪p,z⟫} Φ(x_{i←z}) dz` is exactly
`kinFT` of `z ↦ χ z·Φ(x_{i←z})`, complexified. -/
lemma tBamp_eq_kinFT_update {N : ℕ} (χ : E3 → ℝ) (Φ : Submission.BoseGases.X N → ℝ)
    (i : Fin N) (p : E3) (x : Submission.BoseGases.X N) :
    Work.SmallBoxTBWord.tBamp χ p Φ i x
      = Submission.BoseGases.kinFT
          (fun z : E3 => ((χ z * Φ (Function.update x i z) : ℝ) : ℂ)) p := by
  rw [Work.SmallBoxTBWord.tBamp, Submission.BoseGases.kinFT]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  push_cast
  ring

/-! ## 2  Fibre Plancherel identities at the `lintegral` level -/

/-- **Unweighted fibre Plancherel.** `∫⁻_p ofReal ‖kinFT u p‖² = ofReal ((2π)³ ∫ u²)`. -/
theorem lintegral_ofReal_kinFT_sq_eq (u : E3 → ℝ) (hu : ContDiff ℝ (⊤ : ENat) u)
    (hcs : HasCompactSupport u) :
    (∫⁻ p : E3, ENNReal.ofReal (‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2))
      = ENNReal.ofReal ((2 * Real.pi) ^ 3 * (∫ z : E3, u z ^ 2)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (Work.BSKinetic.integrable_kinFT_sq u hu hcs)
    (Filter.Eventually.of_forall (fun p => sq_nonneg _))]
  have hval : (∫ p : E3, ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2)
      = ((2 * Real.pi) ^ 3) * (∫ z : E3, u z ^ 2) := by
    have h3 : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 (by positivity)
    have hh : ((2 * Real.pi) ^ 3) * (∫ z : E3, u z ^ 2)
        = ∫ p : E3, ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2 := by
      rw [← Work.BSKinetic.plancherel_pconv u hu hcs, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
    exact hh.symm
  rw [hval]

/-- **Weighted fibre Plancherel.**
`∫⁻_p ofReal (‖p‖²‖kinFT u p‖²) = ofReal ((2π)³ ∫ Σ_k (∂_k u)²)`. -/
theorem lintegral_ofReal_kinFT_energy_eq (u : E3 → ℝ) (hu : ContDiff ℝ (⊤ : ENat) u)
    (hcs : HasCompactSupport u) :
    (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2))
      = ENNReal.ofReal ((2 * Real.pi) ^ 3 *
          (∫ z : E3, ∑ k : Fin 3,
            (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (Work.SmallBoxTBWord.integrable_kinFT_energy_cspt u hu hcs)
    (Filter.Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))]
  -- the exchange of `∫` and the finite coordinate sum
  have hInt_real : ∀ k : Fin 3,
      Integrable (fun x : E3 => (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
    set v : E3 → ℂ := fun y => (u y : ℂ) with hv
    have hv_smooth : ContDiff ℝ (⊤ : ENat) v := by
      simpa only [hv, Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.contDiff.comp hu
    have hv_cs : HasCompactSupport v := by
      simpa only [hv, Function.comp_def, Complex.ofRealCLM_apply] using
        hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
    let f : SchwartzMap E3 ℂ := hv_cs.toSchwartzMap hv_smooth
    have hf_coe : (f : E3 → ℂ) = v := rfl
    have hInt_complex : ∀ k : Fin 3,
        Integrable (fun x : E3 =>
          ‖fderiv ℝ (f : E3 → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
          (MeasureTheory.volume : MeasureTheory.Measure E3) := by
      intro k
      have hm : MeasureTheory.MemLp
          (LineDeriv.lineDerivOp (Submission.BoseGases.kcStdBasis k) f : E3 → ℂ) 2
          (MeasureTheory.volume : MeasureTheory.Measure E3) :=
        SchwartzMap.memLp _ 2 (MeasureTheory.volume : MeasureTheory.Measure E3)
      rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable] at hm
      simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hm
    have hfder : ∀ x : E3, fderiv ℝ (f : E3 → ℂ) x
        = Complex.ofRealCLM.comp (fderiv ℝ u x) := by
      intro x
      rw [hf_coe, hv]
      have h := (Complex.ofRealCLM.hasFDerivAt (x := u x)).comp x
        ((hu1.differentiable_one x).hasFDerivAt)
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h.fderiv
    intro k
    refine (hInt_complex k).congr ?_
    filter_upwards with x
    rw [hfder x]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    rw [Complex.sq_norm, Complex.normSq_ofReal, pow_two]
  have hsum : (∫ z : E3, ∑ k : Fin 3,
        (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ z : E3, (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    MeasureTheory.integral_finsetSum (Finset.univ) (fun k _ => hInt_real k)
  rw [hsum]
  have hval : (∫ p : E3, ‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2)
      = ((2 * Real.pi) ^ 3) * (∑ k : Fin 3, ∫ z : E3,
          (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    have h3 : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 (by positivity)
    have hh : ((2 * Real.pi) ^ 3) * (∑ k : Fin 3, ∫ z : E3,
            (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∫ p : E3, ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2 := by
      rw [← Work.BSKinetic.kinFT_energy_sum u hu hcs, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
    exact hh.symm
  rw [hval]

/-- The unweighted fibre Plancherel inequality. -/
theorem lintegral_ofReal_kinFT_sq_le (u : E3 → ℝ) (hu : ContDiff ℝ (⊤ : ENat) u)
    (hcs : HasCompactSupport u) {C : ℝ}
    (hC : (∫ z : E3, u z ^ 2) ≤ C) :
    (∫⁻ p : E3, ENNReal.ofReal (‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
  rw [lintegral_ofReal_kinFT_sq_eq u hu hcs]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hC (by positivity))

/-- The `‖p‖²`-weighted fibre Plancherel inequality. -/
theorem lintegral_ofReal_kinFT_energy_le (u : E3 → ℝ) (hu : ContDiff ℝ (⊤ : ENat) u)
    (hcs : HasCompactSupport u) {C : ℝ}
    (hC : (∫ z : E3, ∑ k : Fin 3,
        (fderiv ℝ u z (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) :
    (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
        ‖Submission.BoseGases.kinFT (fun z : E3 => (u z : ℂ)) p‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
  rw [lintegral_ofReal_kinFT_energy_eq u hu hcs]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hC (by positivity))

/-! ## 3  Measurability of the joint amplitude -/

/-- **Quasi-measure-preservation of the slot-update map, with a dummy coordinate.**

The map `(p, x, z) ↦ x|i ↦ z` pushes the product measure
`vol ⊗ (vol↾abox N a) ⊗ (vol↾acube a)` to a measure absolutely continuous with respect to
`vol↾abox N a`.  The dummy `p`-coordinate contributes `∞·0 = 0`. -/
theorem qmp_update_abox_prod {n : ℕ} {a : ℝ} (i : Fin (n + 1)) :
    Measure.QuasiMeasurePreserving
      (fun w : (E3 × Submission.BoseGases.X (n + 1)) × E3 => Function.update w.1.2 i w.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) a))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube a)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) a)) := by
  have h1 : Measure.QuasiMeasurePreserving
      (Prod.map (Prod.snd : E3 × Submission.BoseGases.X (n + 1) → Submission.BoseGases.X (n + 1)) id)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) a))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube a)))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) a)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube a))) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_snd) (Measure.QuasiMeasurePreserving.id _)
  have h2 : Measure.QuasiMeasurePreserving
      (fun p : Submission.BoseGases.X (n + 1) × E3 => Function.update p.1 i p.2)
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) a)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure E3).restrict
          (Submission.BoseGases.acube a)))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) a)) :=
    Work.BoseFixB1S.Gen.qmp_update_abox_gen (a := a) (A := Submission.BoseGases.acube a)
      (subset_refl _) n i
  have hfg : (fun w : (E3 × Submission.BoseGases.X (n + 1)) × E3 => Function.update w.1.2 i w.2)
      = (fun p : Submission.BoseGases.X (n + 1) × E3 => Function.update p.1 i p.2) ∘
        (Prod.map (Prod.snd : E3 × Submission.BoseGases.X (n + 1) → Submission.BoseGases.X (n + 1))
          id) :=
    rfl
  rw [hfg]
  exact h2.comp h1

/-- **Joint a.e. strong measurability of the windowed amplitude.**  For an only a.e. measurable
`Φ` (on the centred box) and a window `χ` vanishing off `acube L`, the map
`(p,x) ↦ tBamp χ p Φ i x` is a.e. strongly measurable for `vol ⊗ (vol↾abox (n+1) L)`. -/
theorem aesm_tBamp_joint {n : ℕ} {L : ℝ} (hL : 0 < L)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    (hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦm : AEMeasurable Φ
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)))
    (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) := by
  have hqmp := qmp_update_abox_prod (a := L) (n := n) i
  have hcomp : AEMeasurable
      (fun w : (E3 × Submission.BoseGases.X (n + 1)) × E3 =>
        Φ (Function.update w.1.2 i w.2))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube L))) :=
    hΦm.comp_quasiMeasurePreserving hqmp
  have hker : Continuous (fun w : (E3 × Submission.BoseGases.X (n + 1)) × E3 =>
      (χ w.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ)))) := by
    fun_prop
  have hprod : MeasureTheory.AEStronglyMeasurable
      (fun w : (E3 × Submission.BoseGases.X (n + 1)) × E3 =>
        (χ w.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ))) *
          (Φ (Function.update w.1.2 i w.2) : ℂ))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod
          (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube L))) :=
    hker.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hcomp.aestronglyMeasurable)
  refine hprod.integral_prod_right'.congr (Filter.Eventually.of_forall (fun q => ?_))
  exact (Work.SmallBoxTBWord.tBamp_eq_setIntegral (a := L) (W := χ) hχ0 i q.1 q.2).symm

/-! ## 4  Elementary support facts -/

/-- Overwriting the `i`-th slot of a box configuration by a point of the cube keeps the
configuration in the box. -/
lemma update_mem_abox {N : ℕ} {a : ℝ} (x : Submission.BoseGases.X (N + 1)) (i : Fin (N + 1))
    {z : E3} (hx : x ∈ Submission.BoseGases.abox (N + 1) a)
    (hz : z ∈ Submission.BoseGases.acube a) :
    Function.update x i z ∈ Submission.BoseGases.abox (N + 1) a := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rcases eq_or_ne j i with rfl | hj
  · simpa using hz
  · rw [Function.update_of_ne hj z x]
    exact hx j

/-- The `L²` mass of the windowed slot-`i` fibre is bounded by `B²∫χ²` when `Φ` is bounded
by `B` on the box and `χ` vanishes off the cube. -/
lemma fibre_sq_integral_le {n : ℕ} {L B : ℝ} {χ : E3 → ℝ} (hχc : Continuous χ)
    (hχcs : HasCompactSupport χ)
    (hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (hB : ∀ x ∈ Submission.BoseGases.abox (n + 1) L, |Φ x| ≤ B)
    (x : Submission.BoseGases.X (n + 1)) (hx : x ∈ Submission.BoseGases.abox (n + 1) L) :
    (∫ z : E3, (χ z * Φ (Function.update x i z)) ^ 2) ≤ B ^ 2 * (∫ z : E3, χ z ^ 2) := by
  have hsp : HasCompactSupport (fun z : E3 => χ z ^ 2) := by
    have h0 : (fun z : E3 => χ z ^ 2) = (χ * χ : E3 → ℝ) := by
      funext z; simp [pow_two, Pi.mul_apply]
    rw [h0]
    exact hχcs.mul_right
  have hInt : Integrable (fun z : E3 => B ^ 2 * χ z ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    (((hχc.pow 2).integrable_of_hasCompactSupport hsp).const_mul _)
  have hpt : ∀ z : E3, (χ z * Φ (Function.update x i z)) ^ 2 ≤ B ^ 2 * χ z ^ 2 := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube L
    · have hmem : Function.update x i z ∈ Submission.BoseGases.abox (n + 1) L :=
        update_mem_abox x i hx hz
      have h1 : |Φ (Function.update x i z)| ≤ B := hB _ hmem
      have h2 : (Φ (Function.update x i z)) ^ 2 ≤ B ^ 2 := by
        rw [sq_le_sq]
        exact le_trans h1 (le_abs_self B)
      calc (χ z * Φ (Function.update x i z)) ^ 2
          = χ z ^ 2 * (Φ (Function.update x i z)) ^ 2 := by ring
        _ ≤ χ z ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = B ^ 2 * χ z ^ 2 := by ring
    · rw [hχ0 z hz]
      simp
  calc (∫ z : E3, (χ z * Φ (Function.update x i z)) ^ 2)
      ≤ ∫ z : E3, B ^ 2 * χ z ^ 2 :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hInt
          (Filter.Eventually.of_forall hpt)
    _ = B ^ 2 * (∫ z : E3, χ z ^ 2) := MeasureTheory.integral_const_mul _ _

/-! ## 5  The main estimate -/

/-- **Integrability of the windowed amplitude forms** for a general state `Φ` that is a.e.
measurable and bounded on the box, with smooth fibres and a uniform Dirichlet bound. -/
theorem cutAmplitude_integrable_aux {n : ℕ} {L : ℝ} (hL : 0 < L)
    {χ : E3 → ℝ} (hχc : Continuous χ) (hχcs : HasCompactSupport χ)
    (hχ0 : ∀ z : E3, z ∉ Submission.BoseGases.acube L → χ z = 0)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (hΦm : AEMeasurable Φ)
    {B : ℝ} (hB : ∀ x ∈ Submission.BoseGases.abox (n + 1) L, |Φ x| ≤ B)
    (hfib : ∀ x ∈ Submission.BoseGases.abox (n + 1) L, ContDiff ℝ (⊤ : ENat)
      (fun z : E3 => χ z * Φ (Function.update x i z)))
    {C : ℝ} (hdir : ∀ x ∈ Submission.BoseGases.abox (n + 1) L,
      (∫ z : E3, ∑ k : Fin 3,
        (fderiv ℝ (fun y : E3 => χ y * Φ (Function.update x i y))
          z (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) :
    (MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
    ∧ (MeasureTheory.Integrable (fun p : E3 =>
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) := by
  classical
  have hLnn : 0 ≤ L := hL.le
  have hinv : (0 : ℝ) ≤ (L ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hLnn 3)
  have hboxvol : (MeasureTheory.volume : MeasureTheory.Measure
        (Submission.BoseGases.X (n + 1))) (Submission.BoseGases.abox (n + 1) L)
      = ENNReal.ofReal ((L ^ 3) ^ (n + 1)) :=
    Submission.BoseGases.abox_volume (n + 1) L hLnn
  -- ### measurability
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    aesm_tBamp_joint hL hχc hχ0 (hΦm.mono_measure Measure.restrict_le_self) i
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    hjoint.norm.pow 2
  have hJsm : MeasureTheory.AEStronglyMeasurable
      (fun p : E3 => ∫ x in Submission.BoseGases.abox (n + 1) L,
        ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    h2.integral_prod_right'
  have hslice : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X (n + 1) =>
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)) :=
    h2.prodMk_left
  have hmeas_px : AEMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ENNReal.ofReal (‖q.1‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((by fun_prop : Continuous (fun q : E3 × Submission.BoseGases.X (n + 1) =>
          ‖q.1‖ ^ 2)).aestronglyMeasurable).mul h2).aemeasurable
  have hmeas_px2 : AEMeasurable
      (fun q : E3 × Submission.BoseGases.X (n + 1) =>
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ q.1 Φ i q.2‖ ^ 2))
      ((MeasureTheory.volume : MeasureTheory.Measure E3).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable h2.aemeasurable
  -- ### the a.e. replacement of the real `x`-integral by its `lintegral`
  have hJbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
      ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)
        ≤ ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
            ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
    filter_upwards [hslice] with p hp
    have h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)]
        (fun x : Submission.BoseGases.X (n + 1) =>
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
      Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    have hconv := MeasureTheory.integral_eq_lintegral_of_nonneg_ae h0 hp
    rw [hconv]
    exact ENNReal.ofReal_toReal_le
  -- ### the two fibre bounds (pointwise in `x`)
  have hperx_w : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)),
      (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) L)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hcongr : (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        = ∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT
              (fun z : E3 => ((χ z * Φ (Function.update x i z) : ℝ) : ℂ)) p‖ ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [tBamp_eq_kinFT_update χ Φ i p x]
    rw [hcongr]
    exact lintegral_ofReal_kinFT_energy_le (fun z : E3 => χ z * Φ (Function.update x i z))
      (hfib x hx) (hχcs.mul_right (f' := fun z => Φ (Function.update x i z))) (hdir x hx)
  have hperx_s : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) L)),
      (∫⁻ p : E3, ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) := by
    rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable (n + 1) L)]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hcongr : (∫⁻ p : E3, ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        = ∫⁻ p : E3, ENNReal.ofReal
            (‖Submission.BoseGases.kinFT
              (fun z : E3 => ((χ z * Φ (Function.update x i z) : ℝ) : ℂ)) p‖ ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [tBamp_eq_kinFT_update χ Φ i p x]
    rw [hcongr]
    exact lintegral_ofReal_kinFT_sq_le (fun z : E3 => χ z * Φ (Function.update x i z))
      (hfib x hx) (hχcs.mul_right (f' := fun z => Φ (Function.update x i z)))
      (fibre_sq_integral_le hχc hχcs hχ0 i hB x hx)
  -- ### the `p`- and `x`-integrals exchanged
  have hswap_w : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
        ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
        ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
    MeasureTheory.lintegral_lintegral_swap hmeas_px
  have hswap_s : (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
      = ∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
        ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) :=
    MeasureTheory.lintegral_lintegral_swap hmeas_px2
  -- ### the weighted estimate
  have hweighted : (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))) < ⊤ := by
    have hbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        ENNReal.ofReal (‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
          ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
      filter_upwards [hJbound] with p hp
      calc ENNReal.ofReal (‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
              (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
          = ENNReal.ofReal (‖p‖ ^ 2) * (ENNReal.ofReal ((L ^ 3)⁻¹) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
            rw [ENNReal.ofReal_mul (sq_nonneg (‖p‖)), ENNReal.ofReal_mul hinv]
        _ = ENNReal.ofReal ((L ^ 3)⁻¹) * (ENNReal.ofReal (‖p‖ ^ 2) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by ring
        _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) * (ENNReal.ofReal (‖p‖ ^ 2) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) :=
            mul_le_mul_right (mul_le_mul_right hp _) _
        _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
            congr 1
            rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall
              (fun x => ENNReal.ofReal_mul (sq_nonneg (‖p‖))))]
            exact (MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (‖p‖ ^ 2))
              (fun x : Submission.BoseGases.X (n + 1) =>
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
              ENNReal.ofReal_ne_top).symm
    have hconst : (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
          ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
            ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
      calc (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
            ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ∫⁻ _x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) :=
            MeasureTheory.lintegral_mono_ae hperx_w
        _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, hboxvol]
    calc (∫⁻ p : E3, ENNReal.ofReal (‖p‖ ^ 2 *
          ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))))
        ≤ ∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_mono_ae hbound
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
              ENNReal.ofReal (‖p‖ ^ 2 * ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
          rw [hswap_w]
      _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (ENNReal.ofReal ((2 * Real.pi) ^ 3 * C) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1))) := mul_le_mul_right hconst _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- ### the unweighted estimate
  have hunweighted : (∫⁻ p : E3, ENNReal.ofReal
        ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))) < ⊤ := by
    have hbound : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure E3),
        ENNReal.ofReal ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
      filter_upwards [hJbound] with p hp
      calc ENNReal.ofReal ((L ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          = ENNReal.ofReal ((L ^ 3)⁻¹) *
              ENNReal.ofReal (∫ x in Submission.BoseGases.abox (n + 1) L,
                ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
            rw [ENNReal.ofReal_mul hinv]
        _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
              (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
                ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
            mul_le_mul_right hp _
    have hconst : (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
          ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
            ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
      calc (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
            ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
          ≤ ∫⁻ _x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) :=
            MeasureTheory.lintegral_mono_ae hperx_s
        _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1)) := by
            rw [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, hboxvol]
    calc (∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
        ≤ ∫⁻ p : E3, ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_mono_ae hbound
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ p : E3, ∫⁻ x in Submission.BoseGases.abox (n + 1) L,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((L ^ 3)⁻¹) *
            (∫⁻ x in Submission.BoseGases.abox (n + 1) L, ∫⁻ p : E3,
              ENNReal.ofReal (‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)) := by
          rw [hswap_s]
      _ ≤ ENNReal.ofReal ((L ^ 3)⁻¹) *
            (ENNReal.ofReal ((2 * Real.pi) ^ 3 * (B ^ 2 * (∫ z : E3, χ z ^ 2))) *
              ENNReal.ofReal ((L ^ 3) ^ (n + 1))) := mul_le_mul_right hconst _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- ### conclusion
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hfun : (fun p : E3 => ‖p‖ ^ 2 * ((L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2)))
        = fun p : E3 => (‖p‖ ^ 2 * (L ^ 3)⁻¹) *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := by
      funext p; ring
    rw [hfun]
    exact (by fun_prop : Continuous (fun p : E3 => ‖p‖ ^ 2 * (L ^ 3)⁻¹)).aestronglyMeasurable.mul
      hJsm
  · refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => ?_))) hweighted
    exact Real.enorm_eq_ofReal (mul_nonneg (sq_nonneg _)
      (mul_nonneg hinv (MeasureTheory.integral_nonneg (fun x => sq_nonneg _))))
  · have hfun : (fun p : E3 => (L ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox (n + 1) L,
            ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2))
        = fun p : E3 => (L ^ 3)⁻¹ *
            (∫ x in Submission.BoseGases.abox (n + 1) L,
              ‖Work.SmallBoxTBWord.tBamp χ p Φ i x‖ ^ 2) := rfl
    rw [hfun]
    exact (continuous_const : Continuous (fun _p : E3 => (L ^ 3)⁻¹)).aestronglyMeasurable.mul hJsm
  · refine lt_of_eq_of_lt (MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun p => ?_))) hunweighted
    exact Real.enorm_eq_ofReal (mul_nonneg hinv
      (MeasureTheory.integral_nonneg (fun x => sq_nonneg _)))

/-! ## 6  The requested theorem -/

theorem cutAmplitude_integrable {n : ℕ} {L : ℝ} (hL : 0 < L)
    {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ENat) χ) (hχcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Submission.BoseGases.acube L)
    {Ψ : Submission.BoseGases.X (n+1) → ℝ} (i : Fin (n+1))
    (hΦm : AEMeasurable (Work.SmallBoxTBWord.boxQ volA A i Ψ))
    {B : ℝ} (hB : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      |Work.SmallBoxTBWord.boxQ volA A i Ψ x| ≤ B)
    (hfib : ∀ x ∈ Submission.BoseGases.abox (n+1) L, ContDiff ℝ (⊤ : ENat)
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i z)))
    {C : ℝ} (hC : 0 ≤ C)
    (hdir : ∀ x ∈ Submission.BoseGases.abox (n+1) L,
      (∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
        χ y * Work.SmallBoxTBWord.boxQ volA A i Ψ (Function.update x i y))
          z (Submission.BoseGases.kcStdBasis k)) ^ 2) ≤ C) :
    (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ 2 *
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2)))
    ∧ (MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        ((L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n+1) L,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2))) := by
  have hχ0 : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube L → χ z = 0 := by
    intro z hz
    by_contra h
    exact hz (htsupp (subset_tsupport χ h))
  exact cutAmplitude_integrable_aux hL hχ.continuous hχcs hχ0 i hΦm hB hfib hdir

end Work.BoseFixB1B
