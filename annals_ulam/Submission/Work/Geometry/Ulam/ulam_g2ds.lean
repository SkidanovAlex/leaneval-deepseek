import Mathlib
import Submission.Work.Geometry.Ulam.ulam_volterra_kernels

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped Interval ContDiff Topology

noncomputable section

/-- Measurability of the Abel weight times an arbitrary continuous-on-`(0,1)` kernel. -/
lemma abel_weight_smul_measurable (K : ℝ → UlamState2)
    (hK : ContinuousOn K (Set.Ioo 0 1)) :
    AEStronglyMeasurable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ • K τ)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hcont : ContinuousOn
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ • K τ) (Set.Ioo 0 1) := by
    change ContinuousOn
      ((fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) • K) (Set.Ioo 0 1)
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact ContinuousOn.sqrt (by fun_prop)
      · intro τ hτ
        exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [hτ.1, hτ.2]))
    · exact hK
  have hmeas := hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hmeas
  simpa using hmeas

/-- Integrability of the Abel weight `(√(τ(1-τ)))⁻¹` on `[0,1]`. -/
lemma intervalIntegrable_abel_weight :
    IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 := by
  let f : ℝ → ℝ := fun u => (Real.sqrt (1 - u ^ 2))⁻¹
  have hbase : IntervalIntegrable f volume (-1 : ℝ) 1 := by
    simpa [f] using Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  have h1 : IntervalIntegrable (fun x : ℝ => f (2 * x)) volume ((-1 : ℝ) / 2) (1 / 2) :=
    hbase.comp_mul_left (c := 2) (by norm_num)
  have h2 : IntervalIntegrable (fun x : ℝ => f (2 * (x + -((1 : ℝ) / 2)))) volume (0 : ℝ) 1 := by
    have h := h1.comp_add_right (-(1 / 2 : ℝ)) (by simp)
    convert h using 1 <;> norm_num
  have h3 : IntervalIntegrable (fun x : ℝ => 2 * f (2 * (x + -((1 : ℝ) / 2)))) volume (0 : ℝ) 1 :=
    h2.const_mul 2
  refine h3.congr_uIoo ?_
  intro x hx
  rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have harg : 1 - (2 * (x + -((1 : ℝ) / 2))) ^ 2 = 4 * (x * (1 - x)) := by ring
  have hpos : 0 < x * (1 - x) := by nlinarith
  have hsqrt : Real.sqrt (4 * (x * (1 - x))) = 2 * Real.sqrt (x * (1 - x)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  dsimp [f]
  rw [harg, hsqrt]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]

/-- Interval integrability of the Abel-weighted kernel integrand. -/
lemma ulamG2_integrand_intervalIntegrable
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ : ℝ) (z : UlamState) (x : ℝ)
    (hgood : ∀ τ ∈ Set.Icc (0 : ℝ) 1, x + τ * (σ - x) ∈ ulamKgood h σ z) :
    IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ulamK n h (x + τ * (σ - x)) σ z) volume (0 : ℝ) 1 := by
  have hkernel : ContinuousOn
      (fun τ : ℝ => ulamK n h (x + τ * (σ - x)) σ z) (Set.uIcc (0 : ℝ) 1) := by
    have hkcont : ContinuousOn (fun u : ℝ => ulamK n h u σ z) (ulamKgood h σ z) :=
      (ulamK_contDiffOn_s n hh σ z).continuousOn
    have haff : ContinuousOn (fun τ : ℝ => x + τ * (σ - x)) (Set.uIcc (0 : ℝ) 1) := by
      fun_prop
    have hmaps : Set.MapsTo (fun τ : ℝ => x + τ * (σ - x))
        (Set.uIcc (0 : ℝ) 1) (ulamKgood h σ z) := by
      intro τ hτ
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      exact hgood τ hτ
    exact hkcont.comp haff hmaps
  exact intervalIntegrable_abel_weight.smul_continuousOn hkernel

/-- Measurability of the Abel-weighted kernel integrand. -/
lemma ulamG2_integrand_measurable
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ : ℝ) (z : UlamState) (x : ℝ)
    (hgood : ∀ τ ∈ Set.Icc (0 : ℝ) 1, x + τ * (σ - x) ∈ ulamKgood h σ z) :
    AEStronglyMeasurable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ulamK n h (x + τ * (σ - x)) σ z)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
  have hcont : ContinuousOn
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ulamK n h (x + τ * (σ - x)) σ z) (Set.Ioo 0 1) := by
    change ContinuousOn
      ((fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) •
        (fun τ : ℝ => ulamK n h (x + τ * (σ - x)) σ z)) (Set.Ioo 0 1)
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact ContinuousOn.sqrt (by fun_prop)
      · intro τ hτ
        exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith [hτ.1, hτ.2]))
    · have hkcont : ContinuousOn (fun u : ℝ => ulamK n h u σ z) (ulamKgood h σ z) :=
        (ulamK_contDiffOn_s n hh σ z).continuousOn
      have haff : ContinuousOn (fun τ : ℝ => x + τ * (σ - x)) (Set.Ioo 0 1) := by fun_prop
      have hmaps : Set.MapsTo (fun τ : ℝ => x + τ * (σ - x)) (Set.Ioo 0 1) (ulamKgood h σ z) := by
        intro τ hτ
        exact hgood τ (Set.Ioo_subset_Icc_self hτ)
      exact hkcont.comp haff hmaps
  have hmeas := hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hmeas
  simpa using hmeas

/-- On the interior of the smoothness region, `ulamK` is differentiable in its
first argument with the expected derivative. -/
lemma hasDerivAt_ulamK_of_mem_interior (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (σ : ℝ) (z : UlamState) {x : ℝ} (hx : x ∈ interior (ulamKgood h σ z)) :
    HasDerivAt (fun u : ℝ => ulamK n h u σ z)
      (deriv (fun u : ℝ => ulamK n h u σ z) x) x := by
  have hdiff : DifferentiableAt ℝ (fun u : ℝ => ulamK n h u σ z) x :=
    ((ulamK_contDiffOn_s n hh σ z).differentiableOn (by simp)).differentiableAt
      (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hx) interior_subset)
  exact hdiff.hasDerivAt

/-- Chain rule for the moving-argument evaluation of `ulamK`, assuming the
one-variable derivative of `ulamK` at the moving point. -/
lemma hasDerivAt_ulamK_comp (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : UlamState) (τ x : ℝ)
    (hderiv : HasDerivAt (fun u : ℝ => ulamK n h u σ z)
      (deriv (fun u : ℝ => ulamK n h u σ z) (x + τ * (σ - x))) (x + τ * (σ - x))) :
    HasDerivAt (fun x : ℝ => ulamK n h (x + τ * (σ - x)) σ z)
      ((1 - τ) • deriv (fun u : ℝ => ulamK n h u σ z) (x + τ * (σ - x))) x := by
  have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
    have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x => (1 - τ) * x + τ * σ := by
      ext x; ring
    rw [hfun]
    simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (𝕜' := ℝ) (F := UlamState2)
    (g₁ := fun u : ℝ => ulamK n h u σ z)
    (h := fun x : ℝ => x + τ * (σ - x)) (x := x) hderiv hinner
  simpa [Function.comp_def] using hcomp

/-- The affine map `s ↦ L_s(t) = s t + h s` is continuous when `h` is. -/
lemma continuous_ulamLine_right (h : ℝ → ℝ) (hc : Continuous h) (t : ℝ) :
    Continuous (fun s => ulamLine h s t) := by
  unfold ulamLine; exact (continuous_id.mul continuous_const).add hc

/-- The divided difference `s ↦ ulamHquot h s σ` is continuous off the diagonal `s = σ`. -/
lemma continuousOn_ulamHquot (h : ℝ → ℝ) (hc : Continuous h) (σ : ℝ) :
    ContinuousOn (fun s => ulamHquot h s σ) {s : ℝ | s ≠ σ} := by
  have hset : {s : ℝ | s ≠ σ} = {s : ℝ | σ - s ≠ 0} := by
    ext s; simp only [Set.mem_setOf_eq, sub_ne_zero, ne_eq, eq_comm]
  rw [hset]
  have h1 : ContinuousOn (fun s : ℝ => (h σ - h s) / (σ - s)) {s : ℝ | σ - s ≠ 0} := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.sub hc).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
    · intro y hy; exact hy
  refine h1.congr ?_
  intro y hy
  have hne : ¬ (σ = y) := fun hh => hy (by rw [hh]; ring)
  simp only [ulamHquot]
  rw [if_neg hne]

/-- The smoothness region `ulamKgood` of the state-level kernel is open. -/
lemma isOpen_ulamKgood {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ : ℝ) (z : UlamState) :
    IsOpen (ulamKgood h σ z) := by
  have hcont : Continuous h := hh.continuous
  have hU : IsOpen {s : ℝ | s ≠ σ} := isOpen_ne
  have hq := continuousOn_ulamHquot h hcont σ
  have hBc : ContinuousOn (fun s : ℝ => ((-(z 0)) + ulamHquot h s σ) *
      (ulamLine h σ (-(z 0)) + ulamLine h s (-(z 0)))) {s : ℝ | s ≠ σ} :=
    (continuousOn_const.add hq).mul
      ((continuous_const.add (continuous_ulamLine_right h hcont (-(z 0)))).continuousOn)
  have hDc : ContinuousOn (fun s : ℝ => (z 1 + ulamHquot h s σ) *
      (ulamLine h σ (z 1) + ulamLine h s (z 1))) {s : ℝ | s ≠ σ} :=
    (continuousOn_const.add hq).mul
      ((continuous_const.add (continuous_ulamLine_right h hcont (z 1))).continuousOn)
  have hA : IsOpen ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ =>
      ulamLine h σ (-(z 0)) ^ 2 - ulamLine h s (-(z 0)) ^ 2) ⁻¹' Set.Ioi 0) :=
    hU.inter (isOpen_lt continuous_const
      (continuous_const.sub ((continuous_ulamLine_right h hcont (-(z 0))).pow 2)))
  have hB : IsOpen ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => ((-(z 0)) + ulamHquot h s σ) *
      (ulamLine h σ (-(z 0)) + ulamLine h s (-(z 0)))) ⁻¹' Set.Ioi 0) :=
    ContinuousOn.isOpen_inter_preimage hBc hU isOpen_Ioi
  have hC : IsOpen ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ =>
      ulamLine h σ (z 1) ^ 2 - ulamLine h s (z 1) ^ 2) ⁻¹' Set.Ioi 0) :=
    hU.inter (isOpen_lt continuous_const
      (continuous_const.sub ((continuous_ulamLine_right h hcont (z 1)).pow 2)))
  have hD : IsOpen ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => (z 1 + ulamHquot h s σ) *
      (ulamLine h σ (z 1) + ulamLine h s (z 1))) ⁻¹' Set.Ioi 0) :=
    ContinuousOn.isOpen_inter_preimage hDc hU isOpen_Ioi
  have hgoal : ulamKgood h σ z =
      ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => ulamLine h σ (-(z 0)) ^ 2 - ulamLine h s (-(z 0)) ^ 2) ⁻¹' Set.Ioi 0)
      ∩ ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => ((-(z 0)) + ulamHquot h s σ) * (ulamLine h σ (-(z 0)) + ulamLine h s (-(z 0)))) ⁻¹' Set.Ioi 0)
      ∩ ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => ulamLine h σ (z 1) ^ 2 - ulamLine h s (z 1) ^ 2) ⁻¹' Set.Ioi 0)
      ∩ ({s : ℝ | s ≠ σ} ∩ (fun s : ℝ => (z 1 + ulamHquot h s σ) * (ulamLine h σ (z 1) + ulamLine h s (z 1))) ⁻¹' Set.Ioi 0) := by
    ext s
    simp only [ulamKgood, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi]
    tauto
  rw [hgoal]
  exact ((hA.inter hB).inter hC).inter hD

/-- The first-argument derivative of the state-level kernel `ulamK` is continuous on the
smoothness region. -/
lemma continuousOn_deriv_ulamK (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ : ℝ)
    (z : UlamState) :
    ContinuousOn (fun u : ℝ => deriv (fun u : ℝ => ulamK n h u σ z) u) (ulamKgood h σ z) := by
  have hso := isOpen_ulamKgood hh σ z
  have hfd : ContinuousOn (fun u : ℝ => fderiv ℝ (fun u : ℝ => ulamK n h u σ z) u)
      (ulamKgood h σ z) :=
    (ulamK_contDiffOn_s n hh σ z).continuousOn_fderiv_of_isOpen hso (by norm_num)
  have h1 := hfd.clm_apply
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (1:ℝ)) (ulamKgood h σ z))
  simpa only [fderiv_apply_one_eq_deriv] using h1

/-- **Differentiation under the Abel integral for `G₂`.**

The derivative of `G₂(·, σ, z)` at `s` is the Abel-weighted integral of the
derivative of the kernel along the moving first argument.  The hypotheses
isolate the two analytic inputs: the moving point stays in the smoothness
region `ulamKgood` for `x` near `s` and all `τ ∈ [0,1]`, and the derivative of
the kernel is uniformly bounded on that neighbourhood. -/
lemma ulamG2ds_eq_integral
    (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (σ : ℝ) (z : UlamState) (s : ℝ)
    (hgood : ∀ x ∈ Set.Ioo (s - 1) (s + 1), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      x + τ * (σ - x) ∈ ulamKgood h σ z)
    (hbound : ∃ C : ℝ, ∀ x ∈ Set.Ioo (s - 1) (s + 1), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) • deriv (fun u : ℝ => ulamK n h u σ z) (x + τ * (σ - x))‖ ≤ C) :
    ulamG2ds n h s σ z =
      ∫ τ in (0 : ℝ)..1,
        (Real.sqrt (τ * (1 - τ)))⁻¹ •
          ((1 - τ) • deriv (fun u : ℝ => ulamK n h u σ z) (s + τ * (σ - s))) := by
  obtain ⟨C, hC⟩ := hbound
  have hss : s ∈ Set.Ioo (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hnhds : Set.Ioo (s - 1) (s + 1) ∈ 𝓝 s := isOpen_Ioo.mem_nhds hss
  have hGcont : ContinuousOn (fun τ : ℝ => (1 - τ) •
      deriv (fun u : ℝ => ulamK n h u σ z) (s + τ * (σ - s))) (Set.Ioo 0 1) := by
    have hd : ContinuousOn (fun u : ℝ => deriv (fun u : ℝ => ulamK n h u σ z) u)
        (ulamKgood h σ z) := continuousOn_deriv_ulamK n hh σ z
    have hmap : Set.MapsTo (fun τ : ℝ => s + τ * (σ - s)) (Set.Ioo 0 1) (ulamKgood h σ z) := by
      intro τ hτ; exact hgood s hss τ (Set.Ioo_subset_Icc_self hτ)
    have h1 : ContinuousOn (fun τ : ℝ => deriv (fun u : ℝ => ulamK n h u σ z) (s + τ * (σ - s)))
        (Set.Ioo 0 1) := hd.comp (by fun_prop) hmap
    have h2 : ContinuousOn (fun τ : ℝ => (1 - τ)) (Set.Ioo 0 1) := by fun_prop
    exact h2.smul h1
  have hF'_meas : AEStronglyMeasurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      ((1 - τ) • deriv (fun u : ℝ => ulamK n h u σ z) (s + τ * (σ - s))))
      (volume.restrict (Ι (0:ℝ) 1)) :=
    abel_weight_smul_measurable _ hGcont
  have hF_meas : ∀ᶠ x in 𝓝 s, AEStronglyMeasurable (fun τ : ℝ => (Real.sqrt (τ*(1-τ)))⁻¹ •
      ulamK n h (x + τ*(σ-x)) σ z) (volume.restrict (Ι (0:ℝ) 1)) :=
    Filter.eventually_of_mem hnhds (fun x hx =>
      ulamG2_integrand_measurable n hh σ z x (fun τ hτ => hgood x hx τ hτ))
  have hF_int : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ*(1-τ)))⁻¹ •
      ulamK n h (s + τ*(σ-s)) σ z) volume (0:ℝ) 1 :=
    ulamG2_integrand_intervalIntegrable n hh σ z s (fun τ hτ => hgood s hss τ hτ)
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → ∀ x ∈ Set.Ioo (s-1) (s+1),
      ‖(Real.sqrt (t * (1 - t)))⁻¹ • ((1 - t) • deriv (fun u : ℝ => ulamK n h u σ z) (x + t * (σ - x)))‖
        ≤ C * (Real.sqrt (t * (1 - t)))⁻¹ := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have h1 := hC x hx t htIcc
    have hnn : 0 ≤ (Real.sqrt (t * (1 - t)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc ‖(Real.sqrt (t * (1 - t)))⁻¹ • ((1 - t) • deriv (fun u : ℝ => ulamK n h u σ z) (x + t * (σ - x)))‖
        = ‖(Real.sqrt (t * (1 - t)))⁻¹‖ * ‖(1 - t) • deriv (fun u : ℝ => ulamK n h u σ z) (x + t * (σ - x))‖ := norm_smul _ _
      _ = (Real.sqrt (t * (1 - t)))⁻¹ * ‖(1 - t) • deriv (fun u : ℝ => ulamK n h u σ z) (x + t * (σ - x))‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      _ ≤ (Real.sqrt (t * (1 - t)))⁻¹ * C := mul_le_mul_of_nonneg_left h1 hnn
      _ = C * (Real.sqrt (t * (1 - t)))⁻¹ := by ring
  have hbound_int : IntervalIntegrable (fun τ : ℝ => C * (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0:ℝ) 1 :=
    intervalIntegrable_abel_weight.const_mul C
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0:ℝ) 1 → ∀ x ∈ Set.Ioo (s - 1) (s + 1),
      HasDerivAt (fun x : ℝ => (Real.sqrt (t * (1 - t)))⁻¹ • ulamK n h (x + t * (σ - x)) σ z)
        ((Real.sqrt (t * (1 - t)))⁻¹ • ((1 - t) • deriv (fun u : ℝ => ulamK n h u σ z) (x + t * (σ - x)))) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have htIcc : t ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    have hmem : x + t * (σ - x) ∈ interior (ulamKgood h σ z) := by
      rw [(isOpen_ulamKgood hh σ z).interior_eq]
      exact hgood x hx t htIcc
    have hd := hasDerivAt_ulamK_of_mem_interior n hh σ z hmem
    exact (hasDerivAt_ulamK_comp n h σ z t x hd).const_smul (Real.sqrt (t * (1 - t)))⁻¹
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ • ulamK n h (x + τ * (σ - x)) σ z)
    (F' := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
      ((1 - τ) • deriv (fun u : ℝ => ulamK n h u σ z) (x + τ * (σ - x))))
    (x₀ := s) (s := Set.Ioo (s - 1) (s + 1))
    (bound := fun τ => C * (Real.sqrt (τ * (1 - τ)))⁻¹)
    hnhds hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  show deriv (fun u : ℝ => ulamG2 n h u σ z) s = _
  simp only [ulamG2]
  exact hmain.2.deriv

end

end Commons.Geometry.Ulam
