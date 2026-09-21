import Mathlib
import Submission.Work.OddExistence.Manifest
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddBridge.KvecM_contDiffOn_box
import Submission.Work.OddBridge.dvi_regularity_of_curveData

/-!
# Differentiating the Abel average `G₂M` in its first slot

`G2M n h u σ x y x' y'` is the Abel average
`∫₀¹ KvecM n h (u + τ(σ-u)) σ x y x' y' / √(τ(1-τ)) dτ` of the *manifest* representative
`Work.OddBridge.KvecM` of the paper's odd Abel kernel.  This file computes its `u`-derivative:
differentiating under the integral sign gives the Abel-weighted integral of the `u`-derivative of
the kernel,

`d/du (G2M n h u σ z)_j = ∫₀¹ (√(τ(1-τ)))⁻¹ (1-τ) ∂_u (KvecM n h · σ z)_j (u+τ(σ-u)) dτ`.

Two ingredients are needed.

* `measurable_KvecM_OddBridge`: the `j`-th component of `KvecM` is (Borel) measurable as a
  function of its first slot.  This is what is needed because the abstract differentiation lemma
  under the integral sign requires the integrand to be a.e. strongly measurable; no continuity in
  the first slot is available at points where the Abel denominator `Kden` vanishes, but
  measurability survives since `Kden` is continuous and `x ↦ x⁻¹` is Borel measurable on `ℝ`.
* `hasDerivAt_abelAvg_scalar`: the scalar form of differentiation under the Abel average, the
  `ℝ`-valued companion of `Work.OddExistence.Manifest.AW.aw_hasDerivAt_abelAvg`.

The hypotheses of the target are exactly the two analytic inputs of the latter: along the moving
point `x + τ(σ-x)` the `j`-th component of `KvecM` is bounded by `C` and differentiable, and its
derivative weighted by `1 - τ` is bounded by `C` (the weight `1 - τ` makes the endpoint `τ = 1`
harmless).
-/

namespace Work.OddExistence.Manifest

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **Measurability in the first slot of the manifest kernel of `Work.OddBridge`.**

The `j`-th component of `KvecM n h · σ z` is Borel measurable.  All the constituents are
continuous except the quotient `K₁ = J₁/Kden`, `K₂ = J₂/Kden`, for which measurability of `Kden`
and of `x ↦ x⁻¹` suffices. -/
lemma measurable_KvecM_OddBridge (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (σ : ℝ) (z : Work.OddVolterra.St) (j : Fin 2) :
    Measurable (fun a : ℝ => (Work.OddBridge.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j) := by
  have hquot : Continuous (fun a : ℝ => Work.OddVolterra.hquot h a σ) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hline : ∀ t : ℝ, Continuous (fun a : ℝ => Work.OddVolterra.line h a t) := by
    intro t
    unfold Work.OddVolterra.line
    exact (continuous_id.mul continuous_const).add hh.continuous
  have hKden : ∀ t : ℝ, Measurable (fun a : ℝ => Work.OddVolterra.Kden h a σ t) := by
    intro t
    have hc : Continuous (fun a : ℝ => Work.OddVolterra.Kden h a σ t) := by
      unfold Work.OddVolterra.Kden
      exact Real.continuous_sqrt.comp
        ((continuous_const.add hquot).mul (continuous_const.add (hline t)))
    exact hc.measurable
  have hJ1 : ∀ t : ℝ, Measurable (fun a : ℝ => Work.OddBridge.J1M n h a σ t) := by
    intro t
    have hc : Continuous (fun a : ℝ => Work.OddBridge.J1M n h a σ t) :=
      (Work.OddBridge.contDiff_RR_triple ((n : ℝ) + 1 / 2) hh
        (initC := fun _ _ _ => (1 : ℝ)) contDiff_const (n + 1)).continuous.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    exact hc.measurable
  have hJ2 : ∀ t : ℝ, Measurable (fun a : ℝ => Work.OddBridge.J2M n h a σ t) := by
    intro t
    have hinit : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × ℝ × ℝ => Work.OddVolterra.lineSlope h p.1 p.2.2) := by
      unfold Work.OddVolterra.lineSlope
      fun_prop
    have hc : Continuous (fun a : ℝ => Work.OddBridge.J2M n h a σ t) :=
      (Work.OddBridge.contDiff_RR_triple ((n : ℝ) - 1 / 2) hh
        (initC := fun s _ t => Work.OddVolterra.lineSlope h s t) hinit n).continuous.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    exact hc.measurable
  have hK1 : ∀ t : ℝ, Measurable (fun a : ℝ => Work.OddBridge.K1M n h a σ t) := by
    intro t
    exact (hJ1 t).div (hKden t)
  have hK2 : ∀ t : ℝ, Measurable (fun a : ℝ => Work.OddBridge.K2M n h a σ t) := by
    intro t
    exact (hJ2 t).div (hKden t)
  have hvec : Measurable (fun a : ℝ =>
      Work.OddBridge.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) := by
    rw [show (fun a : ℝ => Work.OddBridge.KvecM n h a σ (z 0) (z 1) (z 2) (z 3))
        = fun a : ℝ => ![- (Work.OddBridge.K1M n h a σ (-(z 0)) * z 2
              + Work.OddBridge.K1M n h a σ (z 1) * z 3),
            - (Work.OddBridge.K2M n h a σ (-(z 0)) * z 2
              + Work.OddBridge.K2M n h a σ (z 1) * z 3)] from by
        funext a i
        fin_cases i <;> rfl]
    rw [measurable_pi_iff]
    intro i
    fin_cases i
    · exact (((hK1 (-(z 0))).mul measurable_const).add
        ((hK1 (z 1)).mul measurable_const)).neg
    · exact (((hK2 (-(z 0))).mul measurable_const).add
        ((hK2 (z 1)).mul measurable_const)).neg
  exact (measurable_pi_apply j).comp hvec

/-- **Differentiation under the Abel average, scalar version.**  If `K : ℝ → ℝ` is measurable,
bounded along the moving point `x + τ(σ-x)`, differentiable there, and its derivative weighted by
`1 - τ` is bounded by `C`, then the Abel average of `K` is differentiable at `s`, with derivative
the Abel-weighted average of the derivative of `K`.

This is the `ℝ`-valued companion of `Work.OddExistence.Manifest.AW.aw_hasDerivAt_abelAvg`. -/
theorem hasDerivAt_abelAvg_scalar {K : ℝ → ℝ} (hK : Measurable K) {s σ : ℝ}
    {δ C : ℝ} (hδ : 0 < δ)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖K (x + τ * (σ - x))‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ K (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv K (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ =>
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * K (u + τ * (σ - u)))
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv K (s + τ * (σ - s)))) s := by
  have hC0 : 0 ≤ C := by
    have h := hbound s ⟨by linarith, by linarith⟩ 1 ⟨zero_le_one, le_rfl⟩
    simpa using h
  have hw_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  have hw_norm : ∀ τ : ℝ, ‖(Real.sqrt (τ * (1 - τ)))⁻¹‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ := by
    intro τ
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
    (Work.OddVolterra.measurable_sqrt_real.comp
      (measurable_id.mul (measurable_const.sub measurable_id))).inv
  set F : ℝ → ℝ → ℝ := fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * K (x + τ * (σ - x)) with hFdef
  set F' : ℝ → ℝ → ℝ :=
    fun x τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * deriv K (x + τ * (σ - x))) with hF'def
  have hF_meas_all : ∀ x : ℝ,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    intro x
    have hm : Measurable (fun τ : ℝ => K (x + τ * (σ - x))) :=
      hK.comp (by fun_prop : Measurable fun τ : ℝ => x + τ * (σ - x))
    exact (hw_meas.mul hm).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in 𝓝 s,
      AEStronglyMeasurable (F x) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    Filter.Eventually.of_forall hF_meas_all
  have hF'_meas : AEStronglyMeasurable (F' s) (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    have hm : Measurable (fun τ : ℝ => deriv K (s + τ * (σ - s))) :=
      (measurable_deriv (𝕜 := ℝ) K).comp
        (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
    exact (hw_meas.mul ((measurable_const.sub measurable_id).mul hm)).aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume (0:ℝ) 1 := by
    refine (hw_int.mul_const C).mono_fun' (hF_meas_all s) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
    by_cases h1 : τ = 1
    · subst h1
      have hz : F s 1 = 0 := by
        simp only [hFdef]
        have hx1 : s + 1 * (σ - s) = σ := by ring
        rw [hx1]
        norm_num
      rw [hz]
      simp
    have hτIco : τ ∈ Set.Ico (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
      exact ⟨le_of_lt hτ.1, lt_of_le_of_ne hτ.2 h1⟩
    have hKb := hbdK s ⟨by linarith, by linarith⟩ τ hτIco
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc ‖F s τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ * ‖K (s + τ * (σ - s))‖ := by
          simp only [hFdef, norm_mul, hw_norm]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hKb hw
  have h_bound : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ),
        ‖F' x τ‖ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      exact ⟨le_of_lt hτ.1, hτ.2⟩
    have hKb := hbound x hx τ hτIcc
    have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc ‖F' x τ‖ = (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ‖(1 - τ) * deriv K (x + τ * (σ - x))‖ := by
          simp only [hF'def, norm_mul, hw_norm]
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := mul_le_mul_of_nonneg_left hKb hw
  have hbound_int : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C) volume (0:ℝ) 1 :=
    hw_int.mul_const C
  have h_diff : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ Set.Ioo (s - δ) (s + δ), HasDerivAt (fun x => F x τ) (F' x τ) x := by
    refine Filter.Eventually.of_forall (fun τ hτ x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
    have hτIcc : τ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hτ.1, hτ.2⟩
    by_cases h1 : τ = 1
    · subst h1
      have hzero : (fun x : ℝ => F x 1) = fun _ : ℝ => (0 : ℝ) := by
        funext y
        simp only [hFdef]
        have hx1 : y + 1 * (σ - y) = σ := by ring
        rw [hx1]
        norm_num
      have hzero' : F' x 1 = 0 := by
        simp only [hF'def, sub_self, mul_zero, zero_mul, Real.sqrt_zero, inv_zero]
      rw [hzero, hzero']
      exact hasDerivAt_const x 0
    · have hτlt : τ < 1 := lt_of_le_of_ne hτIcc.2 h1
      have hinner : HasDerivAt (fun x : ℝ => x + τ * (σ - x)) (1 - τ) x := by
        have hfun : (fun x : ℝ => x + τ * (σ - x)) = fun x : ℝ => (1 - τ) * x + τ * σ := by
          funext y; ring
        rw [hfun]
        simpa using ((hasDerivAt_id x).const_mul (1 - τ)).add_const (τ * σ)
      have houter : HasDerivAt K (deriv K (x + τ * (σ - x))) (x + τ * (σ - x)) :=
        (hdiff x hx τ ⟨hτIcc.1, hτlt⟩).hasDerivAt
      have hcomp := houter.scomp (𝕜 := ℝ) (F := ℝ) (x := x) hinner
      have hfull := hcomp.const_mul ((Real.sqrt (τ * (1 - τ)))⁻¹)
      refine hfull.congr_deriv ?_
      simp only [hFdef, hF'def]
      ring
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0:ℝ)) (b := 1) (μ := volume)
    (F := F) (F' := F') (x₀ := s) (s := Set.Ioo (s - δ) (s + δ))
    (bound := fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C)
    (isOpen_Ioo.mem_nhds ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  simpa only [hFdef, hF'def] using hmain.2

/-- **The `j`-th component of `G₂M` is differentiable in the first slot**, with the
Abel-weighted average of the derivative of the `j`-th component of the kernel as its derivative.

The hypotheses are the two analytic inputs of differentiation under the Abel integral: along the
moving point `x + τ(σ-x)` the `j`-th component of `KvecM` is bounded by `C` and differentiable,
and its derivative weighted by `1 - τ` is bounded by `C`. -/
theorem hasDerivAt_G2M_apply (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {s σ : ℝ} (z : Work.OddVolterra.St) (j : Fin 2) {δ C : ℝ} (hδ : 0 < δ)
    (hbdK : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖(Work.OddBridge.KvecM n h (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)) j‖ ≤ C)
    (hdiff : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) (x + τ * (σ - x)))
    (hbound : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) (x + τ * (σ - x))‖ ≤ C) :
    HasDerivAt (fun u : ℝ => (Work.OddBridge.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) j)
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u : ℝ =>
          (Work.OddBridge.KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) (s + τ * (σ - s)))) s := by
  have hK : Measurable (fun a : ℝ =>
      (Work.OddBridge.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j) :=
    measurable_KvecM_OddBridge n hh σ z j
  have hmain := hasDerivAt_abelAvg_scalar
    (K := fun a : ℝ => (Work.OddBridge.KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)
    hK hδ hbdK hdiff hbound
  have hfun : (fun u : ℝ => (Work.OddBridge.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) j)
      = fun u : ℝ => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          (Work.OddBridge.KvecM n h (u + τ * (σ - u)) σ (z 0) (z 1) (z 2) (z 3)) j := by
    funext u
    simp only [Work.OddBridge.G2M]
    exact intervalIntegral.integral_congr (fun τ _ => by rw [div_eq_inv_mul])
  rw [hfun]
  exact hmain

end

end Work.OddExistence.Manifest
