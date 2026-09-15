import Submission.FUP.HSFunc
import Submission.Commons.MeasureTheory.Lp.eLpNorm_comp_smul_toReal
import Submission.Commons.MeasureTheory.Integral.integral_sq_mul_le_of_indicator_bound

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 5: the one-step gain of the induction on scales

This module contains the *analytic* layer of the one-step gain of Han–Schlag's §5:

* `measurable_Psi` — `Ψ_n` is measurable (it is a convolution, hence a measurable parametric
  integral);
* `toReal_eLpNorm_two` — the bridge `(eLpNorm f 2).toReal = (∫‖f‖²)^{1/2}`;
* `indFun_lower_on_X` / `eLpNorm_indicator_le_indFun` — the factor `(1-c'')^{-m}` relating `f 1_X`
  to `f_m`;
* `integral_indFun_gain` / `gain_norm` — the one-step gain
  `‖f_{m+1}‖ ≤ (1-γ)^{1/2}‖f_m‖` from the localisation estimate on the holes.
-/

namespace Submission.FUP

/-! ## Measurability of the cut-off -/

lemma measurable_PsiC {L : ℕ} (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    Measurable (PsiC Φ L T X n) := by
  have h1 : StronglyMeasurable (fun p : ℝᵈ × ℝᵈ =>
      ((scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) p.2 : ℝ) : ℂ)) :=
    ((Complex.continuous_ofReal.comp (continuous_scaleFun Φ.continuous_reFun _)).comp
      continuous_snd).stronglyMeasurable
  have h2 : StronglyMeasurable (fun p : ℝᵈ × ℝᵈ =>
      (StarS L X (n+1)).indicator (fun _ => (1:ℂ)) (p.1 - p.2)) :=
    ((measurable_const.indicator (measurableSet_StarS L X (n+1))).comp
      (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have h3 : StronglyMeasurable (fun p : ℝᵈ × ℝᵈ =>
      ((scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) p.2 : ℝ) : ℂ) *
      (StarS L X (n+1)).indicator (fun _ => (1:ℂ)) (p.1 - p.2)) := h1.mul h2
  exact (h3.integral_prod_right' (ν := (volume : Measure ℝᵈ))).measurable

lemma measurable_Psi {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    Measurable (Psi Φ L T X n) := by
  have heq : Psi Φ L T X n = fun x => (PsiC Φ L T X n x).re := by
    funext x
    rw [PsiC_eq_ofReal hL Φ T n X]
    exact (Complex.ofReal_re _).symm
  rw [heq]
  exact Complex.continuous_re.measurable.comp (measurable_PsiC Φ T n X)

/-! ## The bridge between `eLpNorm` and the `L²` integral -/

/-- The `L²`-norm of the class of a function is the integral of `‖f‖^2` (the `volume` analogue of
`Submission.FUP.norm_sq_toLp`). -/
lemma norm_sq_toLp_volume {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    ‖hf.toLp f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hint : Integrable (fun z => inner ℂ ((hf.toLp f) z) ((hf.toLp f) z)) volume :=
    MeasureTheory.L2.integrable_inner (hf.toLp f) (hf.toLp f)
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f), MeasureTheory.L2.inner_def,
    ← integral_re hint]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf] with z hz
  rw [hz, inner_self_eq_norm_sq]

lemma toReal_eLpNorm_two_sq {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume) :
    (eLpNorm f 2 (volume : Measure ℝᵈ)).toReal ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have h1 : (eLpNorm f 2 (volume : Measure ℝᵈ)).toReal = ‖hf.toLp f‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hf)]
  rw [h1, norm_sq_toLp_volume hf]

lemma toReal_eLpNorm_two {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume) :
    (eLpNorm f 2 (volume : Measure ℝᵈ)).toReal = Real.sqrt (∫ z, ‖f z‖ ^ 2) :=
  calc (eLpNorm f 2 (volume : Measure ℝᵈ)).toReal
      = Real.sqrt ((eLpNorm f 2 (volume : Measure ℝᵈ)).toReal ^ 2) :=
        (Real.sqrt_sq ENNReal.toReal_nonneg).symm
    _ = Real.sqrt (∫ z, ‖f z‖ ^ 2) := by rw [toReal_eLpNorm_two_sq hf]

/-! ## The pointwise bounds -/

lemma norm_indFun_le {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ) (X : Set ℝᵈ)
    (f : ℝᵈ → ℂ) (z : ℝᵈ) : ‖indFun Φ L T X m f z‖ ≤ ‖f z‖ := by
  rw [indFun, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (cutFam_nonneg hL Φ T m X z)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cutFam_le_one hL Φ T m X z)

/-- **The pointwise lower bound for `f_m` on `X`.** -/
lemma indFun_lower_on_X {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (m : ℕ) (f : ℝᵈ → ℂ) {x : ℝᵈ} (hx : x ∈ X) :
    (1 - tailMass Φ L T) ^ m * ‖f x‖ ≤ ‖indFun Φ L T X m f x‖ := by
  have hlow := cutFam_lower hL hT Φ hX m x hx
  have hnn : 0 ≤ cutFam Φ L T X m x := cutFam_nonneg hL Φ T m X x
  rw [indFun, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_right hlow (norm_nonneg _)

/-- **The factor `(1-c'')^{-m}` relating `f·1_X` to `f_m`.** -/
theorem eLpNorm_indicator_le_indFun {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d)
    {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) (hs : tailMass Φ L T < 1) (m : ℕ) {f : ℝᵈ → ℂ}
    (hf : MemLp f 2 volume) :
    (eLpNorm (X.indicator f) 2 (volume : Measure ℝᵈ)).toReal
      ≤ (((1 - tailMass Φ L T) ^ m)⁻¹)
        * (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal := by
  have hp : 0 < (1 - tailMass Φ L T) ^ m := pow_pos (by linarith) m
  have hpt : ∀ z, ‖(X.indicator f) z‖
      ≤ ‖(((1 - tailMass Φ L T) ^ m)⁻¹) • indFun Φ L T X m f z‖ := by
    intro z
    by_cases hz : z ∈ X
    · rw [Set.indicator_of_mem hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le),
        le_inv_mul_iff₀ hp]
      exact indFun_lower_on_X hL hT Φ hX m f hz
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  have hmem : MemLp (indFun Φ L T X m f) 2 volume := memLp_indFun_two hL Φ T m hX hf
  have hfin : eLpNorm ((((1 - tailMass Φ L T) ^ m)⁻¹) • indFun Φ L T X m f) 2
      (volume : Measure ℝᵈ) ≠ ⊤ := (hmem.const_smul _).eLpNorm_lt_top.ne
  calc (eLpNorm (X.indicator f) 2 (volume : Measure ℝᵈ)).toReal
      ≤ (eLpNorm ((((1 - tailMass Φ L T) ^ m)⁻¹) • indFun Φ L T X m f) 2
          (volume : Measure ℝᵈ)).toReal :=
        ENNReal.toReal_mono hfin (eLpNorm_mono hpt)
    _ = (((1 - tailMass Φ L T) ^ m)⁻¹)
        * (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal := by
        rw [eLpNorm_const_smul, ENNReal.toReal_mul, ← ofReal_norm,
          ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]

/-! ## The one-step gain -/

/-- `√A ≤ √c·√B` when `A ≤ cB` and `A,B ≥ 0`. -/
lemma sqrt_le_sqrt_mul_sqrt {A B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ≤ c * B) :
    Real.sqrt A ≤ Real.sqrt c * Real.sqrt B := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have hB0' : B = 0 := hB0.symm
    have hA0 : A = 0 := le_antisymm (by rw [hB0', mul_zero] at h; exact h) hA
    rw [hA0, hB0']
    simp
  · have hc : 0 ≤ c := by
      by_contra hc
      have hc' : c < 0 := not_le.mp hc
      nlinarith
    calc Real.sqrt A ≤ Real.sqrt (c * B) := Real.sqrt_le_sqrt h
      _ = Real.sqrt c * Real.sqrt B := Real.sqrt_mul hc B

/-- **The one-step gain in integral form.**  If `‖f_m‖²` is controlled by its mass on `U` with
constant `C`, and `Ψ_{mT} ≤ e` on `U`, then the `L²` mass of `f_{m+1} = Ψ_{mT}f_m` drops by the
factor `1 - (1-e²)/C²`. -/
theorem integral_indFun_gain {L T : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (m : ℕ) {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume)
    {e C : ℝ} (he : 0 ≤ e) (hC : 0 < C) {U : Set ℝᵈ} (hUm : MeasurableSet U)
    (hPsiU : ∀ z ∈ U, Psi Φ L T X (m * T) z ≤ e)
    (hbound : ∫ z, ‖indFun Φ L T X m f z‖ ^ 2
      ≤ C ^ 2 * ∫ z in U, ‖indFun Φ L T X m f z‖ ^ 2) :
    ∫ z, ‖indFun Φ L T X (m + 1) f z‖ ^ 2
      ≤ (1 - (1 - e ^ 2) / C ^ 2) * ∫ z, ‖indFun Φ L T X m f z‖ ^ 2 := by
  have h1 : (fun z => Psi Φ L T X (m * T) z ^ 2 * ‖indFun Φ L T X m f z‖ ^ 2)
      = fun z => ‖indFun Φ L T X (m + 1) f z‖ ^ 2 := by
    funext z
    rw [indFun_succ]
    simp only [Pi.mul_apply, psiC]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Psi_nonneg hL Φ T (m * T) X z), mul_pow]
  rw [← h1]
  exact Commons.MeasureTheory.Integral.integral_sq_mul_le_of_indicator_bound
    (memLp_indFun_two hL Φ T m hX hf) (measurable_Psi hL Φ T (m * T) X)
    (Psi_nonneg hL Φ T (m * T) X) (Psi_le_one hL Φ T (m * T) X) he hC hUm hPsiU hbound

/-- **The one-step gain in `L²` norm form.** -/
theorem gain_norm {L T : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (m : ℕ) {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume)
    {e C : ℝ} (he : 0 ≤ e) (hC : 0 < C) {U : Set ℝᵈ} (hUm : MeasurableSet U)
    (hPsiU : ∀ z ∈ U, Psi Φ L T X (m * T) z ≤ e)
    (hbound : ∫ z, ‖indFun Φ L T X m f z‖ ^ 2
      ≤ C ^ 2 * ∫ z in U, ‖indFun Φ L T X m f z‖ ^ 2) :
    (eLpNorm (indFun Φ L T X (m + 1) f) 2 (volume : Measure ℝᵈ)).toReal
      ≤ Real.sqrt (1 - (1 - e ^ 2) / C ^ 2)
        * (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal := by
  have hgain := integral_indFun_gain hL Φ hX m hf he hC hUm hPsiU hbound
  rw [toReal_eLpNorm_two (memLp_indFun_two hL Φ T (m+1) hX hf),
    toReal_eLpNorm_two (memLp_indFun_two hL Φ T m hX hf)]
  refine sqrt_le_sqrt_mul_sqrt (c := 1 - (1 - e ^ 2) / C ^ 2) (by positivity) (by positivity) ?_
  exact hgain

end Submission.FUP
