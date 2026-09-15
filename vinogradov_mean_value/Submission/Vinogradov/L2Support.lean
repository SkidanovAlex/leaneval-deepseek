/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.L2Base
import Submission.Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The frequency support of an `L²` member of the class `𝒞(U)`

This module proves that an `L²` function `f` which is the Fourier transform of a finite measure
supported in `U` has its `L²` Fourier transform supported in `U`:

  `𝓕 f = 0` almost everywhere off `U`.

The proof is the textbook one:

* from the pairing identity `L2Base.repFun_integral_fourier_mul_conj`, a Schwartz test function
  vanishing on `U` pairs trivially with `𝓕 f`;
* multiplying a Schwartz test function by a *smooth temperate* cutoff `χ` vanishing on `U` keeps
  it Schwartz (and vanishing on `U`), so `(𝓕f)·χ` pairs trivially with *every* Schwartz function;
* density of Schwartz functions in `L²` upgrades this to `(𝓕f)·χ = 0` in `L²`;
* a sequence `χ_n` of such cutoffs with `χ_n → 1` pointwise off `U` concludes.
-/

noncomputable section
open MeasureTheory FourierTransform Complex Classical Filter
open scoped FourierTransform RealInnerProductSpace InnerProductSpace BigOperators ENNReal NNReal
open scoped ContDiff

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Submission.Vinogradov

/-- The `L²` Fourier transform of an `L²` function. -/
noncomputable def fourierLp {k : ℕ} {f : E k → ℂ} (hf2 : MemLp f 2 (volume : Measure (E k))) :
    Lp ℂ 2 (volume : Measure (E k)) :=
  𝓕 (hf2.toLp f)

/-! ## 1. Temperate cutoffs acting on Schwartz functions -/

/-- A temperate function scales a Schwartz function to a Schwartz function. -/
lemma smulLeftCLM_apply_eq {k : ℕ} {χ : E k → ℝ} (hχ : Function.HasTemperateGrowth χ)
    (ψ : SchwartzMap (E k) ℂ) (x : E k) :
    (SchwartzMap.smulLeftCLM ℂ χ ψ) x = (χ x : ℂ) * ψ x := by
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ]
  simp

/-- The conjugate of a scaled Schwartz function. -/
lemma star_smulLeftCLM_apply {k : ℕ} {χ : E k → ℝ} (hχ : Function.HasTemperateGrowth χ)
    (ψ : SchwartzMap (E k) ℂ) (x : E k) :
    star ((SchwartzMap.smulLeftCLM ℂ χ ψ) x) = (χ x : ℂ) * star (ψ x) := by
  rw [smulLeftCLM_apply_eq hχ, star_mul, Complex.star_def, Complex.conj_ofReal]; ring

/-! ## 2. The pairing with a cutoff vanishes -/

set_option maxHeartbeats 4000000 in
/-- **`𝓕 f` times a cutoff vanishing on `U` is zero.**  For `f = repFun k Γ ν φ ∈ L²` with
`Γ` supported in `U`, and any smooth cutoff `χ` which is bounded by `1` and vanishes on `U`,
the product `(𝓕 f) · χ` vanishes almost everywhere. -/
theorem fourierLp_mul_cutoff_ae_zero {k : ℕ} {ι : Type*} [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} [IsFiniteMeasure ν] {φ : ι → ℂ} {U : Set (E k)}
    (hφ : Integrable φ ν) (hΓ : Measurable Γ) (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U)
    (hf2 : MemLp (repFun k Γ ν φ) 2 (volume : Measure (E k)))
    {χ : E k → ℝ} (hχ : Function.HasTemperateGrowth χ)
    (hχU : ∀ ξ ∈ U, χ ξ = 0) (hχbd : ∀ ξ, ‖χ ξ‖ ≤ 1) :
    (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ)) =ᵐ[volume] (0 : E k → ℂ) := by
  have hfLmem : MemLp (fourierLp hf2 : E k → ℂ) 2 (volume : Measure (E k)) := Lp.memLp _
  have hgmeas : AEStronglyMeasurable
      (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ)) volume :=
    hfLmem.aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp hχ.1.continuous).measurable.aestronglyMeasurable)
  have hg2 : MemLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ)) 2 (volume : Measure (E k)) :=
    hfLmem.of_le hgmeas (Filter.Eventually.of_forall fun ξ => by
      have h1 : ‖(χ ξ : ℂ)‖ = ‖χ ξ‖ := by simp
      rw [norm_mul, h1]
      exact mul_le_of_le_one_right (norm_nonneg _) (hχbd ξ))
  have hkey : ∀ ψ : SchwartzMap (E k) ℂ,
      inner ℂ ((SchwartzMap.memLp ψ 2 (volume : Measure (E k))).toLp ψ)
        (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0 := by
    intro ψ
    let χψ : SchwartzMap (E k) ℂ := SchwartzMap.smulLeftCLM ℂ χ ψ
    have hvan : ∀ ξ ∈ U, χψ ξ = 0 := by
      intro ξ hξ
      show (SchwartzMap.smulLeftCLM ℂ χ ψ) ξ = 0
      rw [smulLeftCLM_apply_eq hχ, hχU ξ hξ, Complex.ofReal_zero, zero_mul]
    have h0 := repFun_integral_fourier_mul_conj_of_vanishing hφ hΓ hU hf2 hvan
    rw [inner_Lp_eq_integral]
    refine Eq.trans ?_ h0
    refine integral_congr_ae ?_
    filter_upwards [hg2.coeFn_toLp,
      (SchwartzMap.memLp ψ 2 (volume : Measure (E k))).coeFn_toLp] with x h1 h2
    rw [h1, h2]
    show ((fourierLp hf2 : E k → ℂ) x * (χ x : ℂ)) * star (ψ x)
      = (fourierLp hf2 : E k → ℂ) x * star (χψ x)
    rw [show χψ = SchwartzMap.smulLeftCLM ℂ χ ψ from rfl, star_smulLeftCLM_apply hχ]
    ring
  have hg2zero : (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0 := by
    have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (E k))) :=
      SchwartzMap.denseRange_toLpCLM (p := 2) (by norm_num) (μ := (volume : Measure (E k)))
    have hclosed : IsClosed {u : Lp ℂ 2 (volume : Measure (E k)) |
        inner ℂ u (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hsub : Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (E k))) ⊆
        {u : Lp ℂ 2 (volume : Measure (E k)) |
          inner ℂ u (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0} := by
      rintro _ ⟨ψ, rfl⟩
      rw [SchwartzMap.toLpCLM_apply]
      exact hkey ψ
    have hall : ∀ u : Lp ℂ 2 (volume : Measure (E k)),
        inner ℂ u (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0 := by
      intro u
      have hone : (Set.univ : Set (Lp ℂ 2 (volume : Measure (E k)))) ⊆
          {u : Lp ℂ 2 (volume : Measure (E k)) |
            inner ℂ u (hg2.toLp (fun ξ => (fourierLp hf2 : E k → ℂ) ξ * (χ ξ : ℂ))) = 0} := by
        rw [← hdense.closure_range]
        exact closure_minimal hsub hclosed
      exact hone (Set.mem_univ u)
    exact inner_self_eq_zero.mp (hall _)
  exact hg2.coeFn_toLp.symm.trans (Eq.symm hg2zero ▸ Lp.coeFn_zero ℂ 2 (volume : Measure (E k)))

/-! ## 3. A family of cutoffs exhausts the complement -/

/-- If `χ n` is a family of smooth cutoffs, all vanishing and bounded on `U`, which is `1`
somewhere off `U` for every point off `U`, then `𝓕 f` vanishes off `U`. -/
theorem fourierLp_ae_eq_zero_off {k : ℕ} {ι : Type*} [MeasurableSpace ι]
    {Γ : ι → E k} {ν : Measure ι} [IsFiniteMeasure ν] {φ : ι → ℂ} {U : Set (E k)}
    (hφ : Integrable φ ν) (hΓ : Measurable Γ) (hU : ∀ u, φ u ≠ 0 → Γ u ∈ U)
    (hf2 : MemLp (repFun k Γ ν φ) 2 (volume : Measure (E k)))
    (χ : ℕ → E k → ℝ) (hχ : ∀ n, Function.HasTemperateGrowth (χ n))
    (hχU : ∀ n ξ, ξ ∈ U → χ n ξ = 0) (hχbd : ∀ n ξ, ‖χ n ξ‖ ≤ 1)
    (hχ1 : ∀ ξ, ξ ∉ U → ∃ n, χ n ξ = 1) :
    ∀ᵐ ξ ∂(volume : Measure (E k)), ξ ∉ U → (fourierLp hf2 : E k → ℂ) ξ = 0 := by
  have h : ∀ n, ∀ᵐ ξ ∂(volume : Measure (E k)),
      (fourierLp hf2 : E k → ℂ) ξ * (χ n ξ : ℂ) = 0 := fun n =>
    fourierLp_mul_cutoff_ae_zero hφ hΓ hU hf2 (hχ n) (hχU n) (hχbd n)
  rw [← MeasureTheory.ae_all_iff] at h
  filter_upwards [h] with ξ hξ hξU
  obtain ⟨n, hn⟩ := hχ1 ξ hξU
  have := hξ n
  rwa [hn, Complex.ofReal_one, mul_one] at this

/-! ## 4. Frequency support for the class `𝒞(U)` -/

/-- The smooth cutoff family of `exists_smooth_cutoff_infDist_scale` is of temperate growth
(its iterated derivatives are uniformly bounded). -/
lemma hasTemperateGrowth_of_bounded_iteratedFDeriv {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → ℝ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ n : ℕ, ∃ A : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ A) :
    Function.HasTemperateGrowth f := by
  refine ⟨hf, fun n => ?_⟩
  obtain ⟨A, hA⟩ := h n
  exact ⟨0, A, fun x => by simpa using hA x⟩

/-- A smooth function all of whose iterated derivatives are bounded on the level sets of a
family is temperate; here we simply record the version used below. -/
lemma hasTemperateGrowth_of_derivBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (θ : ℝ → X → ℝ)
    (hcd : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (θ r))
    (hder : ∀ j : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 < r → ∀ x,
      ‖iteratedFDeriv ℝ j (θ r) x‖ ≤ A / r ^ j)
    {r : ℝ} (hr : 0 < r) : Function.HasTemperateGrowth (θ r) := by
  refine hasTemperateGrowth_of_bounded_iteratedFDeriv (hcd r hr) (fun n => ?_)
  obtain ⟨A, hA0, hA⟩ := hder n
  refine ⟨A / r ^ n, fun x => ?_⟩
  exact hA r hr x

set_option maxHeartbeats 4000000 in
/-- **The frequency support of an `L²` member of `𝒞(U)`.**  If `f` is the Fourier transform of
a finite measure supported in `U` and `f ∈ L²`, then the `L²` Fourier transform of `f` vanishes
almost everywhere off the points at positive distance from `U`. -/
theorem IsFourierRep.fourierLp_ae_eq_zero_off {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    (hf : IsFourierRep k U f) (hf2 : MemLp f 2 (volume : Measure (E k)))
    (hUpos : ∀ ξ ∉ U, 0 < Metric.infDist ξ U) :
    ∀ᵐ ξ ∂(volume : Measure (E k)), ξ ∉ U →
      ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) ξ = 0 := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hUΓ, hfq⟩ := hf
  haveI := hν
  have hfeq : f = repFun k Γ ν φ := funext fun x => (hfq x).trans rfl
  subst hfeq
  obtain ⟨θ, hθcd, hθbd, hθzero, hθone, hθder⟩ :=
    Commons.Analysis.Calculus.BumpFunction.exists_smooth_cutoff_infDist_scale Uᶜ
  refine Submission.Vinogradov.fourierLp_ae_eq_zero_off hφ hΓ hUΓ hf2 (fun n => θ (1 / (n + 1 : ℝ)))
    (fun n => hasTemperateGrowth_of_derivBound θ hθcd hθder (by positivity))
    ?_ ?_ ?_
  · intro n ξ hξ
    refine hθzero (1 / (n + 1 : ℝ)) (by positivity) ξ ?_
    rw [compl_compl]
    exact le_trans (le_of_eq (Metric.infDist_zero_of_mem hξ)) (by positivity)
  · intro n ξ
    rw [Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := hθbd (1 / (n + 1 : ℝ)) (by positivity) ξ
    exact abs_le.mpr ⟨by linarith, h2⟩
  · intro ξ hξ
    have hpos : 0 < Metric.infDist ξ U := hUpos ξ hξ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < Metric.infDist ξ U / 3)
    refine ⟨n, hθone (1 / (n + 1 : ℝ)) (by positivity) ξ ?_⟩
    rw [compl_compl]
    have hn' : (1 : ℝ) / (n + 1) < Metric.infDist ξ U / 3 := hn
    linarith

/-- **The frequency support of an `L²` member of `𝒞(U)`** for compact `U`. -/
theorem IsFourierRep.fourierLp_ae_eq_zero_off_of_isCompact {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    (hf : IsFourierRep k U f) (hf2 : MemLp f 2 (volume : Measure (E k)))
    (hUc : IsCompact U) (hUne : U.Nonempty) :
    ∀ᵐ ξ ∂(volume : Measure (E k)), ξ ∉ U →
      ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) ξ = 0 :=
  hf.fourierLp_ae_eq_zero_off hf2 fun ξ hξ =>
    (Metric.infDist_pos_iff_notMem_closure hUne).mp (by rwa [hUc.isClosed.closure_eq])

/-! ## 5. Orthogonality of classes with essentially disjoint frequency support -/

set_option maxHeartbeats 4000000 in
/-- **`L²` orthogonality of `𝒞(U)` and `𝒞(V)` for essentially disjoint `U, V`.** -/
theorem inner_eq_zero_of_isFourierRep_of_disjoint {k : ℕ} {U V : Set (E k)} {f g : E k → ℂ}
    (hf : IsFourierRep k U f) (hg : IsFourierRep k V g)
    (hf2 : MemLp f 2 (volume : Measure (E k))) (hg2 : MemLp g 2 (volume : Measure (E k)))
    (hUpos : ∀ ξ ∉ U, 0 < Metric.infDist ξ U) (hVpos : ∀ ξ ∉ V, 0 < Metric.infDist ξ V)
    (hUV : volume (U ∩ V) = 0) :
    inner ℂ (hf2.toLp f) (hg2.toLp g) = 0 := by
  rw [← Lp.inner_fourier_eq (hf2.toLp f) (hg2.toLp g)]
  have hf0 := hf.fourierLp_ae_eq_zero_off hf2 hUpos
  have hg0 := hg.fourierLp_ae_eq_zero_off hg2 hVpos
  have hUV' : ∀ᵐ x ∂(volume : Measure (E k)), x ∉ U ∩ V := by
    rw [MeasureTheory.ae_iff]
    simpa using hUV
  have hzero : (fun x : E k => ((𝓕 (hg2.toLp g) : Lp ℂ 2 (volume : Measure (E k))) : E k → ℂ) x
      * star ((((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure (E k)))) : E k → ℂ) x))
      =ᵐ[volume] 0 := by
    filter_upwards [hf0, hg0, hUV'] with x hfx hgx hxUV
    simp only [Pi.zero_apply]
    by_cases hxU : x ∈ U
    · have hxV : x ∉ V := fun hx => hxUV ⟨hxU, hx⟩
      simp only [hgx hxV, zero_mul]
    · simp only [hfx hxU, star_zero, mul_zero]
  rw [inner_Lp_eq_integral, integral_congr_ae hzero]
  simp only [Pi.zero_apply, integral_zero]

end Submission.Vinogradov
