import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The second Fréchet derivative of a parameter integral along lines

For `ω : E → ℝ` of class `C²` with compact support and `a b V W : E` with `b ≠ 0`, the function
```
p ↦ ∫ u, ω (p.1 + u • p.2) * (1 + u^2)⁻¹
```
on `E × E` is twice differentiable, and its second derivative at `(a, b)`, evaluated on the
diagonal vector `(V, W)`, is the integral of the corresponding second derivative of `ω`:
```
D²(∫ u, ω ((a,b) + u • ...)) (V,W)(V,W) = ∫ u, D²ω (a + u • b) (V + u • W)(V + u • W) * (1+u²)⁻¹.
```

The proof differentiates twice under the integral sign, using Mathlib's parametric-integral
lemmas.  The derivative lives in the space of continuous linear maps `(E × E) →L ((E × E) →L ℝ)`,
for which Mathlib currently lacks the `ContinuousENorm` instance required by `MeasureTheory.Integrable`
(the existing instance goes through the operator-norm topology, which is only propositionally equal
to the topology of bounded convergence used for continuous linear maps).  We provide that instance
(`IFD2.instContinuousENormCLM`) as part of this file; it is of independent interest.

## Main results

* `Commons.Analysis.Calculus.IFD2.instContinuousENormCLM`: continuous linear maps between normed
  spaces are `ContinuousENorm`.
* `Commons.Analysis.Calculus.IFD2.hasFDerivAt_paramIntegral`, `..._deriv`: the first and second
  derivatives of the parameter integral.
* `Commons.Analysis.Calculus.iteratedFDeriv_two_integral_add_smul_general` and
  `Commons.Analysis.Calculus.iteratedFDeriv_two_integral_add_smul`.
-/

set_option maxHeartbeats 400000

open MeasureTheory Metric Filter Bornology
open scoped Topology

namespace Commons.Analysis.Calculus
namespace IFD2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


section ContinuousENormCLM

variable {E₀ F₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
  [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]

lemma norm_lt_mem_nhds_zero_CLM (ε : ℝ) (hε : 0 < ε) :
    {f : E₀ →L[ℝ] F₀ | ‖f‖ < ε} ∈ 𝓝 (0 : E₀ →L[ℝ] F₀) := by
  have hε2 : (0:ℝ) < ε/2 := by linarith
  have h1 : IsVonNBounded ℝ (closedBall (0:E₀) 1) :=
    NormedSpace.isVonNBounded_closedBall ℝ E₀ 1
  have h2 : ball (0:F₀) (ε/2) ∈ 𝓝 (0 : F₀) := ball_mem_nhds 0 hε2
  refine ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mpr
    ⟨(closedBall (0:E₀) 1, ball (0:F₀) (ε/2)), ⟨h1, h2⟩, ?_⟩
  intro f hf
  have hle : ‖f‖ ≤ ε/2 := by
    refine ContinuousLinearMap.opNorm_le_bound f hε2.le fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hx1 : (‖x‖)⁻¹ • x ∈ closedBall (0:E₀) 1 := by
        rw [mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        rw [inv_mul_cancel₀ (ne_of_gt hxpos)]
      have hh := hf _ hx1
      rw [mem_ball, dist_eq_norm, sub_zero] at hh
      have h2 : ‖f ((‖x‖)⁻¹ • x)‖ = (‖x‖)⁻¹ * ‖f x‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
      rw [h2] at hh
      have h3 : ‖f x‖ < ε/2 * ‖x‖ := by
        calc ‖f x‖ = ‖x‖ * ((‖x‖)⁻¹ * ‖f x‖) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hxpos), one_mul]
          _ < ‖x‖ * (ε/2) := mul_lt_mul_of_pos_left hh hxpos
          _ = ε/2 * ‖x‖ := by ring
      exact le_of_lt h3
  exact lt_of_le_of_lt hle (by linarith)

lemma continuous_norm_CLM : Continuous (fun f : E₀ →L[ℝ] F₀ => ‖f‖) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt]
  have h1 : map (fun g : E₀ →L[ℝ] F₀ => f + g) (𝓝 0) = 𝓝 f := by
    simpa using map_add_left_nhds (0 : E₀ →L[ℝ] F₀) f
  rw [← h1, Filter.tendsto_map'_iff]
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_iff_exists_mem]
  refine ⟨{g : E₀ →L[ℝ] F₀ | ‖g‖ < ε}, norm_lt_mem_nhds_zero_CLM ε hε, ?_⟩
  intro g hg
  simp only [Function.comp_apply]
  rw [Real.dist_eq, abs_lt]
  have hg' : ‖g‖ < ε := hg
  have h2 : ‖f + g‖ ≤ ‖f‖ + ‖g‖ := ContinuousLinearMap.opNorm_add_le f g
  have h3 : ‖f‖ ≤ ‖f + g‖ + ‖g‖ := by
    have h4 : (f + g) - g = f := by abel
    calc ‖f‖ = ‖(f + g) - g‖ := by rw [h4]
      _ ≤ ‖f + g‖ + ‖g‖ := norm_sub_le _ _
  constructor <;> linarith [hg', norm_nonneg g]

/-- The space of continuous linear maps between normed spaces is `ContinuousENorm` for its
topology of bounded convergence.  (Mathlib only provides the instance through the operator-norm
topology, which is not definitionally equal to the topology of bounded convergence.) -/
noncomputable instance instContinuousENormCLM :
    ContinuousENorm (E₀ →L[ℝ] F₀) where
  __ := (inferInstance : ENorm (E₀ →L[ℝ] F₀))
  continuous_enorm := by
    have h0 : Continuous (fun f : E₀ →L[ℝ] F₀ => ‖f‖) := continuous_norm_CLM
    have h1 : Continuous (fun f : E₀ →L[ℝ] F₀ => (Real.toNNReal ‖f‖ : NNReal)) :=
      continuous_real_toNNReal.comp h0
    have h2 : Continuous (fun f : E₀ →L[ℝ] F₀ =>
        ((Real.toNNReal ‖f‖ : NNReal) : ENNReal)) :=
      ENNReal.continuous_coe.comp h1
    convert h2 using 1
    ext f
    rw [enorm_eq_nnnorm, Real.toNNReal_of_nonneg (norm_nonneg f)]
    rfl

end ContinuousENormCLM

/-! ## Basic objects -/

/-- The weight `u ↦ (1 + u^2)⁻¹`. -/
noncomputable def paramWeight (u : ℝ) : ℝ := (1 + u ^ 2)⁻¹

/-- The continuous linear map `p ↦ p.1 + u • p.2` on `E × E`. -/
noncomputable def paramLine (u : ℝ) : E × E →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E E + u • ContinuousLinearMap.snd ℝ E E

/-- The continuous linear map `A ↦ A.comp (paramLine u)`. -/
noncomputable def paramPrecomp (u : ℝ) : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ (E × E) E ℝ).flip (paramLine u)

@[simp] lemma paramLine_apply (u : ℝ) (p : E × E) : paramLine u p = p.1 + u • p.2 := by
  simp [paramLine]

lemma paramPrecomp_apply (u : ℝ) (A : E →L[ℝ] ℝ) :
    paramPrecomp u A = A.comp (paramLine u) := by
  simp [paramPrecomp, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

lemma paramWeight_nonneg (u : ℝ) : 0 ≤ paramWeight u := by
  rw [paramWeight]; positivity

lemma paramWeight_pos (u : ℝ) : 0 < paramWeight u := by
  rw [paramWeight]; positivity

lemma paramWeight_le_one (u : ℝ) : paramWeight u ≤ 1 := by
  rw [paramWeight]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg u])

lemma paramWeight_continuous : Continuous paramWeight := by
  change Continuous (fun u : ℝ => (1 + u ^ 2)⁻¹)
  exact (by fun_prop : Continuous fun u : ℝ => (1 + u ^ 2 : ℝ)).inv₀ (fun u => by positivity)

lemma integrable_paramWeight : Integrable paramWeight volume := by
  change Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) volume
  exact integrable_inv_one_add_sq

lemma continuous_paramLine :
    Continuous (fun u : ℝ => (paramLine u : E × E →L[ℝ] E)) := by
  have h : (fun u : ℝ => (paramLine u : E × E →L[ℝ] E))
      = fun u : ℝ => ContinuousLinearMap.fst ℝ E E + u • ContinuousLinearMap.snd ℝ E E := by
    funext u; simp [paramLine]
  rw [h]; fun_prop

lemma continuous_paramWeight_smul_paramLine :
    Continuous (fun u : ℝ => paramWeight u • (paramLine u : E × E →L[ℝ] E)) := by
  have h : (fun u : ℝ => paramWeight u • (paramLine u : E × E →L[ℝ] E))
      = fun u : ℝ => paramWeight u • (ContinuousLinearMap.fst ℝ E E
          + u • ContinuousLinearMap.snd ℝ E E) := by
    funext u; simp [paramLine]
  rw [h]
  exact paramWeight_continuous.smul (by fun_prop)

lemma hasFDerivAt_paramLine (u : ℝ) (q : E × E) :
    HasFDerivAt (fun q' : E × E => q'.1 + u • q'.2) (paramLine u) q := by
  have h := (paramLine u : E × E →L[ℝ] E).hasFDerivAt (x := q)
  convert h using 1
  funext q'; simp

lemma paramLine_norm_le (u : ℝ) :
    ‖(paramLine u : E × E →L[ℝ] E)‖ ≤ 1 + |u| := by
  have h : (paramLine u : E × E →L[ℝ] E)
      = ContinuousLinearMap.fst ℝ E E + u • ContinuousLinearMap.snd ℝ E E := by
    simp [paramLine]
  rw [h]
  calc ‖ContinuousLinearMap.fst ℝ E E + u • ContinuousLinearMap.snd ℝ E E‖
      ≤ ‖ContinuousLinearMap.fst ℝ E E‖ + ‖u • ContinuousLinearMap.snd ℝ E E‖ := norm_add_le _ _
    _ ≤ 1 + |u| := by
        rw [norm_smul, Real.norm_eq_abs]
        have h1 : ‖ContinuousLinearMap.fst ℝ E E‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ E E
        have h2 : ‖ContinuousLinearMap.snd ℝ E E‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ E E
        nlinarith [abs_nonneg u]

lemma paramLine_apply_norm_le (u : ℝ) (p : E × E) :
    ‖paramLine u p‖ ≤ (1 + |u|) * ‖p‖ := by
  rw [paramLine_apply]
  calc ‖p.1 + u • p.2‖ ≤ ‖p.1‖ + ‖u • p.2‖ := norm_add_le _ _
    _ = ‖p.1‖ + |u| * ‖p.2‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖p‖ + |u| * ‖p‖ := by
        gcongr
        · exact norm_fst_le p
        · exact norm_snd_le p
    _ = (1 + |u|) * ‖p‖ := by ring

lemma paramPrecomp_norm_le (u : ℝ) :
    ‖(paramPrecomp u : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ))‖ ≤ 1 + |u| := by
  have h : (paramPrecomp u : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ))
      = (ContinuousLinearMap.compL ℝ (E × E) E ℝ).flip (paramLine u) := by
    simp [paramPrecomp]
  rw [h]
  calc ‖(ContinuousLinearMap.compL ℝ (E × E) E ℝ).flip (paramLine u)‖
      ≤ ‖(ContinuousLinearMap.compL ℝ (E × E) E ℝ).flip‖ * ‖(paramLine u : E × E →L[ℝ] E)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * (1 + |u|) := by
        gcongr
        · rw [ContinuousLinearMap.opNorm_flip]
          exact ContinuousLinearMap.norm_compL_le ℝ (E × E) E ℝ
        · exact paramLine_norm_le u
    _ = 1 + |u| := by ring

lemma continuous_paramPrecomp :
    Continuous (fun u : ℝ => (paramPrecomp u : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ))) := by
  have h : (fun u : ℝ => (paramPrecomp u : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ)))
      = fun u : ℝ => ((ContinuousLinearMap.flipₗᵢ ℝ (E →L[ℝ] ℝ) ((E × E) →L[ℝ] E)
          ((E × E) →L[ℝ] ℝ)) (ContinuousLinearMap.compL ℝ (E × E) E ℝ)) (paramLine u) := by
    funext u; simp [paramPrecomp, ContinuousLinearMap.coe_flipₗᵢ]
  rw [h]
  exact (ContinuousLinearMap.continuous _).comp continuous_paramLine

/-! ## Compact support: vanishing and boundedness -/

lemma exists_support_radius {F : Type*} [NormedAddCommGroup F] {f : E → F}
    (hcpt : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : E, R < ‖z‖ → f z = 0 := by
  obtain ⟨r, hr⟩ : ∃ r, tsupport f ⊆ closedBall 0 r :=
    (isBounded_iff_subset_closedBall (0 : E)).mp hcpt.isCompact.isBounded
  refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
  have hzr : r < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hz' : z ∉ tsupport f := by
    intro hmem
    have hmem' := hr hmem
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hmem'
    linarith
  exact image_eq_zero_of_notMem_tsupport hz'

lemma fderiv_eq_zero_of_notMem_tsupport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {z : E} (hz : z ∉ tsupport g) : fderiv ℝ g z = 0 := by
  have h : g =ᶠ[𝓝 z] (0 : E → F) := by
    rwa [← notMem_tsupport_iff_eventuallyEq]
  simpa using h.fderiv_eq

lemma tsupport_fderiv_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) :
    tsupport (fderiv ℝ g) ⊆ tsupport g := by
  refine closure_minimal (fun z hz => ?_) (isClosed_tsupport g)
  rw [Function.mem_support] at hz
  by_contra hz'
  exact hz (fderiv_eq_zero_of_notMem_tsupport hz')

/-- Outside a ball of radius `R`, `ω`, `fderiv ω` and `fderiv (fderiv ω)` all vanish. -/
lemma support_radius_of_contDiff {ω : E → ℝ} (hcpt : HasCompactSupport ω) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : E, R < ‖z‖ →
      ω z = 0 ∧ fderiv ℝ ω z = 0 ∧ fderiv ℝ (fderiv ℝ ω) z = 0 := by
  obtain ⟨R, hR, hvan⟩ := exists_support_radius hcpt
  have hsupp : Function.support ω ⊆ closedBall (0 : E) R := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    by_contra h
    exact hz (hvan z (lt_of_not_ge h))
  have htsub : tsupport ω ⊆ closedBall (0 : E) R :=
    closure_minimal hsupp isClosed_closedBall
  refine ⟨R, hR, fun z hz => ?_⟩
  have hz' : z ∉ tsupport ω := by
    intro hmem
    have hmem' := htsub hmem
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hmem'
    linarith
  exact ⟨hvan z hz, fderiv_eq_zero_of_notMem_tsupport hz',
    fderiv_eq_zero_of_notMem_tsupport (fun hmem => hz' (tsupport_fderiv_subset ω hmem))⟩

lemma exists_norm_bound_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F] {f : E → F}
    (hcpt : HasCompactSupport f) (hcont : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖f z‖ ≤ M := by
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hcont
  exact ⟨max C 0, le_max_right _ _, fun z => le_trans (hC z) (le_max_left _ _)⟩

lemma integrable_indicator_Icc_const (C K : ℝ) :
    Integrable (fun u : ℝ => C * (Set.Icc (-K) K).indicator (fun _ => (1 : ℝ)) u) volume := by
  have hvol : volume (Set.Icc (-K) K) < ⊤ := isCompact_Icc.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-K) K)) := ⟨by simpa using hvol⟩
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) (Set.Icc (-K) K) volume :=
    Integrable.of_bound aestronglyMeasurable_const 1 (by simp)
  exact ((integrable_indicator_iff measurableSet_Icc).mpr h1).const_mul C

/-! ## The dominating function -/

/-- An integrable dominating function: `M * (1+K)^2` on `[-K,K]`, `0` elsewhere. -/
noncomputable def paramBound (M K : ℝ) : ℝ → ℝ :=
  fun u => M * ((1 + K) * (1 + K)) * (Set.Icc (-K) K).indicator (fun _ => (1 : ℝ)) u

lemma integrable_paramBound (M K : ℝ) : Integrable (paramBound M K) volume :=
  integrable_indicator_Icc_const (M * ((1 + K) * (1 + K))) K

lemma paramBound_nonneg {M K u : ℝ} (hM : 0 ≤ M) : 0 ≤ paramBound M K u := by
  rw [paramBound]
  have h1 : 0 ≤ (Set.Icc (-K) K).indicator (fun _ => (1 : ℝ)) u := by
    by_cases h : u ∈ Set.Icc (-K) K
    · rw [Set.indicator_of_mem h]; norm_num
    · rw [Set.indicator_of_notMem h]
  exact mul_nonneg (mul_nonneg hM (mul_self_nonneg (1 + K))) h1

lemma paramBound_of_mem {M K u : ℝ} (hu : u ∈ Set.Icc (-K) K) :
    paramBound M K u = M * ((1 + K) * (1 + K)) := by
  rw [paramBound, Set.indicator_of_mem hu, mul_one]

/-! ## A geometric bound -/

/-- If `q` is close to `p` and `|u|` is large enough, then `q.1 + u • q.2` is far from the
origin. -/
lemma smulLine_norm_gt {R K ρ : ℝ} {p q : E × E} {u : ℝ} (hρ : ρ = ‖p.2‖) (hρpos : 0 < ρ)
    (hq : q ∈ ball p (ρ / 2)) (hK : R + ‖p.1‖ + ρ ≤ K * (ρ / 2)) (hu : K < |u|) :
    R < ‖q.1 + u • q.2‖ := by
  have hdist : ‖q - p‖ < ρ / 2 := by
    rw [mem_ball, dist_eq_norm] at hq; exact hq
  have hq2 : ρ / 2 ≤ ‖q.2‖ := by
    have h1 : ‖q.2 - p.2‖ ≤ ‖q - p‖ := norm_snd_le (q - p)
    have h2 := abs_norm_sub_norm_le q.2 p.2
    rw [abs_le] at h2
    have h3 : ‖p.2‖ = ρ := hρ.symm
    linarith [h2.1]
  have hq1 : ‖q.1‖ ≤ ‖p.1‖ + ρ / 2 := by
    have h1 : ‖q.1 - p.1‖ ≤ ‖q - p‖ := norm_fst_le (q - p)
    have h2 := abs_norm_sub_norm_le q.1 p.1
    rw [abs_le] at h2
    linarith [h2.2]
  have h3 : |u| * (ρ / 2) ≤ ‖u • q.2‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hq2 (abs_nonneg u)
  have h4 : K * (ρ / 2) < |u| * (ρ / 2) :=
    mul_lt_mul_of_pos_right hu (by positivity)
  have h5 : ‖u • q.2‖ - ‖q.1‖ ≤ ‖q.1 + u • q.2‖ := by
    have h := abs_norm_sub_norm_le (u • q.2) (-q.1)
    rw [norm_neg, sub_neg_eq_add] at h
    calc ‖u • q.2‖ - ‖q.1‖ ≤ |‖u • q.2‖ - ‖q.1‖| := le_abs_self _
      _ ≤ ‖u • q.2 + q.1‖ := h
      _ = ‖q.1 + u • q.2‖ := by rw [add_comm]
  linarith

/-! ## The second derivative as a bilinear form -/

lemma bilinearComp_smul_right (Φ' : E →L[ℝ] (E →L[ℝ] ℝ)) (L M : E × E →L[ℝ] E) (c : ℝ) :
    Φ'.bilinearComp L (c • M) = c • Φ'.bilinearComp L M := by
  simp only [ContinuousLinearMap.bilinearComp]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.flip_smul]

lemma norm_bilinearComp_le (Φ' : E →L[ℝ] (E →L[ℝ] ℝ)) (L M : E × E →L[ℝ] E) :
    ‖Φ'.bilinearComp L M‖ ≤ ‖Φ'‖ * ‖L‖ * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  rw [ContinuousLinearMap.bilinearComp_apply]
  have h1 : ‖(Φ' (L x)) (M y)‖ ≤ ‖Φ' (L x)‖ * ‖M y‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖Φ' (L x)‖ ≤ ‖Φ'‖ * ‖L x‖ := ContinuousLinearMap.le_opNorm Φ' (L x)
  have h3 : ‖L x‖ ≤ ‖L‖ * ‖x‖ := ContinuousLinearMap.le_opNorm L x
  have h4 : ‖M y‖ ≤ ‖M‖ * ‖y‖ := ContinuousLinearMap.le_opNorm M y
  calc ‖(Φ' (L x)) (M y)‖ ≤ (‖Φ'‖ * ‖L x‖) * (‖M‖ * ‖y‖) :=
        h1.trans (mul_le_mul h2 h4 (norm_nonneg _) (by positivity))
    _ ≤ (‖Φ'‖ * (‖L‖ * ‖x‖)) * (‖M‖ * ‖y‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 (norm_nonneg Φ')) (le_refl _) (by positivity)
          (by positivity)
    _ = (‖Φ'‖ * ‖L‖ * ‖M‖) * ‖x‖ * ‖y‖ := by ring

lemma norm_bilinearComp_scaled_le (Φ' : E →L[ℝ] (E →L[ℝ] ℝ)) (u : ℝ) :
    ‖Φ'.bilinearComp (paramLine u : E × E →L[ℝ] E)
        (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖
      ≤ ‖Φ'‖ * (1 + |u|) * (1 + |u|) := by
  have hL : ‖(paramLine u : E × E →L[ℝ] E)‖ ≤ 1 + |u| := paramLine_norm_le u
  have hL2 : ‖paramWeight u • (paramLine u : E × E →L[ℝ] E)‖ ≤ 1 * (1 + |u|) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (paramWeight_nonneg u)]
    exact mul_le_mul (paramWeight_le_one u) hL (norm_nonneg (paramLine u : E × E →L[ℝ] E))
      zero_le_one
  have h1 : ‖Φ'‖ * ‖(paramLine u : E × E →L[ℝ] E)‖ *
        ‖paramWeight u • (paramLine u : E × E →L[ℝ] E)‖
      ≤ ‖Φ'‖ * (1 + |u|) * (1 * (1 + |u|)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hL (norm_nonneg Φ')) hL2
      (norm_nonneg (paramWeight u • (paramLine u : E × E →L[ℝ] E))) (by positivity)
  calc ‖Φ'.bilinearComp (paramLine u : E × E →L[ℝ] E)
          (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖
      ≤ ‖Φ'‖ * ‖(paramLine u : E × E →L[ℝ] E)‖ *
          ‖paramWeight u • (paramLine u : E × E →L[ℝ] E)‖ :=
        norm_bilinearComp_le Φ' _ _
    _ ≤ ‖Φ'‖ * (1 + |u|) * (1 * (1 + |u|)) := h1
    _ = ‖Φ'‖ * (1 + |u|) * (1 + |u|) := by ring

lemma paramPrecomp_comp_eq_bilinearComp (Φ' : E →L[ℝ] (E →L[ℝ] ℝ)) (u : ℝ) :
    (paramPrecomp u).comp (Φ'.comp (paramLine u))
      = Φ'.bilinearComp (paramLine u) (paramLine u) := by
  refine ContinuousLinearMap.ext fun r => ?_
  refine ContinuousLinearMap.ext fun y => ?_
  simp [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    paramPrecomp_apply]

/-! ## Bounds for the two derivative integrands -/

lemma norm_fderiv_comp_le_paramBound {ω : E → ℝ} {M K R ρ : ℝ} {p q : E × E} {u : ℝ}
    (hM0 : 0 ≤ M) (hK1 : 1 ≤ K) (hMb : ∀ z, ‖fderiv ℝ ω z‖ ≤ M)
    (hvanish : ∀ z, R < ‖z‖ → fderiv ℝ ω z = 0)
    (hρ : ρ = ‖p.2‖) (hρpos : 0 < ρ) (hK : R + ‖p.1‖ + ρ ≤ K * (ρ / 2))
    (hq : q ∈ ball p (ρ / 2)) :
    ‖paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u))‖ ≤ paramBound M K u := by
  by_cases hu : |u| ≤ K
  · have h1 : ‖paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u))‖
        = paramWeight u * ‖(fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (paramWeight_nonneg u)]
    rw [h1, paramBound_of_mem (Set.mem_Icc.mpr (abs_le.mp hu))]
    have h2 : ‖(fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)‖ ≤ M * (1 + |u|) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hMb (q.1 + u • q.2)) (paramLine_norm_le u) (norm_nonneg _) hM0)
    have h5 : 1 + |u| ≤ (1 + K) * (1 + K) := by nlinarith [hK1, abs_nonneg u]
    have h6 : paramWeight u * (M * (1 + |u|)) ≤ M * ((1 + K) * (1 + K)) := by
      have hw : paramWeight u ≤ 1 := paramWeight_le_one u
      have hM1 : M * (1 + |u|) ≤ M * ((1 + K) * (1 + K)) := mul_le_mul_of_nonneg_left h5 hM0
      have hM1n : 0 ≤ M * (1 + |u|) := mul_nonneg hM0 (by positivity)
      calc paramWeight u * (M * (1 + |u|)) ≤ 1 * (M * (1 + |u|)) :=
            mul_le_mul_of_nonneg_right hw hM1n
        _ = M * (1 + |u|) := one_mul _
        _ ≤ M * ((1 + K) * (1 + K)) := hM1
    calc paramWeight u * ‖(fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)‖
        ≤ paramWeight u * (M * (1 + |u|)) := mul_le_mul_of_nonneg_left h2 (paramWeight_nonneg u)
      _ ≤ M * ((1 + K) * (1 + K)) := h6
  · push_neg at hu
    have hz : fderiv ℝ ω (q.1 + u • q.2) = 0 := hvanish _ (smulLine_norm_gt hρ hρpos hq hK hu)
    rw [hz, ContinuousLinearMap.zero_comp, smul_zero, norm_zero]
    exact paramBound_nonneg hM0

lemma norm_fderiv_fderiv_le_paramBound {ω : E → ℝ} {M K R ρ : ℝ} {p q : E × E} {u : ℝ}
    (hM0 : 0 ≤ M) (hK1 : 1 ≤ K) (hMb : ∀ z, ‖fderiv ℝ (fderiv ℝ ω) z‖ ≤ M)
    (hvanish : ∀ z, R < ‖z‖ → fderiv ℝ (fderiv ℝ ω) z = 0)
    (hρ : ρ = ‖p.2‖) (hρpos : 0 < ρ) (hK : R + ‖p.1‖ + ρ ≤ K * (ρ / 2))
    (hq : q ∈ ball p (ρ / 2)) :
    ‖(fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp (paramLine u : E × E →L[ℝ] E)
        (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖ ≤ paramBound M K u := by
  by_cases hu : |u| ≤ K
  · rw [paramBound_of_mem (Set.mem_Icc.mpr (abs_le.mp hu))]
    have h5 : (1 + |u|) * (1 + |u|) ≤ (1 + K) * (1 + K) := by nlinarith [hK1, abs_nonneg u]
    calc ‖(fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp (paramLine u : E × E →L[ℝ] E)
          (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖
        ≤ ‖fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)‖ * (1 + |u|) * (1 + |u|) :=
          norm_bilinearComp_scaled_le (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)) u
      _ = ‖fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)‖ * ((1 + |u|) * (1 + |u|)) := by ring
      _ ≤ M * ((1 + K) * (1 + K)) :=
          mul_le_mul (hMb (q.1 + u • q.2)) h5 (by positivity) hM0
  · push_neg at hu
    have hz : fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2) = 0 :=
      hvanish _ (smulLine_norm_gt hρ hρpos hq hK hu)
    have hzero : (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp
        (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E)) = 0 := by
      rw [hz, ContinuousLinearMap.bilinearComp_zero]
    rw [hzero, ContinuousLinearMap.opNorm_zero]
    exact paramBound_nonneg hM0

/-! ## Chain rules -/

lemma hasFDerivAt_integrand {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (u : ℝ) (q : E × E) :
    HasFDerivAt (fun q' : E × E => ω (q'.1 + u • q'.2) * paramWeight u)
      (paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u))) q := by
  have h1 : HasFDerivAt (fun z : E => ω z) (fderiv ℝ ω (q.1 + u • q.2)) (q.1 + u • q.2) :=
    (hω.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun z : E => ω z * paramWeight u)
      (paramWeight u • fderiv ℝ ω (q.1 + u • q.2)) (q.1 + u • q.2) := h1.mul_const _
  have h3 := h2.comp q (hasFDerivAt_paramLine u q)
  rwa [ContinuousLinearMap.smul_comp] at h3

lemma hasFDerivAt_integrand_deriv {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (u : ℝ) (q : E × E) :
    HasFDerivAt (fun q' : E × E => paramWeight u •
        ((fderiv ℝ ω (q'.1 + u • q'.2)).comp (paramLine u)))
      ((fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp (paramLine u)
        (paramWeight u • paramLine u)) q := by
  have hΦ : HasFDerivAt (fun z : E => fderiv ℝ ω z)
      (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)) (q.1 + u • q.2) :=
    ((hω.fderiv_right (m := 1) (by norm_num)).differentiable_one).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (fun q' : E × E => fderiv ℝ ω (q'.1 + u • q'.2))
      ((fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).comp (paramLine u)) q :=
    hΦ.comp q (hasFDerivAt_paramLine u q)
  have h2 := ((paramPrecomp u : (E →L[ℝ] ℝ) →L[ℝ] (E × E →L[ℝ] ℝ)).hasFDerivAt).comp q h1
  have h3 := h2.const_smul (paramWeight u)
  have hfun : (fun q' : E × E => paramWeight u • ((fderiv ℝ ω (q'.1 + u • q'.2)).comp (paramLine u)))
      = fun q' : E × E => paramWeight u • (paramPrecomp u) (fderiv ℝ ω (q'.1 + u • q'.2)) := by
    funext q'; simp [paramPrecomp_apply]
  have h3' : HasFDerivAt (fun q' : E × E => paramWeight u •
        ((fderiv ℝ ω (q'.1 + u • q'.2)).comp (paramLine u)))
      (paramWeight u • ((paramPrecomp u).comp
        ((fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).comp (paramLine u)))) q :=
    h3.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)
  have hder : paramWeight u • ((paramPrecomp u).comp
        ((fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).comp (paramLine u)))
      = (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp (paramLine u)
        (paramWeight u • paramLine u) := by
    rw [paramPrecomp_comp_eq_bilinearComp, bilinearComp_smul_right]
  rwa [hder] at h3'

/-! ## Continuity of the integrands in `u` -/

lemma continuous_integrand {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (q : E × E) :
    Continuous (fun u : ℝ => ω (q.1 + u • q.2) * paramWeight u) := by
  have h1 : Continuous (fun u : ℝ => ω (q.1 + u • q.2)) := hω.continuous.comp (by fun_prop)
  exact h1.mul paramWeight_continuous

lemma continuous_integrand_deriv {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (q : E × E) :
    Continuous (fun u : ℝ => paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u))) := by
  have hA : Continuous (fun u : ℝ => fderiv ℝ ω (q.1 + u • q.2)) :=
    (hω.continuous_fderiv (by norm_num)).comp (by fun_prop)
  have h1 := hA.clm_comp continuous_paramLine
  exact paramWeight_continuous.smul h1

lemma continuous_bilinearComp {X : Type*} [TopologicalSpace X]
    {f : X → E →L[ℝ] (E →L[ℝ] ℝ)} {g h : X → E × E →L[ℝ] E}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => (f x).bilinearComp (g x) (h x)) := by
  have h1 : Continuous (fun x : X => (f x).comp (g x)) := hf.clm_comp hg
  have h2 : Continuous (fun x : X => ((f x).comp (g x)).flip) := by
    have := (ContinuousLinearMap.flipₗᵢ ℝ (E × E) E ℝ).continuous.comp h1
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using this
  have h3 : Continuous (fun x : X => (((f x).comp (g x)).flip).comp (h x)) := h2.clm_comp hh
  have h4 : Continuous (fun x : X => ((((f x).comp (g x)).flip).comp (h x)).flip) := by
    have := (ContinuousLinearMap.flipₗᵢ ℝ (E × E) (E × E) ℝ).continuous.comp h3
    simpa [ContinuousLinearMap.coe_flipₗᵢ, Function.comp_def] using this
  simpa [ContinuousLinearMap.bilinearComp] using h4

lemma continuous_integrand_deriv_deriv {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (q : E × E) :
    Continuous (fun u : ℝ => (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp
        (paramLine u) (paramWeight u • paramLine u)) := by
  have hf : Continuous (fun u : ℝ => fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)) :=
    ((hω.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp
      (by fun_prop)
  exact continuous_bilinearComp hf continuous_paramLine continuous_paramWeight_smul_paramLine


/-! ## Differentiation under the integral sign -/

/-- First derivative of the parameter integral `q ↦ ∫ u, ω (q.1 + u • q.2) * w u`. -/
theorem hasFDerivAt_paramIntegral {ω : E → ℝ} (hω : ContDiff ℝ 2 ω)
    (hcpt : HasCompactSupport ω) (p : E × E) (hp : p.2 ≠ 0) :
    HasFDerivAt (fun q : E × E => ∫ u : ℝ, ω (q.1 + u • q.2) * paramWeight u)
      (∫ u : ℝ, paramWeight u • ((fderiv ℝ ω (p.1 + u • p.2)).comp (paramLine u))) p := by
  obtain ⟨M, hM0, hMb⟩ := exists_norm_bound_of_hasCompactSupport (hcpt.fderiv ℝ)
    (hω.continuous_fderiv (by norm_num))
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_norm_bound_of_hasCompactSupport hcpt hω.continuous
  obtain ⟨R, hR0, hRvan⟩ := support_radius_of_contDiff hcpt
  set ρ : ℝ := ‖p.2‖ with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact norm_pos_iff.mpr hp
  set K : ℝ := max 1 (2 * (R + ‖p.1‖ + ρ) / ρ) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKbig : R + ‖p.1‖ + ρ ≤ K * (ρ / 2) := by
    have h2 : 2 * (R + ‖p.1‖ + ρ) / ρ ≤ K := by rw [hKdef]; exact le_max_right _ _
    rw [div_le_iff₀ hρpos] at h2
    linarith
  have hint : Integrable (fun u : ℝ => ω (p.1 + u • p.2) * paramWeight u) volume := by
    refine Integrable.mono' (integrable_paramWeight.const_mul M₀) ?_ ?_
    · exact (continuous_integrand hω p).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      have hw : 0 ≤ paramWeight u := paramWeight_nonneg u
      calc ‖ω (p.1 + u • p.2) * paramWeight u‖
          = |ω (p.1 + u • p.2)| * paramWeight u := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw]
        _ ≤ M₀ * paramWeight u := by
            have h := hM₀ (p.1 + u • p.2)
            rw [Real.norm_eq_abs] at h
            exact mul_le_mul_of_nonneg_right h hw
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := ℝ) (H := E × E)
    (μ := volume)
    (F := fun q : E × E => fun u : ℝ => ω (q.1 + u • q.2) * paramWeight u)
    (F' := fun q : E × E => fun u : ℝ =>
      paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)))
    (x₀ := p) (s := ball p (ρ / 2)) (bound := paramBound M K) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ball_mem_nhds p (by positivity)
  · exact Eventually.of_forall fun q => (continuous_integrand hω q).aestronglyMeasurable
  · exact hint
  · exact (continuous_integrand_deriv hω p).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    intro q hq
    exact norm_fderiv_comp_le_paramBound hM0 hK1 hMb (fun z hz => (hRvan z hz).2.1)
      hρ hρpos hKbig hq
  · exact integrable_paramBound M K
  · exact Eventually.of_forall fun u => fun q _ => hasFDerivAt_integrand hω u q

/-- The second derivative of the parameter integral, together with the integrability of the
second-derivative integrand. -/
theorem hasFDerivAt_paramIntegral_deriv {ω : E → ℝ} (hω : ContDiff ℝ 2 ω)
    (hcpt : HasCompactSupport ω) (p : E × E) (hp : p.2 ≠ 0) :
    Integrable (fun u : ℝ => (fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
        (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E))) volume ∧
    (∀ v : E × E, Integrable (fun u : ℝ =>
        (fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
          (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E)) v)
        volume) ∧
    HasFDerivAt (fun q : E × E => ∫ u : ℝ,
        paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)))
      (∫ u : ℝ, (fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
          (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E))) p := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_norm_bound_of_hasCompactSupport (hcpt.fderiv ℝ)
    (hω.continuous_fderiv (by norm_num))
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_norm_bound_of_hasCompactSupport
    (F := E →L[ℝ] (E →L[ℝ] ℝ))
    (f := fun z : E => fderiv ℝ (fderiv ℝ ω) z)
    (by simpa only using (hcpt.fderiv ℝ).fderiv ℝ)
    ((hω.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))
  obtain ⟨R, hR0, hRvan⟩ := support_radius_of_contDiff hcpt
  set ρ : ℝ := ‖p.2‖ with hρ
  have hρpos : 0 < ρ := by rw [hρ]; exact norm_pos_iff.mpr hp
  set K : ℝ := max 1 (2 * (R + ‖p.1‖ + ρ) / ρ) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKbig : R + ‖p.1‖ + ρ ≤ K * (ρ / 2) := by
    have h2 : 2 * (R + ‖p.1‖ + ρ) / ρ ≤ K := by rw [hKdef]; exact le_max_right _ _
    rw [div_le_iff₀ hρpos] at h2
    linarith
  have hMb1 : ∀ z, ‖fderiv ℝ ω z‖ ≤ max M₁ M₂ := fun z =>
    le_trans (hM₁ z) (le_max_left _ _)
  have hMb2 : ∀ z, ‖fderiv ℝ (fderiv ℝ ω) z‖ ≤ max M₁ M₂ := fun z =>
    le_trans (hM₂ z) (le_max_right _ _)
  have hM0 : 0 ≤ max M₁ M₂ := le_trans hM₁0 (le_max_left _ _)
  have hpball : p ∈ ball p (ρ / 2) := mem_ball_self (by positivity)
  have hint : Integrable (fun u : ℝ =>
      paramWeight u • ((fderiv ℝ ω (p.1 + u • p.2)).comp (paramLine u))) volume := by
    refine Integrable.mono' (β := (E × E) →L[ℝ] ℝ)
      (g := paramBound (max M₁ M₂) K) (integrable_paramBound (max M₁ M₂) K) ?_ ?_
    · exact (continuous_integrand_deriv hω p).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      exact norm_fderiv_comp_le_paramBound hM0 hK1 hMb1 (fun z hz => (hRvan z hz).2.1)
        hρ hρpos hKbig hpball
  have hint2 : Integrable (fun u : ℝ => (fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
      (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E))) volume := by
    refine Integrable.mono' (β := (E × E) →L[ℝ] ((E × E) →L[ℝ] ℝ))
      (g := paramBound (max M₁ M₂) K) (integrable_paramBound (max M₁ M₂) K) ?_ ?_
    · exact (continuous_integrand_deriv_deriv hω p).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      exact norm_fderiv_fderiv_le_paramBound hM0 hK1 hMb2 (fun z hz => (hRvan z hz).2.2)
        hρ hρpos hKbig hpball
  have hint3 : ∀ v : E × E, Integrable (fun u : ℝ =>
      (fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
        (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E)) v) volume := by
    intro v
    refine Integrable.mono' ((integrable_paramBound (max M₁ M₂) K).mul_const ‖v‖) ?_ ?_
    · exact ((continuous_integrand_deriv_deriv hω p).clm_apply continuous_const).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      have hX : ‖(fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
          (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖
          ≤ paramBound (max M₁ M₂) K u :=
        norm_fderiv_fderiv_le_paramBound hM0 hK1 hMb2 (fun z hz => (hRvan z hz).2.2)
          hρ hρpos hKbig hpball
      calc ‖(fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
            (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E)) v‖
          ≤ ‖(fderiv ℝ (fderiv ℝ ω) (p.1 + u • p.2)).bilinearComp
              (paramLine u : E × E →L[ℝ] E) (paramWeight u • (paramLine u : E × E →L[ℝ] E))‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ paramBound (max M₁ M₂) K u * ‖v‖ := mul_le_mul_of_nonneg_right hX (norm_nonneg v)
  refine ⟨hint2, hint3, ?_⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := (E × E →L[ℝ] ℝ))
    (H := E × E) (μ := volume)
    (F := fun q : E × E => fun u : ℝ =>
      paramWeight u • ((fderiv ℝ ω (q.1 + u • q.2)).comp (paramLine u)))
    (F' := fun q : E × E => fun u : ℝ =>
      (fderiv ℝ (fderiv ℝ ω) (q.1 + u • q.2)).bilinearComp (paramLine u)
        (paramWeight u • paramLine u))
    (x₀ := p) (s := ball p (ρ / 2)) (bound := paramBound (max M₁ M₂) K) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ball_mem_nhds p (by positivity)
  · exact Eventually.of_forall fun q => (continuous_integrand_deriv hω q).aestronglyMeasurable
  · exact hint
  · exact (continuous_integrand_deriv_deriv hω p).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    intro q hq
    exact norm_fderiv_fderiv_le_paramBound hM0 hK1 hMb2 (fun z hz => (hRvan z hz).2.2)
      hρ hρpos hKbig hq
  · exact integrable_paramBound (max M₁ M₂) K
  · exact Eventually.of_forall fun u => fun q _ => hasFDerivAt_integrand_deriv hω u q

end IFD2

/-! ## The main statement -/

/-- The second Fréchet derivative of the parameter integral `p ↦ ∫ u, ω (p.1 + u • p.2) * (1+u²)⁻¹`
at `(a, b)`, in a general real normed space. -/
theorem iteratedFDeriv_two_integral_add_smul_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ω : E → ℝ} (hω : ContDiff ℝ 2 ω) (hcpt : HasCompactSupport ω)
    (a b V W : E) (hb : b ≠ 0) :
    (iteratedFDeriv ℝ 2 (fun p : E × E =>
        ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u) (a, b))
        (fun _ : Fin 2 => (V, W)) =
      ∫ u : ℝ, (iteratedFDeriv ℝ 2 ω (a + u • b)) (fun _ : Fin 2 => (V + u • W)) *
        IFD2.paramWeight u := by
  have hnb : {p : E × E | p.2 ≠ 0} ∈ 𝓝 ((a, b) : E × E) :=
    (isOpen_ne.preimage continuous_snd).mem_nhds (by simpa using hb)
  have hG : fderiv ℝ (fun p : E × E => ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u)
      =ᶠ[𝓝 ((a, b) : E × E)] fun p : E × E =>
        ∫ u : ℝ, IFD2.paramWeight u • ((fderiv ℝ ω (p.1 + u • p.2)).comp (IFD2.paramLine u)) := by
    filter_upwards [hnb] with p hp
    exact (IFD2.hasFDerivAt_paramIntegral hω hcpt p hp).fderiv
  obtain ⟨hint2, hint3, hL2⟩ := IFD2.hasFDerivAt_paramIntegral_deriv hω hcpt (a, b) (by simpa using hb)
  have hderiv : fderiv ℝ (fderiv ℝ (fun p : E × E =>
        ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u)) (a, b)
      = (∫ u : ℝ, (fderiv ℝ (fderiv ℝ ω) (a + u • b)).bilinearComp
          (IFD2.paramLine u : E × E →L[ℝ] E)
          (IFD2.paramWeight u • (IFD2.paramLine u : E × E →L[ℝ] E))) := by
    rw [hG.fderiv_eq, hL2.fderiv]
  have hBintV : Integrable (fun u : ℝ =>
      ((fderiv ℝ (fderiv ℝ ω) (a + u • b)).bilinearComp
        (IFD2.paramLine u : E × E →L[ℝ] E)
        (IFD2.paramWeight u • (IFD2.paramLine u : E × E →L[ℝ] E))) (V, W)) volume :=
    hint3 (V, W)
  have hfinal : (fderiv ℝ (fderiv ℝ (fun p : E × E =>
        ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u)) (a, b)) (V, W) (V, W) =
      ∫ u : ℝ, (fderiv ℝ (fderiv ℝ ω) (a + u • b) (V + u • W) (V + u • W)) *
        IFD2.paramWeight u := by
    rw [hderiv, ContinuousLinearMap.integral_apply hint2,
      ContinuousLinearMap.integral_apply hBintV]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.bilinearComp_apply, IFD2.paramLine_apply,
      ContinuousLinearMap.smul_apply, map_smul]
    ring
  calc (iteratedFDeriv ℝ 2 (fun p : E × E =>
          ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u) (a, b)) (fun _ : Fin 2 => (V, W))
      = (fderiv ℝ (fderiv ℝ (fun p : E × E =>
          ∫ u : ℝ, ω (p.1 + u • p.2) * IFD2.paramWeight u)) (a, b)) (V, W) (V, W) :=
        iteratedFDeriv_two_apply _ _ _
    _ = ∫ u : ℝ, (iteratedFDeriv ℝ 2 ω (a + u • b)) (fun _ : Fin 2 => (V + u • W)) *
          IFD2.paramWeight u := by
        rw [hfinal]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp [iteratedFDeriv_two_apply]


/-- The second Fréchet derivative of the parameter integral
`p ↦ ∫ u, ω (p.1 + u • p.2) * (1 + u^2)⁻¹` at `(a, b)`, evaluated on the diagonal vector `(V, W)`. -/
theorem iteratedFDeriv_two_integral_add_smul {d : ℕ} {ω : EuclideanSpace ℝ (Fin d) → ℝ}
    (hω : ContDiff ℝ 2 ω) (hcpt : HasCompactSupport ω)
    (a b V W : EuclideanSpace ℝ (Fin d)) (hb : b ≠ 0) :
    (iteratedFDeriv ℝ 2 (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ∫ u : ℝ, ω (p.1 + u • p.2) * (1 + u ^ 2)⁻¹) (a, b))
        (fun _ : Fin 2 => (V, W)) =
      ∫ u : ℝ, (iteratedFDeriv ℝ 2 ω (a + u • b)) (fun _ : Fin 2 => (V + u • W)) *
        (1 + u ^ 2)⁻¹ := by
  simpa [IFD2.paramWeight] using
    (iteratedFDeriv_two_integral_add_smul_general (E := EuclideanSpace ℝ (Fin d))
      hω hcpt a b V W hb)

end Commons.Analysis.Calculus