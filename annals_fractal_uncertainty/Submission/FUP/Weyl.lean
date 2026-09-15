import Submission.FUP.Dbar2Calc
import Submission.FUP.DbarCutoff
import Submission.Commons.Analysis.Complex.weyl_dbar
import Submission.FUP.DbarCutoff2
import Submission.Commons.Analysis.Complex.analyticOnNhd_of_dbar_eq_zero
import Submission.Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero
import Submission.Commons.MeasureTheory.Integral.exists_approximate_identity_complex
import Submission.Commons.Analysis.Convolution.contDiff_integral_mul_sub
import Submission.Commons.Analysis.Convolution.fderiv_integral_mul_sub
import Submission.Commons.Analysis.Complex.norm_fderiv_single_le_of_slice_bound
import Submission.Commons.Analysis.Complex.meanValue_polydisc

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.FUP

variable {d : ℕ}

/-- `1 ≤ ∞` for the `ContDiff` order. -/
private lemma hle_one : (1 : ℕ∞ω) ≤ ((⊤ : ENat) : WithTop ENat) := WithTop.coe_le_coe.mpr le_top

/-- `2 ≤ ∞` for the `ContDiff` order. -/
private lemma hle_two : (2 : ℕ∞ω) ≤ ((⊤ : ENat) : WithTop ENat) := WithTop.coe_le_coe.mpr le_top

/-- the product rule identity: `ϑ_φ u · e^{-φ} = -∑_k ∂_k(u_k e^{-φ})`. -/
lemma dbarAdjoint_mul_exp {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {u : FormDu d → (Fin d → ℂ)} (hu : ∀ k, ContDiff ℝ 1 (fun z => u z k)) :
    (fun z => dbarAdjoint φ u z * Complex.exp (-(phiC φ z)))
      = fun z => -(∑ k, partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z) := by
  funext z
  have hterm : ∀ k : Fin d, (partialZ k (fun w => u w k) z
      - u z k * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z) * Complex.exp (-(phiC φ z))
      = partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z := by
    intro k
    have h1 := congrFun (partialZ_exp_mul (φ := φ) hφ hu k) z
    have hfun : (fun w => u w k * Complex.exp (-(phiC φ w)))
        = (fun w => Complex.exp (-(phiC φ w)) * u w k) := by funext w; ring
    have h1' : Complex.exp (-(phiC φ z)) * (partialZ k (fun w => u w k) z
        - u z k * partialZ k (fun w => ((φ w : ℝ) : ℂ)) z)
        = partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z := by
      rw [hfun]
      exact h1.symm
    rw [mul_comm, h1']
  rw [dbarAdjoint, neg_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => hterm k)

/-- `star (Complex.exp (-(phiC φ z))) = Complex.exp (-(phiC φ z))`. -/
lemma star_cexp_neg_phiC {d : ℕ} {φ : FormDu d → ℝ} (z : FormDu d) :
    star (Complex.exp (-(phiC φ z))) = Complex.exp (-(phiC φ z)) :=
  star_cexp_neg (φ := φ) z

/-- The conjugate of the product-rule identity. -/
lemma star_dbarAdjoint_mul_exp {d : ℕ} {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {u : FormDu d → (Fin d → ℂ)} (hu : ∀ k, ContDiff ℝ 1 (fun z => u z k)) :
    (fun z => star (dbarAdjoint φ u z) * Complex.exp (-(phiC φ z)))
      = fun z => -(∑ k, partialZbar k (fun w => star (u w k * Complex.exp (-(phiC φ w)))) z) := by
  have h := dbarAdjoint_mul_exp (φ := φ) hφ hu
  funext z
  have hz := congrFun h z
  have h2 : star (dbarAdjoint φ u z) * Complex.exp (-(phiC φ z))
      = -(∑ k, star (partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z)) := by
    calc star (dbarAdjoint φ u z) * Complex.exp (-(phiC φ z))
        = star (Complex.exp (-(phiC φ z))) * star (dbarAdjoint φ u z) := by
          rw [star_cexp_neg_phiC]; ring
      _ = star (dbarAdjoint φ u z * Complex.exp (-(phiC φ z))) := (star_mul _ _).symm
      _ = star (-(∑ k, partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z)) := by rw [hz]
      _ = -(∑ k, star (partialZ k (fun w => u w k * Complex.exp (-(phiC φ w))) z)) := by
          rw [star_neg, star_sum]
  rw [h2]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [partialZbar_star]

/-- **The distributional form of the weak `∂̄`-relation.**  If `F ∈ L²(μ_φ)` is weakly `∂̄`-closed
for the weight `e^{-φ}`, then `∫ F ∂̄_j ξ = 0` for every smooth compactly supported test function
`ξ` and every `j`. -/
theorem dbarWeak_zero_distributional {d : ℕ} {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {F : FormDu d → ℂ} (hFm : MemLp F 2 (wtMeasure φ))
    (hweak : DbarWeak φ (hFm.toLp F) 0) :
    ∀ (j : Fin d) (ξ : FormDu d → ℂ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      ∫ x, F x * partialZbar j ξ x = 0 := by
  have hφc : Continuous φ := hφ.continuous
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le hle_two
  have hφ1 : ContDiff ℝ 1 (fun z : FormDu d => ((φ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.of_le hle_one)
  intro j ξ hξ hξs
  let u : FormDu d → (Fin d → ℂ) :=
    fun z k => (if k = j then star (ξ z) else 0) * Complex.exp (phiC φ z)
  have hexp : ContDiff ℝ ∞ (fun z : FormDu d => Complex.exp (phiC φ z)) :=
    (Complex.ofRealCLM.contDiff.comp hφ).cexp
  have hucd : ∀ k, ContDiff ℝ ∞ (fun z => u z k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      have h' : ContDiff ℝ ∞ (fun z : FormDu d => star (ξ z) * Complex.exp (phiC φ z)) :=
        ((Complex.conjCLE.contDiff (n := ∞)).comp hξ).mul hexp
      simpa [u] using h'
    · have h' : ContDiff ℝ ∞ (fun _ : FormDu d => (0 : ℂ)) := contDiff_const
      simpa [u, hk] using h'
  have hus : ∀ k, HasCompactSupport (fun z => u z k) := by
    intro k
    by_cases hk : k = j
    · subst hk
      have h' : HasCompactSupport (fun z : FormDu d => star (ξ z) * Complex.exp (phiC φ z)) :=
        (hξs.comp_left (g := fun w : ℂ => star w) (by simp)).mul_right
          (f' := fun z : FormDu d => Complex.exp (phiC φ z))
      simpa [u] using h'
    · have h' : HasCompactSupport (fun _ : FormDu d => (0 : ℂ)) := HasCompactSupport.zero
      simpa [u, hk] using h'
  have hψsm : ContDiff ℝ ∞ (liftForm u) := contDiff_liftForm hucd
  have hψcs : HasCompactSupport (liftForm u) :=
    hasCompactSupport_liftForm (hasCompactSupport_pi (F := u) hus)
  have hψm : MemLp (liftForm u) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφc hψsm hψcs
  have hθc : Continuous (dbarAdjoint φ (toFormFun (liftForm u))) :=
    continuous_dbarAdjoint (fun k => (hucd k).of_le hle_one) hφ1
  have hθs : HasCompactSupport (dbarAdjoint φ (toFormFun (liftForm u))) :=
    hasCompactSupport_dbarAdjoint (hasCompactSupport_pi (F := u) hus)
  have hθm : MemLp (dbarAdjoint φ (toFormFun (liftForm u))) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_continuous_hasCompactSupport hφc hθc hθs
  have hrel := hweak (liftForm u) hψsm hψcs hψm hθm
  rw [inner_zero_right] at hrel
  have h0 : inner ℂ (hθm.toLp (dbarAdjoint φ (toFormFun (liftForm u)))) (hFm.toLp F) = 0 :=
    hrel.symm
  rw [inner_toLp_eq_integral hθm hFm, integral_wtMeasure hφc] at h0
  have hpt : ∀ z : FormDu d, Real.exp (-(φ z)) •
      inner ℂ ((dbarAdjoint φ (toFormFun (liftForm u))) z) (F z)
      = -(F z * partialZbar j ξ z) := by
    intro z
    rw [RCLike.inner_apply, Complex.real_smul]
    have h2 : star ((dbarAdjoint φ (toFormFun (liftForm u))) z) * Complex.exp (-(phiC φ z))
        = -(∑ k, partialZbar k (fun w => star (u w k * Complex.exp (-(phiC φ w)))) z) := by
      have h := congrFun (star_dbarAdjoint_mul_exp (φ := φ) hφ2
        (fun k => (hucd k).of_le hle_one)) z
      simpa using h
    have hfun : (fun w => star (u w j * Complex.exp (-(phiC φ w)))) = ξ := by
      funext w
      simp only [u]
      rw [mul_assoc, ← Complex.exp_add]
      simp
    have h3 : (∑ k, partialZbar k (fun w => star (u w k * Complex.exp (-(phiC φ w)))) z)
        = partialZbar j ξ z := by
      rw [Finset.sum_eq_single j]
      · rw [hfun]
      · intro k _ hk
        have hk' : (fun w => star (u w k * Complex.exp (-(phiC φ w)))) = fun _ => (0 : ℂ) := by
          funext w
          simp [u, hk]
        rw [hk']
        simp [partialZbar]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hmain : star ((dbarAdjoint φ (toFormFun (liftForm u))) z) * Complex.exp (-(phiC φ z))
        * F z = -(F z * partialZbar j ξ z) := by
      rw [h2, h3]
      ring
    calc ↑(Real.exp (-(φ z))) * (F z * star ((dbarAdjoint φ (toFormFun (liftForm u))) z))
        = star ((dbarAdjoint φ (toFormFun (liftForm u))) z) * Complex.exp (-(phiC φ z)) * F z := by
          rw [Complex.ofReal_exp, Complex.ofReal_neg, phiC]
          ring
      _ = -(F z * partialZbar j ξ z) := hmain
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at h0
  rw [integral_neg] at h0
  exact neg_eq_zero.mp h0


/-- **Weyl's lemma for the weighted space `L²(μ_φ)`.**  A function in `L²(μ_φ)` whose weak
`∂̄`-derivative vanishes (in the sense of `DbarWeak`) agrees `μ_φ`-a.e. with a holomorphic
function.

The two local-integrability hypotheses are those of the volume-based Weyl lemma
(`Commons.Analysis.Complex.weyl_dbar`); they are automatically satisfied when `F` is the
representative of an `L²(μ_φ)`-class and `φ` is continuous (a lemma to that effect lives in the
commons). -/
theorem weyl_dbar_wt {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {F : FormDu d → ℂ} (hFm : MemLp F 2 (wtMeasure φ))
    (hF1 : LocallyIntegrable F (volume : Measure (FormDu d)))
    (hF2 : LocallyIntegrable (fun z => ‖F z‖ ^ 2) (volume : Measure (FormDu d)))
    (hweak : DbarWeak φ (hFm.toLp F) 0) :
    ∃ H : FormDu d → ℂ, Differentiable ℂ H ∧ F =ᵐ[wtMeasure φ] H := by
  have hdist := dbarWeak_zero_distributional hφ hFm hweak
  have hweak' : ∀ (j : Fin d) (ξ : FormDu d → ℂ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      ∫ x, F x * (((fderiv ℝ ξ x) (Pi.single j 1)
        + Complex.I * (fderiv ℝ ξ x) (Pi.single j Complex.I)) / 2) = 0 := by
    intro j ξ hξ hξs
    simpa only [partialZbar] using hdist j ξ hξ hξs
  obtain ⟨H, hHd, hHeq⟩ := Commons.Analysis.Complex.weyl_dbar hF1 hF2 hweak'
  exact ⟨H, hHd, hHeq.filter_mono (Measure.AbsolutelyContinuous.ae_le
    (wtMeasure_absolutelyContinuous φ))⟩

/-! ## Mollification of a weakly `∂̄`-closed function

The analytic core of Weyl's lemma for `∂̄`: the mollification `moll K F n` of a locally integrable
`F` is `C^∞`, and the weak relation `∫ F ∂̄_j ξ = 0` implies that it is holomorphic (its `∂̄`
vanishes pointwise).
-/


section Basic

/-- Reflection preserves compact support. -/
lemma hasCompactSupport_comp_sub {φ : FormDu d → ℂ} (h : HasCompactSupport φ) (z : FormDu d) :
    HasCompactSupport (fun t => φ (z - t)) := by
  have hsub : tsupport (fun t : FormDu d => φ (z - t))
      ⊆ (fun t : FormDu d => z - t) ⁻¹' tsupport φ := by
    refine closure_minimal ?_ ((isClosed_tsupport φ).preimage
      (continuous_const.sub continuous_id))
    intro t ht
    exact subset_tsupport φ ht
  refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hsub
  have heq : (fun t : FormDu d => z - t) ⁻¹' tsupport φ
      = (fun s : FormDu d => z - s) '' tsupport φ := by
    ext t
    constructor
    · intro ht; exact ⟨z - t, ht, by simp⟩
    · rintro ⟨s, hs, rfl⟩; simpa using hs
  rw [heq]
  exact h.image (continuous_const.sub continuous_id)

/-- A continuous function with compact support times a locally integrable function is integrable. -/
lemma integrable_mul_of_hasCompactSupport {g F : FormDu d → ℂ} (hg : Continuous g)
    (hgs : HasCompactSupport g) (hF : LocallyIntegrable F (volume : Measure (FormDu d))) :
    Integrable (fun t => g t * F t) (volume : Measure (FormDu d)) := by
  have hK : IsCompact (tsupport g) := hgs
  have h1 : IntegrableOn (fun t => g t * F t) (tsupport g) volume :=
    IntegrableOn.continuousOn_mul hg.continuousOn (hF.integrableOn_isCompact hK) hK
  have hsupp : ∀ t ∉ tsupport g, g t * F t = 0 := by
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  have h2 : (fun t => g t * F t) = (tsupport g).indicator (fun t => g t * F t) := by
    funext t
    by_cases ht : t ∈ tsupport g
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hsupp t ht]
  rw [h2, integrable_indicator_iff hK.isClosed.measurableSet]
  exact h1

/-- Mollification of `F` against the approximate identity `K`. -/
noncomputable def moll {d : ℕ} (K : ℕ → FormDu d → ℝ) (F : FormDu d → ℂ) (n : ℕ) :
    FormDu d → ℂ :=
  fun z => ∫ t, K n (z - t) • F t ∂(volume : Measure (FormDu d))

lemma contDiff_moll {K : ℕ → FormDu d → ℝ} {F : FormDu d → ℂ}
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hF : LocallyIntegrable F (volume : Measure (FormDu d))) (n : ℕ) :
    ContDiff ℝ ∞ (moll K F n) :=
  Commons.Analysis.Convolution.contDiff_integral_mul_sub (hK n) (hKs n) hF

/-- `∂̄` of the reflection: `∂̄_j (s ↦ g (z - s)) t = - ∂̄_j g (z - t)`. -/
lemma partialZbar_comp_sub (j : Fin d) (g : FormDu d → ℂ) (z t : FormDu d)
    (hg : DifferentiableAt ℝ g (z - t)) :
    partialZbar j (fun s => g (z - s)) t = - partialZbar j g (z - t) := by
  rw [partialZbar, partialZbar]
  have h1 : HasFDerivAt (fun s : FormDu d => z - s) (-(1 : FormDu d →L[ℝ] FormDu d)) t :=
    (hasFDerivAt_id (𝕜 := ℝ) t).const_sub z
  have hR : fderiv ℝ (fun s : FormDu d => g (z - s)) t
      = (fderiv ℝ g (z - t)).comp (-(1 : FormDu d →L[ℝ] FormDu d)) :=
    (hg.hasFDerivAt.comp t h1).fderiv
  rw [hR]
  have h4 : ((-(1 : FormDu d →L[ℝ] FormDu d)) (Pi.single j (1 : ℂ))) = -(Pi.single j (1 : ℂ)) := by
    simp
  have h5 : ((-(1 : FormDu d →L[ℝ] FormDu d)) (Pi.single j Complex.I)) = -(Pi.single j Complex.I) := by
    simp
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h4, h5, map_neg, map_neg]
  ring

end Basic

section Dbar

/-- The mollification of a weakly `∂̄`-closed `L²`-function is holomorphic. -/
lemma partialZbar_moll {K : ℕ → FormDu d → ℝ} {F : FormDu d → ℂ}
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hF : LocallyIntegrable F (volume : Measure (FormDu d)))
    (hweak : ∀ (j : Fin d) (ξ : FormDu d → ℂ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      ∫ x, F x * partialZbar j ξ x = 0)
    (n : ℕ) (j : Fin d) : partialZbar j (moll K F n) = 0 := by
  funext z
  -- the two kernels
  have hcont1 : Continuous (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((((hK n).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).comp (continuous_const.sub continuous_id)))
  have hcont2 : Continuous (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ)) :=
    (Complex.continuous_ofReal.comp ((((hK n).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).comp (continuous_const.sub continuous_id)))
  have hcs1 : HasCompactSupport (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ)) :=
    hasCompactSupport_comp_sub
      (((hKs n).fderiv_apply ℝ (Pi.single j (1 : ℂ))).comp_left
        (g := fun w : ℝ => ((w : ℝ) : ℂ)) (by simp)) z
  have hcs2 : HasCompactSupport (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ)) :=
    hasCompactSupport_comp_sub
      (((hKs n).fderiv_apply ℝ (Pi.single j Complex.I)).comp_left
        (g := fun w : ℝ => ((w : ℝ) : ℂ)) (by simp)) z
  have hInt1 : Integrable (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ) * F t) :=
    integrable_mul_of_hasCompactSupport hcont1 hcs1 hF
  have hInt2 : Integrable (fun t : FormDu d =>
      ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ) * F t) :=
    integrable_mul_of_hasCompactSupport hcont2 hcs2 hF
  -- the derivative formula
  have hder : ∀ v : FormDu d, (fderiv ℝ (moll K F n) z) v
      = ∫ t, ((fderiv ℝ (K n) (z - t)) v) • F t := fun v =>
    Commons.Analysis.Convolution.fderiv_integral_mul_sub (hK n) (hKs n) hF z v
  -- the weak equation with the reflected test function
  have hξsm : ContDiff ℝ ∞ (fun s : FormDu d => ((K n (z - s) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hK n)).comp (contDiff_const.sub contDiff_id)
  have hξcs : HasCompactSupport (fun s : FormDu d => ((K n (z - s) : ℝ) : ℂ)) :=
    hasCompactSupport_comp_sub ((hKs n).comp_left
      (g := fun w : ℝ => ((w : ℝ) : ℂ)) (by simp)) z
  have hW := hweak j (fun s : FormDu d => ((K n (z - s) : ℝ) : ℂ)) hξsm hξcs
  -- the pointwise identification of `∂̄` of the reflected test function
  have hpt : ∀ s : FormDu d, partialZbar j (fun s : FormDu d => ((K n (z - s) : ℝ) : ℂ)) s
      = - ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ)
          + Complex.I * ((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ)) / 2) := by
    intro s
    have hd : DifferentiableAt ℝ (fun w : FormDu d => ((K n w : ℝ) : ℂ)) (z - s) :=
      (Complex.ofRealCLM.differentiable.comp ((hK n).differentiable
        (by simp))).differentiableAt
    rw [partialZbar_comp_sub j (fun w : FormDu d => ((K n w : ℝ) : ℂ)) z s hd]
    congr 1
    rw [partialZbar]
    have hfd : fderiv ℝ (fun w : FormDu d => ((K n w : ℝ) : ℂ)) (z - s)
        = Complex.ofRealCLM.comp (fderiv ℝ (K n) (z - s)) := by
      have h1 : HasFDerivAt (fun w : FormDu d => ((K n w : ℝ) : ℂ))
          (Complex.ofRealCLM.comp (fderiv ℝ (K n) (z - s))) (z - s) :=
        (Complex.ofRealCLM.hasFDerivAt).comp (z - s)
          ((hK n).differentiable (by simp)).differentiableAt.hasFDerivAt
      exact h1.fderiv
    rw [hfd]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  have hptF : ∀ s : FormDu d, F s * partialZbar j (fun s : FormDu d => ((K n (z - s) : ℝ) : ℂ)) s
      = - (F s * ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ)
          + Complex.I * ((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ)) / 2)) := by
    intro s
    rw [hpt s]
    ring
  -- the weak equation in the desired form
  have hW2 : ∫ s, F s * ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ)
      + Complex.I * ((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ)) / 2) = 0 := by
    have h := hW
    rw [integral_congr_ae (Eventually.of_forall hptF)] at h
    rwa [integral_neg, neg_eq_zero] at h
  -- splitting the integral
  have hsplit : (∫ s, F s * ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ)
        + Complex.I * ((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ)) / 2))
      = ((∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ) * F t)
          + Complex.I * (∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ) * F t)) / 2 := by
    rw [show (fun s : FormDu d => F s * ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ)
          + Complex.I * ((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ)) / 2))
        = (fun s : FormDu d => ((((fderiv ℝ (K n) (z - s)) (Pi.single j (1 : ℂ)) : ℂ) * F s)
          + Complex.I * (((fderiv ℝ (K n) (z - s)) (Pi.single j Complex.I) : ℂ) * F s)) / 2)
        from by funext s; ring]
    rw [integral_div, integral_add hInt1 (hInt2.const_mul Complex.I), integral_const_mul]
  -- the real-scalar products
  have hA : (∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ))) • F t)
      = ∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ) * F t := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ))) • F t
      = ((fderiv ℝ (K n) (z - t)) (Pi.single j (1 : ℂ)) : ℂ) * F t
    rw [Complex.real_smul]
  have hB : (∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I)) • F t)
      = ∫ t, ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ) * F t := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I)) • F t
      = ((fderiv ℝ (K n) (z - t)) (Pi.single j Complex.I) : ℂ) * F t
    rw [Complex.real_smul]
  rw [partialZbar, hder (Pi.single j (1 : ℂ)), hder (Pi.single j Complex.I), hA, hB, ← hsplit]
  exact hW2

/-- The mollification of a weakly `∂̄`-closed function is complex differentiable (holomorphic). -/
lemma differentiable_moll {K : ℕ → FormDu d → ℝ} {F : FormDu d → ℂ}
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hKs : ∀ n, HasCompactSupport (K n))
    (hF : LocallyIntegrable F (volume : Measure (FormDu d)))
    (hweak : ∀ (j : Fin d) (ξ : FormDu d → ℂ), ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      ∫ x, F x * partialZbar j ξ x = 0)
    (n : ℕ) : Differentiable ℂ (moll K F n) := by
  refine Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero
    ((contDiff_moll hK hKs hF n).differentiable (by simp)) ?_
  intro j z
  have h : ((fderiv ℝ (moll K F n) z) (Pi.single j (1 : ℂ))
      + Complex.I * (fderiv ℝ (moll K F n) z) (Pi.single j Complex.I)) / 2 = 0 := by
    have h' := congrFun (partialZbar_moll hK hKs hF hweak n j) z
    rwa [partialZbar] at h'
  rcases div_eq_zero_iff.mp h with h' | h'
  · exact h'
  · exact absurd h' (by norm_num)

/-- **A complex differentiable function is `∂̄`-closed.**  This is the converse of the commons
`Commons.Analysis.Complex.differentiable_complex_of_dbar_eq_zero`, used to write the solution of
Hörmander's equation as `g = H + h` with `H` holomorphic. -/
lemma partialZbar_eq_zero_of_differentiable_complex {d : ℕ} {H : FormDu d → ℂ}
    (hH : Differentiable ℂ H) (j : Fin d) : partialZbar j H = 0 := by
  funext z
  rw [partialZbar]
  have hsmul : (Pi.single j Complex.I : FormDu d) = Complex.I • (Pi.single j (1 : ℂ)) := by
    funext i
    simp [Pi.single_apply]
  have hI : fderiv ℝ H z (Pi.single j Complex.I)
      = Complex.I * fderiv ℝ H z (Pi.single j (1 : ℂ)) := by
    rw [hsmul, (hH z).fderiv_restrictScalars ℝ]
    change (fderiv ℂ H z) (Complex.I • (Pi.single j (1 : ℂ)))
      = Complex.I * (fderiv ℂ H z) (Pi.single j (1 : ℂ))
    rw [map_smul, smul_eq_mul]
  rw [hI]
  rw [show Complex.I * (Complex.I * (fderiv ℝ H z) (Pi.single j (1 : ℂ)))
      = - (fderiv ℝ H z) (Pi.single j (1 : ℂ)) by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
  rw [add_neg_cancel, zero_div]
  rfl

end Dbar


end Submission.FUP

