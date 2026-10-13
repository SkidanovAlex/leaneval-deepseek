import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.PressureOn.vorticity_cross_eq
import Submission.Work.FTS.BSSwirl.integral_vorticity_eq
import Submission.Work.FTS.BSSwirl.contDiff_vorticity_and_support
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.OffPlanes.offPlanes_ibp
import Submission.Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero
import Submission.Work.FTS.PressureOn.integrable_mul_div
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.div_vorticity_mul_eq_zero
import Submission.Work.FTS.PressureOn.weakCurl.weyl_cross

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


/-!
# `weakCurl_pair`

See the module docstring of `Defs.lean` for the role of this lemma in the pressure reconstruction:
it is the statement that `∂_t curl u = curl ∂_t u` **weakly**, i.e. that the pairings of `∂_t u` and
of `u × ω` against a curl `A` agree.

## Route

* `BSSwirl.integral_vorticity_eq` (the curl is self-adjoint on `ℝ³`) gives, for every `s` near `t`,
  `∫ ⟪u(·,s), curl A⟫ = ∫ ⟪curl u(·,s), A⟫ = ∫ ⟪ω(·,s), A⟫`;
* differentiating in `s` at `t` (`tendsto_integral_slope_self`) gives
  `∫ ⟪∂_t u(·,t), curl A⟫ = ∫ ⟪∂_t ω(·,t), A⟫`;
* the pointwise vorticity equation (`hvort`, valid a.e.) rewrites the right-hand side as
  `X := ∫ ⟪(ω·∇)u, A⟫ - ∫ ⟪(u·∇)ω, A⟫`;
* `vorticity_cross_eq` gives `curl (u × ω) = (div ω) • u + (ω·∇)u - (u·∇)ω` (using `div u = 0`), so
  `∫ ⟪curl (u×ω), A⟫ = T1 + X` with `T1 := ∫ div ω · ⟪u,A⟫`;
* the pointwise Weyl identity `BSSwirl.inner_vorticity_sub_eq_div` turns
  `∫ ⟪curl (u × ω), A⟫` into `∫ ⟪u × ω, curl A⟫ + ∫ div((u×ω) × A)`, and the last integral
  vanishes (it is `∫ div(ω⟪u,A⟫) - ∫ div(u⟪ω,A⟫) = 0`, the first term by the off-plane integration
  by parts `OffPlanes.offPlanes_ibp` together with `CurlGrad.vorticity_gradient_integral_eq_zero`,
  the second by `div u = 0`);
* finally `T1 = 0`, again by the off-plane integration by parts and
  `CurlGrad.vorticity_gradient_integral_eq_zero`.

Hence `∫ ⟪u × ω, curl A⟫ = T1 + X = X = ∫ ⟪∂_t u, curl A⟫`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open MeasureTheory Filter Set Topology
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

/-! ## Nullity of the complement of `Uax` -/

/-- **Every coordinate hyperplane of `ℝ³` is Lebesgue-null.** -/
lemma volume_coord_eq_zero_R3 (i : Fin 3) (c : ℝ) :
    volume {x : R3 | x i = c} = 0 := by
  have hmap : Measure.map (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) volume = volume :=
    (PiLp.volume_preserving_toLp (Fin 3)).map_eq
  rw [← hmap, MeasureTheory.Measure.map_apply (by fun_prop) (by measurability)]
  have h : (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) ⁻¹' {x : R3 | x i = c}
      = {v : Fin 3 → ℝ | v i = c} := by
    ext v; simp
  rw [h, MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) i c

lemma volume_Uax_compl_eq_zero : volume (Uaxᶜ : Set R3) = 0 := by
  have hsub : (Uaxᶜ : Set R3) ⊆ {x : R3 | x 2 = 0} ∪ {x : R3 | x 0 = 0} := by
    intro x hx
    by_cases h1 : x 2 = 0
    · exact Or.inl h1
    · right
      have h2 : x 0 ^ 2 + x 1 ^ 2 = 0 := not_not.mp (fun hc => hx ⟨h1, hc⟩)
      have hA : x 0 ^ 2 = 0 := by nlinarith [sq_nonneg (x 1)]
      simpa using (sq_eq_zero_iff.mp hA)
  exact measure_mono_null hsub
    (measure_union_null (volume_coord_eq_zero_R3 2 0) (volume_coord_eq_zero_R3 0 0))

lemma ae_mem_Uax : ∀ᵐ x ∂(volume : Measure R3), x ∈ Uax := by
  rw [MeasureTheory.ae_iff]
  exact volume_Uax_compl_eq_zero

/-! ## A compact-support integrability helper -/

/-- A coordinate entry `y ↦ (Dω y)(e k)_j` of the Jacobian is locally integrable whenever `Dω`
is. -/
lemma locallyIntegrable_entry {ω : R3 → R3}
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ ω x)) (k j : Fin 3) :
    MeasureTheory.LocallyIntegrable
      (fun y : R3 => (fderiv ℝ ω y) (FiniteTimeSingularity.e k) j) := by
  set hL : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).comp
      (ContinuousLinearMap.apply ℝ R3 (FiniteTimeSingularity.e k)) with hLdef
  have key : (fun y : R3 => (fderiv ℝ ω y) (FiniteTimeSingularity.e k) j)
      = ⇑hL ∘ (fun x => fderiv ℝ ω x) := by
    funext y
    simp only [Function.comp_apply, hLdef, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.apply_apply, PiLp.proj_apply]
  rw [key]
  exact MeasureTheory.locallyIntegrableOn_univ.mp
    (hL.locallyIntegrableOn_comp (MeasureTheory.locallyIntegrableOn_univ.mpr hωint))

/-- A function supported in a compact set and dominated by a locally integrable function is
integrable. -/
lemma integrable_of_support_subset_compact_of_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : R3 → ℝ} {g : R3 → E} {K : Set R3} (hK : IsCompact K)
    (hf : ∀ x, x ∉ K → f x = 0) (hfm : AEStronglyMeasurable f) (hgl : LocallyIntegrable g)
    {C : ℝ} (hbd : ∀ x, ‖f x‖ ≤ C * (‖g x‖ + 1)) : Integrable f := by
  have hbase : IntegrableOn (fun x => C * (‖g x‖ + 1)) K :=
    (((hgl.integrableOn_isCompact hK).norm.add
      (integrableOn_const (μ := volume) (s := K) hK.measure_ne_top))).const_mul C
  have hgi : Integrable (K.indicator (fun x => C * (‖g x‖ + 1))) :=
    (integrable_indicator_iff hK.measurableSet).mpr hbase
  refine hgi.mono' hfm ?_
  filter_upwards with x
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact hbd x
  · rw [hf x hx, norm_zero, Set.indicator_of_notMem hx]

/-! ## The main theorem -/

theorem weakCurl_pair {u ω : R3 → ℝ → R3} {t : ℝ} {A : R3 → R3}
    (hA : ∀ n : ℕ, ContDiff ℝ n A) (hAcs : HasCompactSupport A)
    (hR : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R)
    (hsnbhd : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ContDiff ℝ 1 (u · s))
    (hcurl : ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x,
      FiniteTimeSingularity.vorticity (fun y => u y s) x = ω x s)
    (hdivu : ∀ s ∈ Set.Ioo (t - 1) (t + 1), FiniteTimeSingularity.div (u · s) = 0)
    (hωcont : Continuous (fun x => ω x t))
    (hωdiff : ∀ x, x 0 ≠ 0 → x 2 ≠ 0 → HasFDerivAt (fun x => ω x t) (fderiv ℝ (ω · t) x) x)
    (hωint : MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x))
    (huderiv : ∀ x, HasDerivWithinAt (u x) (FiniteTimeSingularity.timeDeriv u x t) (Set.Ici t) t)
    (hωderiv : ∀ x, HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hulip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|)
    (hωlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖ω x s - ω x t‖ ≤ C * |s - t|)
    (hvort : ∀ x ∈ Uax, FiniteTimeSingularity.timeDeriv ω x t
        + FiniteTimeSingularity.directionalDeriv ω u x t
          = FiniteTimeSingularity.directionalDeriv u ω x t) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (FiniteTimeSingularity.vorticity A x)
      = ∫ x, inner ℝ (crossVec (u x t) (ω x t)) (FiniteTimeSingularity.vorticity A x) := by
  have hBcs : HasCompactSupport (fun x => vorticity A x) :=
    (BSSwirl.contDiff_vorticity_and_support hA hAcs).2
  have hBcont : Continuous (fun x => vorticity A x) :=
    ((BSSwirl.contDiff_vorticity_and_support hA hAcs).1 0).continuous
  -- ## Step 1: for every `s` near `t`, the two pairings agree
  have hident : ∀ s ∈ Ioo (t - 1) (t + 1),
      ∫ x, inner ℝ (u x s) (vorticity A x) = ∫ x, inner ℝ (ω x s) (A x) := by
    intro s hs
    have h := BSSwirl.integral_vorticity_eq (V := fun x => u x s) (Ψ := A) (hsnbhd s hs) hA hAcs
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hcurl s hs x]
  -- ## Step 2: differentiate the identity in `s` at `t`
  have hucont : ∀ᶠ s in nhdsWithin t (Ioi t), Continuous (fun x => u x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact (hsnbhd s ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩).continuous
  have hwcont : ∀ᶠ s in nhdsWithin t (Ioi t), Continuous (fun x => ω x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    rw [show (fun x => ω x s) = fun x => vorticity (fun y => u y s) x from
      funext (fun x => (hcurl s hsI x).symm)]
    exact BSSwirl.continuous_vorticity (hsnbhd s hsI)
  have hlim_u := tendsto_integral_slope_self (u := u) (t := t) (w := fun x => vorticity A x)
    hBcont hBcs hucont huderiv hulip
  have hlim_w := tendsto_integral_slope_self (u := ω) (t := t) (w := A)
    (hA 0).continuous hAcs hwcont hωderiv hωlip
  -- the slope integrals are the difference quotients of the two pairings
  have hquot_u : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
        = ((∫ x, inner ℝ (u x s) (vorticity A x))
            - (∫ x, inner ℝ (u x t) (vorticity A x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
    have hcs : ContDiff ℝ 1 (fun x => u x s) := hsnbhd s hsI
    have hct : ContDiff ℝ 1 (fun x => u x t) := hsnbhd t htI
    have hIs : Integrable (fun x => inner ℝ (u x s) (vorticity A x)) :=
      (hcs.continuous.inner hBcont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hBcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hIt : Integrable (fun x => inner ℝ (u x t) (vorticity A x)) :=
      (hct.continuous.inner hBcont).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hBcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hsub : (∫ x, inner ℝ (u x s - u x t) (vorticity A x))
        = (∫ x, inner ℝ (u x s) (vorticity A x))
          - (∫ x, inner ℝ (u x t) (vorticity A x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (u x s - u x t) (vorticity A x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  have hquot_w : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x))
        = ((∫ x, inner ℝ (ω x s) (A x))
            - (∫ x, inner ℝ (ω x t) (A x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hsI : s ∈ Ioo (t - 1) (t + 1) :=
      ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
    have hcs : Continuous (fun x => ω x s) := by
      rw [show (fun x => ω x s) = fun x => vorticity (fun y => u y s) x from
        funext (fun x => (hcurl s hsI x).symm)]
      exact BSSwirl.continuous_vorticity (hsnbhd s hsI)
    have hct : Continuous (fun x => ω x t) := hωcont
    have hIs : Integrable (fun x => inner ℝ (ω x s) (A x)) :=
      (hcs.inner (hA 0).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hAcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hIt : Integrable (fun x => inner ℝ (ω x t) (A x)) :=
      (hct.inner (hA 0).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hAcs (by
          intro x hx
          rw [Function.mem_support] at hx
          exact subset_tsupport _ (by
            rw [Function.mem_support]
            intro h0
            exact hx (by simp [h0]))))
    have hsub : (∫ x, inner ℝ (ω x s - ω x t) (A x))
        = (∫ x, inner ℝ (ω x s) (A x)) - (∫ x, inner ℝ (ω x t) (A x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (ω x s - ω x t) (A x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  have hEq : ∀ᶠ s in nhdsWithin t (Ioi t),
      (∫ x, inner ℝ (u x s) (vorticity A x)) = ∫ x, inner ℝ (ω x s) (A x) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, -⟩
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_ball, Real.dist_eq] at hs
    exact hident s ⟨by linarith [(abs_lt.mp hs).1], by linarith [(abs_lt.mp hs).2]⟩
  have hEq_t : (∫ x, inner ℝ (u x t) (vorticity A x)) = ∫ x, inner ℝ (ω x t) (A x) :=
    hident t ⟨by linarith, by linarith⟩
  have hQeq : (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (vorticity A x))
      =ᶠ[nhdsWithin t (Ioi t)]
      (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (ω x s - ω x t)) (A x)) := by
    filter_upwards [hquot_u, hquot_w, hEq] with s h1 h2 h3
    rw [h1, h2, h3, hEq_t]
  -- ## the conclusion of Step 2
  have hLHS_eq : (∫ x, inner ℝ (timeDeriv u x t) (vorticity A x))
      = ∫ x, inner ℝ (timeDeriv ω x t) (A x) :=
    tendsto_nhds_unique hlim_u (hlim_w.congr' hQeq.symm)
  -- ## Step 3: the pointwise vorticity equation
  have hLHS_eq2 : (∫ x, inner ℝ (timeDeriv ω x t) (A x))
      = ∫ x, inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Uax] with x hx
    have h := hvort x hx
    simp only [FiniteTimeSingularity.directionalDeriv] at h
    have h' : timeDeriv ω x t
        = fderiv ℝ (fun y => u y t) x (ω x t) - fderiv ℝ (fun y => ω y t) x (u x t) := by
      rw [eq_sub_iff_add_eq]
      exact h
    rw [h']
  rw [hLHS_eq, hLHS_eq2]
  -- ## Step 4: the pointwise curl of `u × ω` and the three remaining integrals
  obtain ⟨R, hR0, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Ioo (t - 1) (t + 1), ∀ x, ω x s ≠ 0 → ‖x‖ ≤ R := hR
  have htI : t ∈ Ioo (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hu_t : ContDiff ℝ 1 (fun y => u y t) := hsnbhd t htI
  have hdu_t : ∀ x, HasFDerivAt (fun y => u y t) (fderiv ℝ (fun y => u y t) x) x := fun x =>
    (hu_t.differentiable_one x).hasFDerivAt
  have hωcs_t : HasCompactSupport (fun y => ω y t) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R) ?_
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hRbd t htI x hx
  have hae_diff : ∀ᵐ x ∂(volume : Measure R3), x 0 ≠ 0 ∧ x 2 ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have h : {x : R3 | ¬(x 0 ≠ 0 ∧ x 2 ≠ 0)} = {x : R3 | x 0 = 0} ∪ {x : R3 | x 2 = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or, not_ne_iff]
    rw [h]
    exact measure_union_null (volume_coord_eq_zero_R3 0 0) (volume_coord_eq_zero_R3 2 0)
  have hdivω_eq : ∀ x, div (fun y => ω y t) x
      = ∑ j : Fin 3, fderiv ℝ (fun y => ω y t) x (FiniteTimeSingularity.e j) j := fun x =>
    vorticityCross_div_eq_sum_diag _ _
  -- the pointwise identity for `curl (u × ω)`
  have hptcurl : ∀ᵐ x ∂(volume : Measure R3),
      inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x)
        = div (fun y => ω y t) x * inner ℝ (u x t) (A x)
          + inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
              - fderiv ℝ (fun y => ω y t) x (u x t)) (A x) := by
    filter_upwards [hae_diff] with x hx
    have hvc := vorticity_cross_eq (u := fun y => u y t) (ω := fun y => ω y t)
      (hdu_t x) (hωdiff x hx.1 hx.2)
    have hdiv0 : div (fun y => u y t) x = 0 := congrFun (hdivu t htI) x
    rw [hvc, hdiv0, zero_smul, sub_zero, inner_sub_left, inner_add_left, real_inner_smul_left,
      inner_sub_left]
    ring
  -- the compact set on which everything lives
  have hK : IsCompact (tsupport (fun y => ω y t)) := hωcs_t.isCompact
  have hKω : ∀ x, x ∉ tsupport (fun y => ω y t) → ω x t = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (f := fun y => ω y t) hx
  have hKfd : ∀ x, x ∉ tsupport (fun y => ω y t) →
      fderiv ℝ (fun y => ω y t) x = 0 := fun x hx =>
    fderiv_eq_zero_of_notMem_tsupport (G := fun y => ω y t) hx
  -- integrability of the two summands
  have hw : ContDiff ℝ 1 (fun p : R3 × R3 => inner ℝ p.1 p.2) :=
    isBoundedBilinearMap_inner.contDiff
  have hψh : ContDiff ℝ 1 (fun x => inner ℝ (u x t) (A x)) :=
    hw.comp (hu_t.prodMk (hA 1))
  have hψhcs : HasCompactSupport (fun x => inner ℝ (u x t) (A x)) := by
    refine hAcs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro hAx
      exact hx (by rw [hAx, inner_zero_right]))
  have hInt1 : Integrable (fun x => div (fun y => ω y t) x * inner ℝ (u x t) (A x)) := by
    have h := integrable_mul_div (ω := fun y => ω y t) hωint hψh hψhcs
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact mul_comm _ _
  have hInt2 : Integrable (fun x => inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
      - fderiv ℝ (fun y => ω y t) x (u x t)) (A x)) :=
    weakCurl.int2_integrable hA hAcs ⟨R, hR0, hRbd⟩ hsnbhd hωcont hωdiff hωint
  -- (A)
  have hA1 : (∫ x, inner ℝ (fderiv ℝ (fun y => u y t) x (ω x t)
          - fderiv ℝ (fun y => ω y t) x (u x t)) (A x))
      = (∫ x, inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x))
        - ∫ x, div (fun y => ω y t) x * inner ℝ (u x t) (A x) := by
    have h := integral_congr_ae hptcurl
    rw [integral_add hInt1 hInt2] at h
    linarith
  -- (C): the divergence term vanishes
  have hT1 : (∫ x, div (fun y => ω y t) x * inner ℝ (u x t) (A x)) = 0 :=
    div_vorticity_mul_eq_zero hu_t (fun x => hcurl t htI x) hωcont
      ⟨R, fun x hx => hRbd t htI x hx⟩ hωdiff hωint hψh hψhcs
  -- (B): the Weyl identity
  have hB1 : (∫ x, inner ℝ (crossVec (u x t) (ω x t)) (vorticity A x))
      = ∫ x, inner ℝ (vorticity (fun y => crossVec (u y t) (ω y t)) x) (A x) :=
    weakCurl.weyl_cross hA hAcs ⟨R, hR0, hRbd⟩ hsnbhd hcurl hdivu hωcont hωdiff hωint
  rw [hB1, hA1, hT1, sub_zero]

end Work.FTS.PressureOn
