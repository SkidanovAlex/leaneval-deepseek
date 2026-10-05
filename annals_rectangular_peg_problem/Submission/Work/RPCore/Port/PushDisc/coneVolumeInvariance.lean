import Mathlib
import Submission.Work.RPCore.Port.PushDisc.conicalFluxMachinery

/-!
# Invariance of the conical signed volume

For a family `Φ : ℝ × E → E` (`E = EuclideanSpace ℝ (Fin d)`) which is smooth off `{q | q.2 = 0}`,
radially `1`-homogeneous and norm preserving, the *conical signed volume*

`J(t) = ∫ y, χ y · det (D_y Φ (t,y))`

(with `χ` the annular cut-off of `conicalFluxMachinery`) is independent of `t`.

The proof is the classical divergence argument.  Pointwise
(`divE_cutoffField`) the divergence of the cut-off flux field `χ • fluxT Φ t` is
`χ y · ∂_t det (D_y Φ (t,y))`; the divergence theorem (`integral_divergence_eq_zero`) makes its
integral vanish, so `∫ χ · ∂_t det = 0` for every `t`; differentiating under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the domination supplied by compactness of
`tsupport χ`) turns this into `J' ≡ 0`, and `J` is constant.
-/

namespace Work.RPCore.Port.PushDisc

open scoped Matrix Topology
open MeasureTheory Filter

variable {d : ℕ}

/-! ## Smoothness, support and integrability of the cut-off flux field -/

section SmoothField

variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- The determinant of the conical Jacobian is smooth away from the origin. -/
lemma contDiffAt_det_jacM
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {p : ℝ × EuclideanSpace ℝ (Fin d)} (hp : p.2 ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => (jacM Φ q).det) p :=
  contDiffAt_det_of_entries (A := jacM Φ) fun i l => contDiffAt_jacM_entry hsm hp i l

/-- The derivative of the Jacobian determinant is continuous away from the origin. -/
lemma continuousOn_fderiv_det_jacM
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0}) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun q => (jacM Φ q).det) p) {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} := by
  intro p hp
  exact ((contDiffAt_det_jacM (Φ := Φ) hsm hp).continuousAt_fderiv (by simp)).continuousWithinAt

/-- The `t`-derivative of the Jacobian determinant is continuous away from the origin. -/
lemma continuousOn_vel_det_jacM
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0}) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun q => (jacM Φ q).det) p (1, 0))
      {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} :=
  (continuousOn_fderiv_det_jacM (Φ := Φ) hsm).clm_apply continuousOn_const

/-- The `χ ≠ 0` set is contained in the complement of the origin. -/
lemma tsupport_chi_subset :
    tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ) ⊆ {y : EuclideanSpace ℝ (Fin d) | y ≠ 0} := by
  intro y hy
  rw [Set.mem_setOf_eq]
  rintro rfl
  have hcompl : (Function.support (chi : EuclideanSpace ℝ (Fin d) → ℝ))ᶜ
      ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)) := by
    filter_upwards [chi_zero_near_zero] with z hz
    simpa [Function.mem_support] using hz
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff_nhds.mp hy _ hcompl
  exact hz1 hz2

/-- The flux field at a fixed time is smooth away from the origin. -/
lemma contDiffAt_fluxT
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {t : ℝ} {y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fluxT Φ t) y := by
  have hp : ((t, y) : ℝ × EuclideanSpace ℝ (Fin d)).2 ≠ 0 := hy
  have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : EuclideanSpace ℝ (Fin d) => (t, y')) y :=
    (contDiffAt_const (c := t)).prodMk contDiffAt_id
  have hcoord : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y' : EuclideanSpace ℝ (Fin d) => fun j : Fin d => fluxV Φ (t, y') j) y := by
    rw [contDiffAt_pi]
    intro j
    exact (contDiffAt_fluxV_entry (Φ := Φ) hsm hp j).comp y hpair
  have hcoe : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((coordE d).symm : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      (fun j : Fin d => fluxV Φ (t, y) j) :=
    (((coordE d).symm : (Fin d → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d)).contDiff).contDiffAt
  have hres := hcoe.comp y hcoord
  have hfun : fluxT Φ t
      = fun x : EuclideanSpace ℝ (Fin d) => (coordE d).symm (fun j : Fin d => fluxV Φ (t, x) j) := rfl
  rw [hfun]
  exact hres

/-- The cut-off flux field is smooth. -/
lemma contDiff_cutoffField
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (t : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutoffField Φ t) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin d)))).congr_of_eventuallyEq ?_
    filter_upwards [chi_zero_near_zero] with y' hy'
    simp [cutoffField_apply, hy']
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi : EuclideanSpace ℝ (Fin d) → ℝ) y :=
      contDiff_chi.contDiffAt
    have h2 := contDiffAt_fluxT (Φ := Φ) (t := t) hsm hy
    have hfun : cutoffField Φ t
        = fun y' : EuclideanSpace ℝ (Fin d) => chi y' • fluxT Φ t y' := rfl
    rw [hfun]
    exact h1.smul h2

/-- The cut-off flux field is differentiable everywhere. -/
lemma differentiableAt_cutoffField
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (t : ℝ) (y : EuclideanSpace ℝ (Fin d)) : DifferentiableAt ℝ (cutoffField Φ t) y :=
  (contDiff_cutoffField (Φ := Φ) hsm t).differentiable (by simp) y

/-- The cut-off flux field has compact support. -/
lemma hasCompactSupport_cutoffField (Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (t : ℝ) : HasCompactSupport (cutoffField Φ t) := by
  have h := (chi_hasCompactSupport (d := d)).smul_right (f' := fluxT Φ t)
  have hfun : cutoffField Φ t
      = fun y : EuclideanSpace ℝ (Fin d) => chi y • fluxT Φ t y := rfl
  rw [hfun]
  exact h

/-- The divergence of a compactly supported field has compact support. -/
lemma hasCompactSupport_divE {V : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hV : HasCompactSupport V) : HasCompactSupport (fun y => divE V y) := by
  refine hV.mono' fun y hy => ?_
  by_contra h
  have h0 : V =ᶠ[𝓝 y] 0 := by
    have hmem : (closure (Function.support V))ᶜ ∈ 𝓝 y := isClosed_closure.isOpen_compl.mem_nhds h
    filter_upwards [hmem] with z hz
    exact Function.notMem_support.mp fun hz' => hz (subset_closure hz')
  have hf : fderiv ℝ V y = 0 := by rw [h0.fderiv_eq]; simp
  refine hy ?_
  simp [divE, hf]

/-- The divergence of the cut-off flux field is continuous. -/
lemma continuous_divE_cutoffField
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (t : ℝ) : Continuous (fun y => divE (cutoffField Φ t) y) := by
  have hfd : Continuous (fderiv ℝ (cutoffField Φ t)) :=
    (contDiff_cutoffField (Φ := Φ) hsm t).continuous_fderiv (by simp)
  change Continuous (fun y : EuclideanSpace ℝ (Fin d) =>
    ∑ i : Fin d, ((fderiv ℝ (cutoffField Φ t) y) (EuclideanSpace.single i 1) :
      EuclideanSpace ℝ (Fin d)).ofLp i)
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp
    (hfd.clm_apply continuous_const))

end SmoothField

/-! ## The integral of the divergence -/

section IntegralZero

variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- The divergence of the cut-off flux field integrates to zero. -/
theorem integral_divE_cutoffField
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (t : ℝ) : ∫ y, divE (cutoffField Φ t) y = 0 := by
  refine integral_divergence_eq_zero (cutoffField Φ t) ∅ Set.countable_empty ?_ ?_ ?_ ?_
  · exact (contDiff_cutoffField (Φ := Φ) hsm t).continuous
  · exact hasCompactSupport_cutoffField Φ t
  · intro y _; exact (differentiableAt_cutoffField (Φ := Φ) hsm t y).hasFDerivAt
  · exact (continuous_divE_cutoffField (Φ := Φ) hsm t).integrable_of_hasCompactSupport
      (hasCompactSupport_divE (hasCompactSupport_cutoffField Φ t))

/-- The `t`-derivative of the determinant of the conical Jacobian integrates to zero. -/
theorem integral_chi_mul_vel_det
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖) (t : ℝ) :
    ∫ y, chi y * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
      (t, y) (1, 0) = 0 := by
  have h := integral_divE_cutoffField (Φ := Φ) hsm t
  rw [integral_congr_ae (Eventually.of_forall fun y =>
    divE_cutoffField (Φ := Φ) hsm hcone hnorm t y)] at h
  exact h

end IntegralZero

/-! ## Differentiation under the integral sign -/

section Parametric

variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- Differentiability of the determinant of the conical Jacobian along the `t`-axis. -/
lemma hasDerivAt_det_jacM_slice
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    {t : ℝ} {y : EuclideanSpace ℝ (Fin d)} (hy : y ≠ 0) :
    HasDerivAt (fun τ : ℝ => (jacM Φ (τ, y)).det)
      ((fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (t, y)) (1, 0)) t := by
  have hp : ((t, y) : ℝ × EuclideanSpace ℝ (Fin d)).2 ≠ 0 := hy
  have hJ : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (t, y)) (t, y) :=
    ((contDiffAt_det_jacM (Φ := Φ) hsm hp).differentiableAt (by simp)).hasFDerivAt
  have hc : HasDerivAt (fun τ : ℝ => ((τ, y) : ℝ × EuclideanSpace ℝ (Fin d))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  simpa [Function.comp_def] using hJ.comp_hasDerivAt t hc

/-- Measurability of the determinant of the conical Jacobian on a time slice. -/
lemma measurable_det_jacM_slice (σ : ℝ) :
    Measurable (fun a : EuclideanSpace ℝ (Fin d) => (jacM Φ (σ, a)).det) := by
  have hentry : ∀ i l : Fin d,
      Measurable (fun a : EuclideanSpace ℝ (Fin d) => jacM Φ (σ, a) i l) := by
    intro i l
    have hfd : Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (σ, z)) a) :=
      measurable_fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (σ, z))
    have h1 : Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => Φ (σ, z)) a)
          (EuclideanSpace.single l 1)) :=
      (ContinuousLinearMap.measurable_apply (𝕜 := ℝ)
        (EuclideanSpace.single l 1)).comp hfd
    exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.measurable.comp h1)
  have hfun : (fun a : EuclideanSpace ℝ (Fin d) => (jacM Φ (σ, a)).det)
      = fun a => ∑ σ' : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ' : ℤ) : ℝ) *
          ∏ i, jacM Φ (σ, a) (σ' i) i := by
    funext a; rw [Matrix.det_apply']
  rw [hfun]
  exact Finset.measurable_sum _ fun σ' _ =>
    measurable_const.mul (Finset.measurable_prod _ fun i _ => hentry (σ' i) i)

/-- Measurability of the `t`-derivative of the determinant of the conical Jacobian. -/
lemma measurable_vel_det_jacM (σ : ℝ) :
    Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (σ, a) (1, 0)) := by
  have h1 : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin d) =>
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) p) :=
    measurable_fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
  have h2 : Measurable (fun a : EuclideanSpace ℝ (Fin d) =>
      ((σ, a) : ℝ × EuclideanSpace ℝ (Fin d))) :=
    (continuous_const.prodMk continuous_id).measurable
  exact (ContinuousLinearMap.measurable_apply (𝕜 := ℝ) (E := ℝ × EuclideanSpace ℝ (Fin d))
    (1, 0)).comp (h1.comp h2)

/-- **Differentiation under the integral sign.**  The conical signed volume has vanishing
derivative. -/
theorem hasDerivAt_integral_jacM
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖) (σ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ y, chi y * (jacM Φ (τ, y)).det) 0 σ := by
  classical
  have hs : Set.Icc (σ - 1) (σ + 1) ∈ 𝓝 σ :=
    Icc_mem_nhds (by linarith) (by linarith)
  -- a uniform bound for the derivative on the annulus carrying `χ`
  have hK : IsCompact (Set.Icc (σ - 1) (σ + 1) ×ˢ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ)) :=
    isCompact_Icc.prod (chi_hasCompactSupport (d := d))
  have hsub : (Set.Icc (σ - 1) (σ + 1) ×ˢ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ))
      ⊆ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0} := fun q hq => tsupport_chi_subset hq.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_vel_det_jacM (Φ := Φ) hsm).mono hsub)
  set M : ℝ := max C 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMC : ∀ q ∈ Set.Icc (σ - 1) (σ + 1) ×ˢ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ),
      ‖fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) q (1, 0)‖ ≤ M :=
    fun q hq => le_trans (hC q hq) (le_max_left _ _)
  -- a uniform bound for the determinant itself on the annulus
  have hcont_slice : ContinuousOn (fun a : EuclideanSpace ℝ (Fin d) => (jacM Φ (σ, a)).det)
      (tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ)) := by
    intro a ha
    have ha0 : a ≠ 0 := tsupport_chi_subset ha
    have hp : ((σ, a) : ℝ × EuclideanSpace ℝ (Fin d)).2 ≠ 0 := ha0
    have hpair : ContinuousAt (fun a' : EuclideanSpace ℝ (Fin d) => (σ, a')) a :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact ((contDiffAt_det_jacM (Φ := Φ) hsm hp).continuousAt.comp hpair).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := (chi_hasCompactSupport (d := d)).exists_bound_of_continuousOn hcont_slice
  set M₂ : ℝ := max C₂ 0 with hM₂def
  have hM₂C : ∀ a ∈ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ),
      ‖(jacM Φ (σ, a)).det‖ ≤ M₂ := fun a ha => le_trans (hC₂ a ha) (le_max_left _ _)
  -- the dominating function
  have hchi_int : Integrable (fun a : EuclideanSpace ℝ (Fin d) => ‖chi a‖) volume :=
    (contDiff_chi.continuous.norm).integrable_of_hasCompactSupport
      (chi_hasCompactSupport (d := d)).norm
  have hbound_int : Integrable (fun a : EuclideanSpace ℝ (Fin d) => M * ‖chi a‖) volume :=
    hchi_int.const_mul M
  -- the hypotheses of the dominated-convergence lemma
  have hF_meas : ∀ᶠ x : ℝ in 𝓝 σ, AEStronglyMeasurable
      (fun a : EuclideanSpace ℝ (Fin d) => chi a * (jacM Φ (x, a)).det) volume :=
    Eventually.of_forall fun x =>
      ((contDiff_chi.continuous.measurable.mul (measurable_det_jacM_slice (Φ := Φ) x))
        |>.aestronglyMeasurable)
  have hF_int : Integrable (fun a : EuclideanSpace ℝ (Fin d) => chi a * (jacM Φ (σ, a)).det) volume := by
    refine (hchi_int.const_mul M₂).mono'
      ((contDiff_chi.continuous.measurable.mul (measurable_det_jacM_slice (Φ := Φ) σ))
        |>.aestronglyMeasurable) ?_
    filter_upwards with a
    by_cases ha : a ∈ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ)
    · calc ‖chi a * (jacM Φ (σ, a)).det‖
          = ‖chi a‖ * ‖(jacM Φ (σ, a)).det‖ := norm_mul _ _
        _ ≤ ‖chi a‖ * M₂ := mul_le_mul_of_nonneg_left (hM₂C a ha) (norm_nonneg _)
        _ = M₂ * ‖chi a‖ := mul_comm _ _
    · have hza : chi a = 0 := Function.notMem_support.mp fun h => ha (subset_tsupport _ h)
      simp [hza]
  have hF'_meas : AEStronglyMeasurable (fun a : EuclideanSpace ℝ (Fin d) =>
      chi a * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
        (σ, a) (1, 0)) volume :=
    ((contDiff_chi.continuous.measurable.mul (measurable_vel_det_jacM (Φ := Φ) σ))
      |>.aestronglyMeasurable)
  have h_bound : ∀ᵐ a : EuclideanSpace ℝ (Fin d) ∂volume, ∀ x ∈ Set.Icc (σ - 1) (σ + 1),
      ‖chi a * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
        (x, a) (1, 0)‖ ≤ M * ‖chi a‖ := by
    filter_upwards with a
    intro x hx
    by_cases ha : a ∈ tsupport (chi : EuclideanSpace ℝ (Fin d) → ℝ)
    · calc ‖chi a * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (x, a) (1, 0)‖
          = ‖chi a‖ * ‖(fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (x, a)) (1, 0)‖
              := norm_mul _ _
        _ ≤ ‖chi a‖ * M := mul_le_mul_of_nonneg_left (hMC (x, a) ⟨hx, ha⟩) (norm_nonneg _)
        _ = M * ‖chi a‖ := mul_comm _ _
    · have hza : chi a = 0 := Function.notMem_support.mp fun h => ha (subset_tsupport _ h)
      simp [hza]
  have h_diff : ∀ᵐ a : EuclideanSpace ℝ (Fin d) ∂volume, ∀ x ∈ Set.Icc (σ - 1) (σ + 1),
      HasDerivAt (fun τ : ℝ => chi a * (jacM Φ (τ, a)).det)
        (chi a * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det)
          (x, a) (1, 0)) x := by
    filter_upwards with a
    intro x _
    by_cases ha : chi a = 0
    · have hfun : (fun τ : ℝ => chi a * (jacM Φ (τ, a)).det) = fun _ : ℝ => 0 := by
        funext τ; rw [ha, zero_mul]
      rw [hfun, ha, zero_mul]
      exact hasDerivAt_const x (0 : ℝ)
    · have ha0 : a ≠ 0 := fun h => ha (by rw [h]; exact chi_eq_zero_of_small (by simp))
      exact (hasDerivAt_det_jacM_slice (Φ := Φ) hsm ha0).const_mul (chi a)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := σ)
    (s := Set.Icc (σ - 1) (σ + 1))
    (F := fun τ (a : EuclideanSpace ℝ (Fin d)) => chi a * (jacM Φ (τ, a)).det)
    (F' := fun τ (a : EuclideanSpace ℝ (Fin d)) =>
      chi a * fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin d) => (jacM Φ q).det) (τ, a) (1, 0))
    (bound := fun a : EuclideanSpace ℝ (Fin d) => M * ‖chi a‖)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  rw [integral_chi_mul_vel_det (Φ := Φ) hsm hcone hnorm σ] at key
  exact key.2

end Parametric

/-! ## Invariance -/

section Invariance

variable {Φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- **Invariance of the conical signed volume.** -/
theorem coneVolume_invariant
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {q : ℝ × EuclideanSpace ℝ (Fin d) | q.2 ≠ 0})
    (hcone : ∀ (t r : ℝ) (y : EuclideanSpace ℝ (Fin d)), 0 < r → Φ (t, r • y) = r • Φ (t, y))
    (hnorm : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin d)), ‖Φ (t, y)‖ = ‖y‖) (a b : ℝ) :
    (∫ y, chi y * (jacM Φ (a, y)).det) = ∫ y, chi y * (jacM Φ (b, y)).det := by
  have hderiv : ∀ σ : ℝ,
      deriv (fun τ : ℝ => ∫ y, chi y * (jacM Φ (τ, y)).det) σ = 0 := fun σ =>
    (hasDerivAt_integral_jacM (Φ := Φ) hsm hcone hnorm σ).deriv
  have hdiff : Differentiable ℝ (fun τ : ℝ => ∫ y, chi y * (jacM Φ (τ, y)).det) := fun σ =>
    (hasDerivAt_integral_jacM (Φ := Φ) hsm hcone hnorm σ).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff hderiv a b

end Invariance

end Work.RPCore.Port.PushDisc
