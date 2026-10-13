import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.FTS.EllipticEst.hasDerivAt_self_antideriv
import Submission.Work.FTS.EllipticEst.exists_bound_div_cos
import Submission.Work.FTS.EllipticEst.continuousOn_antideriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Two functions which agree on the open interval `(0, π/2)` agree almost everywhere on the
closed interval, since the two endpoints are a null set. -/
private lemma ae_eq_restrict_of_eqOn_Ioo {g h : ℝ → ℝ}
    (hgh : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), g θ = h θ) :
    g =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] h := by
  show ∀ᵐ θ ∂(volume.restrict (Icc (0 : ℝ) (π / 2))), g θ = h θ
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [mem_ofPred_eq, not_imp, mem_Icc] at hθ
    obtain ⟨hθs, hne⟩ := hθ
    rcases eq_or_lt_of_le hθs.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hθs.2 with h2 | h2
      · exact Or.inr h2
      · exact absurd (hgh θ ⟨h, h2⟩) hne
  · rw [show ({0, π / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {π / 2} from by
      ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
    exact measure_union_null (measure_singleton 0) (measure_singleton (π / 2))

/-- The main workhorse: the angular integration by parts for a single function `f`. -/
private lemma Lzero_self_form_aux (f : ℝ → ℝ)
    (hs : ContDiffOn ℝ 2 f (Icc (0 : ℝ) (π / 2))) (h0 : f 0 = 0) (h1 : f (π / 2) = 0) :
    (∫ θ in Icc (0 : ℝ) (π / 2), Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      = (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  have hlt : (0 : ℝ) < π / 2 := by positivity
  set dW : ℝ → ℝ := derivWithin f (Icc (0 : ℝ) (π / 2)) with hdW
  set ps : ℝ → ℝ := derivWithin dW (Icc (0 : ℝ) (π / 2)) with hps
  set FW : ℝ → ℝ := fun θ => -(dW θ) * f θ + (1 / 2) * Real.tan θ * (f θ) ^ 2 with hFW
  set R0 : ℝ → ℝ := fun θ => (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
    + Real.sin θ * (f θ / Real.cos θ) * dW θ with hR0
  -- continuity of the auxiliary functions
  have hdW_cont : ContinuousOn dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hdW_cd : ContDiffOn ℝ 1 dW (Icc (0 : ℝ) (π / 2)) := by
    rw [hdW]
    exact hs.derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hps_cont : ContinuousOn ps (Icc (0 : ℝ) (π / 2)) := by
    rw [hps]
    exact hdW_cd.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hf_cont : ContinuousOn f (Icc (0 : ℝ) (π / 2)) := hs.continuousOn
  -- the pointwise facts relating `deriv f` to `dW`, `deriv (deriv f)` to `ps`
  have hcos_ne : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    have hmem : θ ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
  have hdf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv f θ = dW θ := by
    intro θ hθ
    rw [hdW]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  have hddf : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), deriv (deriv f) θ = ps θ := by
    intro θ hθ
    have hev : deriv f =ᶠ[𝓝 θ] dW := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)).symm
    rw [hev.deriv_eq, hps]
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  -- the pointwise derivative identity, via the delegated lemma
  have hderiv_FW : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = Work.Elliptic.Lzero (fun _ s => f s) 0 θ * f θ
        - (deriv f θ) ^ 2 - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2 := by
    intro θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hA := hasDerivAt_self_antideriv f θ hθ h2
    have hev : FW =ᶠ[𝓝 θ]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    exact (hA.congr_of_eventuallyEq hev).deriv
  -- the a.e. identity for `Lzero · f`
  have hA_ae : (fun θ => Work.Elliptic.Lzero (fun _ θ' => f θ') 0 θ * f θ)
      =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))]
      (fun θ => deriv FW θ + (deriv f θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        - 6 * (f θ) ^ 2) := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hderiv_FW θ hθ]
    ring
  -- the explicit computation of `deriv FW`
  have hFW_deriv : ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
      deriv FW θ = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := hcos_ne θ hθ
    have h2 : ContDiffAt ℝ 2 f θ := hs.contDiffAt (Icc_mem_nhds hθ.1 hθ.2)
    have hfd : HasDerivAt f (dW θ) θ :=
      ((h2.differentiableAt (by norm_num)).hasDerivAt).congr_deriv (hdf θ hθ)
    have hev : dW =ᶠ[𝓝 θ] deriv f := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
      rw [hdW]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
    have hdW_d : HasDerivAt dW (ps θ) θ :=
      ((((h2.derivWithin (m := 1) (by norm_num)).differentiableAt (n := 1)
        (by norm_num)).hasDerivAt).congr_deriv (hddf θ hθ)).congr_of_eventuallyEq hev
    have h1 : HasDerivAt (fun y => (-(dW y)) * f y)
        ((-(ps θ)) * f θ + (-(dW θ)) * dW θ) θ := hdW_d.neg.mul hfd
    have h2p : HasDerivAt (fun y => (f y) ^ 2) (2 * f θ ^ (2 - 1) * dW θ) θ := hfd.pow 2
    have h3 : HasDerivAt (fun y => Real.tan y * (f y) ^ 2)
        ((1 / Real.cos θ ^ 2) * (f θ) ^ 2 + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ)) θ :=
      (Real.hasDerivAt_tan hcos).mul h2p
    have h4 : HasDerivAt (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))
        ((1 / 2) * ((1 / Real.cos θ ^ 2) * (f θ) ^ 2
          + Real.tan θ * (2 * f θ ^ (2 - 1) * dW θ))) θ := h3.const_mul (1 / 2)
    have h5 := (h1.add h4).congr_of_eventuallyEq
      (show FW =ᶠ[𝓝 θ] ((fun y => (-(dW y)) * f y)
        + (fun y => (1 / 2) * (Real.tan y * (f y) ^ 2))) from by
        filter_upwards with y
        simp only [Pi.add_apply, hFW]
        ring)
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    rw [h5.deriv, h21, pow_one, div_pow]
    ring
  -- the a.e. identity for the derivative of `FW`, in a form with bounded pieces
  have hE_ae : (fun θ => deriv FW θ) =ᵐ[volume.restrict (Icc (0 : ℝ) (π / 2))] R0 := by
    refine ae_eq_restrict_of_eqOn_Ioo (fun θ hθ => ?_)
    rw [hFW_deriv θ hθ, hR0]
    change (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.tan θ * dW θ * f θ
      = (-(ps θ)) * f θ - (dW θ) ^ 2 + (1 / 2) * (f θ / Real.cos θ) ^ 2
        + Real.sin θ * (f θ / Real.cos θ) * dW θ
    rw [Real.tan_eq_sin_div_cos]
    ring
  -- bounds
  obtain ⟨Cb, hCb0, hCb⟩ := exists_bound_div_cos f hs h1
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hdW_cont
  -- measurability
  have hf_aem : AEMeasurable f (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_cont.aemeasurable measurableSet_Icc
  have hdiv_aem : AEMeasurable (fun θ => f θ / Real.cos θ)
      (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hf_aem.div Real.measurable_cos.aemeasurable
  have hdW_aem : AEMeasurable dW (volume.restrict (Icc (0 : ℝ) (π / 2))) :=
    hdW_cont.aemeasurable measurableSet_Icc
  -- integrability of the pieces
  have hD_int : IntegrableOn (fun θ => (f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hf_cont.pow 2).integrableOn_compact isCompact_Icc
  have hC_int : IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb ^ 2) ?_
    · have heq : (fun θ => (f θ / Real.cos θ) ^ 2)
          = (fun θ => f θ / Real.cos θ) * (fun θ => f θ / Real.cos θ) := by
        funext θ; simp only [Pi.mul_apply, sq]
      rw [heq]
      exact (hdiv_aem.mul hdiv_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have h2 : (f θ / Real.cos θ) ^ 2 ≤ Cb ^ 2 := by
        rw [← sq_abs (f θ / Real.cos θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h2
  have hBsq_int : IntegrableOn (fun θ => (dW θ) ^ 2) (Icc (0 : ℝ) (π / 2)) :=
    (hdW_cont.pow 2).integrableOn_compact isCompact_Icc
  have hB_int : IntegrableOn (fun θ => (deriv f θ) ^ 2) (Icc (0 : ℝ) (π / 2)) := by
    have h := ae_eq_restrict_of_eqOn_Ioo (g := fun θ => deriv f θ) (h := dW)
      (fun θ hθ => hdf θ hθ)
    refine hBsq_int.congr_fun_ae ?_
    filter_upwards [h.symm] with θ hθ
    rw [hθ]
  have hA4_int : IntegrableOn (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
      (Icc (0 : ℝ) (π / 2)) := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (Cb * M1) ?_
    · have heq : (fun θ => Real.sin θ * (f θ / Real.cos θ) * dW θ)
          = (Real.sin * (fun θ => f θ / Real.cos θ)) * dW := by
        funext θ; simp only [Pi.mul_apply]
      rw [heq]
      exact ((Real.continuous_sin.measurable.aemeasurable.mul hdiv_aem).mul
        hdW_aem).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Icc]
      refine Eventually.of_forall (fun θ hθ => ?_)
      have hx := hCb θ hθ
      have hy' : |dW θ| ≤ M1 := by simpa only [Real.norm_eq_abs] using hM1 θ hθ
      have hs1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |Real.sin θ| * |f θ / Real.cos θ| * |dW θ|
          ≤ 1 * Cb * M1 := by gcongr
        _ = Cb * M1 := by ring
  have hA1_int : IntegrableOn (fun θ => (-(ps θ)) * f θ) (Icc (0 : ℝ) (π / 2)) :=
    ((continuous_neg.comp_continuousOn hps_cont).mul hf_cont).integrableOn_compact
      isCompact_Icc
  have hR0_int : IntegrableOn R0 (Icc (0 : ℝ) (π / 2)) := by
    have hsum := (hA1_int.sub hBsq_int).add
      ((Integrable.const_mul hC_int (1 / 2)).add hA4_int)
    refine hsum.congr_fun_ae ?_
    refine Eventually.of_forall (fun θ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hR0]
    ring
  have hE_int : IntegrableOn (fun θ => deriv FW θ) (Icc (0 : ℝ) (π / 2)) :=
    hR0_int.congr_fun_ae hE_ae.symm
  -- the fundamental theorem of calculus for the antiderivative
  have hFW_cont : ContinuousOn FW (Icc (0 : ℝ) (π / 2)) := by
    rw [hFW, hdW]
    exact continuousOn_antideriv f hs h1
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (π / 2), HasDerivAt FW (deriv FW x) x := by
    intro x hx
    have h2 : ContDiffAt ℝ 2 f x := hs.contDiffAt (Icc_mem_nhds hx.1 hx.2)
    have hA := hasDerivAt_self_antideriv f x hx h2
    have hev : FW =ᶠ[𝓝 x]
        (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp only [hFW, hdW, derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
    have hA' := hA.congr_of_eventuallyEq hev
    rw [hA'.deriv]
    exact hA'
  have hint : IntervalIntegrable (fun θ => deriv FW θ) volume (0 : ℝ) (π / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr hE_int
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2), deriv FW θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFW_cont hderiv hint, hFW]
    simp only [h0, h1, mul_zero, Real.tan_zero]
    norm_num
  have hFTC' : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    exact hFTC
  -- assemble
  have hF1 : IntegrableOn ((fun θ => deriv FW θ) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hE_int
  have hF2 : IntegrableOn ((fun θ => (deriv f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) := hB_int
  have hF3 : IntegrableOn ((fun θ => (1 / 2) * (f θ / Real.cos θ) ^ 2) : ℝ → ℝ)
      (Icc (0 : ℝ) (π / 2)) := Integrable.const_mul hC_int (1 / 2)
  have hF4 : IntegrableOn ((fun θ => 6 * (f θ) ^ 2) : ℝ → ℝ) (Icc (0 : ℝ) (π / 2)) :=
    Integrable.const_mul hD_int 6
  have hF12 := hF1.add hF2
  have hF123 := hF12.add hF3
  have hsp1 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2 - 6 * (f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
          + (1 / 2) * (f θ / Real.cos θ) ^ 2)
        - (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2) :=
    integral_sub hF123 hF4
  have hsp2 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2
        + (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2) :=
    integral_add hF12 hF3
  have hsp3 : (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ + (deriv f θ) ^ 2)
      = (∫ θ in Icc (0 : ℝ) (π / 2), deriv FW θ)
        + (∫ θ in Icc (0 : ℝ) (π / 2), (deriv f θ) ^ 2) :=
    integral_add hF1 hF2
  have hsp4 : (∫ θ in Icc (0 : ℝ) (π / 2), (1 / 2) * (f θ / Real.cos θ) ^ 2)
      = (1 / 2) * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ / Real.cos θ) ^ 2) :=
    integral_const_mul (1 / 2) (fun θ => (f θ / Real.cos θ) ^ 2)
  have hsp5 : (∫ θ in Icc (0 : ℝ) (π / 2), 6 * (f θ) ^ 2)
      = 6 * (∫ θ in Icc (0 : ℝ) (π / 2), (f θ) ^ 2) :=
    integral_const_mul 6 (fun θ => (f θ) ^ 2)
  rw [integral_congr_ae hA_ae, hsp1, hsp2, hsp3, hsp4, hsp5, hFTC']
  ring

/-- The angular integration by parts against the function itself: for a `C²` slice `θ ↦ v z θ`
vanishing at `θ = 0, π/2`, the pairing of `Lzero` with `v` is the quadratic form
`∫ v_θ² + (1/2) ∫ (v/cos)² - 6 ∫ v²`.  (The antiderivative is `-v' v + (1/2) tan θ · v²`; at the
endpoints it vanishes, at `π/2` because `v` vanishes to first order there.) -/
theorem Lzero_self_form (v : ℝ → ℝ → ℝ) (z : ℝ)
    (hs : ContDiffOn ℝ 2 (fun θ => v z θ) (Set.Icc 0 (π / 2))) (h0 : v z 0 = 0)
    (h1 : v z (π / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero v z θ * v z θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => v z θ') θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (v z θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (v z θ) ^ 2) := by
  have hL : ∀ θ : ℝ,
      Work.Elliptic.Lzero v z θ = Work.Elliptic.Lzero (fun _ θ' => v z θ') 0 θ := by
    intro θ
    rw [Work.Elliptic.Lzero_eq_deriv, Work.Elliptic.Lzero_eq_deriv]
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  simp only [hL]
  exact Lzero_self_form_aux (fun θ => v z θ) hs h0 h1

end Work.FTS.EllipticEst
