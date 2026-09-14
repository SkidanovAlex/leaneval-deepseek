import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Commons.Analysis.Calculus.duBoisReymond_scalar

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter Function
open scoped Topology

/-- The interval integral of `⟪g ·, w⟫` equals `⟪∫ g, w⟫`. -/
private lemma intervalIntegral_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    {g : ℝ → F} {w : F} {a t : ℝ} (h : IntervalIntegrable g volume a t) :
    (∫ s in a..t, inner ℝ (g s) w) = inner ℝ (∫ s in a..t, g s) w := by
  have hc := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ w) h
  have h1 : (fun x => innerSL ℝ w (g x)) = (fun x => inner ℝ (g x) w) := by
    ext x; rw [innerSL_apply_apply, real_inner_comm]
  have h2 : innerSL ℝ w (∫ x in a..t, g x) = inner ℝ (∫ x in a..t, g x) w := by
    rw [innerSL_apply_apply, real_inner_comm]
  rw [h1, h2] at hc
  exact hc

/-- `t ↦ ⟪f t, w⟫` is locally integrable whenever `f` is. -/
private lemma locallyIntegrableOn_inner_const {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : ℝ → F} {s : Set ℝ} {w : F}
    (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn (fun t => inner ℝ (f t) w) s volume := by
  have h2 : LocallyIntegrableOn ((innerSL ℝ w) ∘ f) s volume :=
    (innerSL ℝ w).locallyIntegrableOn_comp hf
  refine h2.congr (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, innerSL_apply_apply]
  rw [real_inner_comm]

/-- The primitive of a function continuous on `[a,b]` is locally integrable on `(a,b)`. -/
private lemma locallyIntegrableOn_intervalIntegral_primitive {v : ℝ → ℝ} {a b : ℝ}
    (hv : ContinuousOn v (Set.Icc a b)) :
    LocallyIntegrableOn (fun t => ∫ s in a..t, v s) (Set.Ioo a b) volume := by
  have hvu : ContinuousOn v (Set.Ioo a b) := hv.mono Ioo_subset_Icc_self
  have hFderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t => ∫ s in a..t, v s) (v x) x := by
    intro x hx
    have hii : IntervalIntegrable v volume a x := by
      have hcont : ContinuousOn v (Set.uIcc a x) := by
        rw [Set.uIcc_of_le hx.1.le]
        exact hv.mono (Set.Icc_subset_Icc_right hx.2.le)
      exact hcont.intervalIntegrable
    have hsm : StronglyMeasurableAtFilter v (𝓝 x) volume :=
      (hvu.stronglyMeasurableAtFilter isOpen_Ioo) x hx
    have hctx : ContinuousAt v x := hv.continuousAt (Icc_mem_nhds hx.1 hx.2)
    exact intervalIntegral.integral_hasDerivAt_right hii hsm hctx
  have hFdiff : DifferentiableOn ℝ (fun t => ∫ s in a..t, v s) (Set.Ioo a b) :=
    fun x hx => (hFderiv x hx).differentiableAt.differentiableWithinAt
  exact hFdiff.continuousOn.locallyIntegrableOn measurableSet_Ioo

/-- Integration by parts: for a smooth compactly supported `ψ` and a function `v` continuous on
`[a,b]`, `∫ ψ' · (∫_a^· v) = - ∫ ψ · v`. -/
private lemma integral_deriv_mul_intervalIntegral_primitive {ψ v : ℝ → ℝ} {a b : ℝ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ Set.Ioo a b) (hv : ContinuousOn v (Set.Icc a b)) :
    ∫ t, deriv ψ t * (∫ s in a..t, v s) = - ∫ t, ψ t * v t := by
  have hFderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t => ∫ s in a..t, v s) (v x) x := by
    intro x hx
    have hvu : ContinuousOn v (Set.Ioo a b) := hv.mono Ioo_subset_Icc_self
    have hii : IntervalIntegrable v volume a x := by
      have hcont : ContinuousOn v (Set.uIcc a x) := by
        rw [Set.uIcc_of_le hx.1.le]
        exact hv.mono (Set.Icc_subset_Icc_right hx.2.le)
      exact hcont.intervalIntegrable
    have hsm : StronglyMeasurableAtFilter v (𝓝 x) volume :=
      (hvu.stronglyMeasurableAtFilter isOpen_Ioo) x hx
    have hctx : ContinuousAt v x := hv.continuousAt (Icc_mem_nhds hx.1 hx.2)
    exact intervalIntegral.integral_hasDerivAt_right hii hsm hctx
  have hFli : LocallyIntegrableOn (fun t => ∫ s in a..t, v s) (Set.Ioo a b) volume :=
    locallyIntegrableOn_intervalIntegral_primitive hv
  have hvli : LocallyIntegrableOn v (Set.Ioo a b) volume :=
    (hv.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hψcont : Continuous ψ := hψ.continuous
  have hdψcont : Continuous (deriv ψ) := hψ.continuous_deriv (by decide)
  have hdψcs : HasCompactSupport (deriv ψ) := hψcs.deriv
  have hdψts : tsupport (deriv ψ) ⊆ Set.Ioo a b := tsupport_deriv_subset.trans hts
  have hint1 : Integrable (ψ * v) volume := by
    have h := integrable_smul_of_locallyIntegrableOn_of_tsupport_subset (f := v) (g := ψ)
      hvli hψcont hψcs hts
    have heq : (fun x => ψ x • v x) = ψ * v := by ext x; rw [Pi.mul_apply, smul_eq_mul]
    rwa [heq] at h
  have hint2 : Integrable ((fun t => deriv ψ t) * (fun t => ∫ s in a..t, v s)) volume := by
    have h := integrable_smul_of_locallyIntegrableOn_of_tsupport_subset
      (f := fun t => ∫ s in a..t, v s) (g := deriv ψ) hFli hdψcont hdψcs hdψts
    have heq : (fun x => deriv ψ x • (∫ s in a..x, v s))
        = (fun t => deriv ψ t) * (fun t => ∫ s in a..t, v s) := by
      ext x; rw [Pi.mul_apply, smul_eq_mul]
    rwa [heq] at h
  have hint3 : Integrable (ψ * (fun t => ∫ s in a..t, v s)) volume := by
    have h := integrable_smul_of_locallyIntegrableOn_of_tsupport_subset
      (f := fun t => ∫ s in a..t, v s) (g := ψ) hFli hψcont hψcs hts
    have heq : (fun x => ψ x • (∫ s in a..x, v s))
        = ψ * (fun t => ∫ s in a..t, v s) := by
      ext x; rw [Pi.mul_apply, smul_eq_mul]
    rwa [heq] at h
  have hu : ∀ x ∈ tsupport (fun t => ∫ s in a..t, v s), HasDerivAt ψ (deriv ψ x) x :=
    fun x _ => (hψ.differentiable (by decide) x).hasDerivAt
  have hv' : ∀ x ∈ tsupport ψ, HasDerivAt (fun t => ∫ s in a..t, v s) (v x) x :=
    fun x hx => hFderiv x (hts hx)
  have hmain := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ψ)
    (v := fun t => ∫ s in a..t, v s) (u' := deriv ψ) (v' := v) hu hv' hint1 hint2 hint3
  linarith [hmain]

theorem ae_eq_add_intervalIntegral_of_forall_integral_inner_deriv_add_eq_zero_smooth {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {f g : ℝ → F} {a b : ℝ} (hab : a < b)
    (hf : MeasureTheory.LocallyIntegrableOn f (Set.Ioo a b) MeasureTheory.volume)
    (hg : ContinuousOn g (Set.Icc a b))
    (h : ∀ (ψ : ℝ → ℝ) (w : F), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b →
      MeasureTheory.integral MeasureTheory.volume (fun t => deriv ψ t * inner ℝ (f t) w)
        + MeasureTheory.integral MeasureTheory.volume (fun t => ψ t * inner ℝ (g t) w) = 0) :
    ∃ c : F, f =ᵐ[MeasureTheory.volume.restrict (Set.Ioo a b)]
      (fun t => c + ∫ s in a..t, g s) := by
  classical
  -- Step 1: for every `w`, the scalar function `t ↦ ⟪f t, w⟫ - ∫_a^t ⟪g s, w⟫` is a.e. constant
  -- on `(a,b)` (du Bois-Reymond for the distributional equality `(⟪f,w⟫)' = ⟪g,w⟫`).
  have key : ∀ w : F, ∃ c : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b →
      inner ℝ (f t) w - (∫ s in a..t, inner ℝ (g s) w) = c := by
    intro w
    have hvcont : ContinuousOn (fun s => inner ℝ (g s) w) (Set.Icc a b) :=
      hg.inner continuousOn_const
    have hfli : LocallyIntegrableOn (fun t => inner ℝ (f t) w) (Set.Ioo a b) volume :=
      locallyIntegrableOn_inner_const hf
    have hUli : LocallyIntegrableOn
        (fun t => inner ℝ (f t) w - (∫ s in a..t, inner ℝ (g s) w))
        (Set.Ioo a b) volume :=
      hfli.sub (locallyIntegrableOn_intervalIntegral_primitive hvcont)
    refine duBoisReymond_scalar hab hUli ?_
    intro ψ hψ hψcs hts
    have hdψcont : Continuous (deriv ψ) := hψ.continuous_deriv (by decide)
    have hdψcs : HasCompactSupport (deriv ψ) := hψcs.deriv
    have hdψts : tsupport (deriv ψ) ⊆ Set.Ioo a b := tsupport_deriv_subset.trans hts
    have hint1 : Integrable (fun t => deriv ψ t * inner ℝ (f t) w) volume := by
      have h := integrable_smul_of_locallyIntegrableOn_of_tsupport_subset
        (f := fun t => inner ℝ (f t) w) (g := deriv ψ) hfli hdψcont hdψcs hdψts
      have heq : (fun x => deriv ψ x • inner ℝ (f x) w)
          = (fun t => deriv ψ t * inner ℝ (f t) w) := by
        ext x; rw [smul_eq_mul]
      rwa [heq] at h
    have hint2 : Integrable (fun t => deriv ψ t * (∫ s in a..t, inner ℝ (g s) w)) volume := by
      have h := integrable_smul_of_locallyIntegrableOn_of_tsupport_subset
        (f := fun t => ∫ s in a..t, inner ℝ (g s) w) (g := deriv ψ)
        (locallyIntegrableOn_intervalIntegral_primitive hvcont) hdψcont hdψcs hdψts
      have heq : (fun x => deriv ψ x • (∫ s in a..x, inner ℝ (g s) w))
          = (fun t => deriv ψ t * (∫ s in a..t, inner ℝ (g s) w)) := by
        ext x; rw [smul_eq_mul]
      rwa [heq] at h
    have hsplit : (∫ t, deriv ψ t * (inner ℝ (f t) w - (∫ s in a..t, inner ℝ (g s) w)))
        = (∫ t, deriv ψ t * inner ℝ (f t) w)
          - ∫ t, deriv ψ t * (∫ s in a..t, inner ℝ (g s) w) := by
      rw [show (fun t => deriv ψ t * (inner ℝ (f t) w - (∫ s in a..t, inner ℝ (g s) w)))
          = (fun t => deriv ψ t * inner ℝ (f t) w
              - deriv ψ t * (∫ s in a..t, inner ℝ (g s) w)) from by ext t; ring]
      rw [integral_sub hint1 hint2]
    rw [hsplit]
    have hh := h ψ w hψ hψcs hts
    have hibp := integral_deriv_mul_intervalIntegral_primitive hψ hψcs hts hvcont
    linarith [hh, hibp]
  choose c hc using key
  -- Step 2: reconstruct the constant vector from its coordinates on an orthonormal basis.
  let e := stdOrthonormalBasis ℝ F
  refine ⟨∑ i, c (e i) • e i, ?_⟩
  change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ioo a b),
    f t = (∑ i, c (e i) • e i) + ∫ s in a..t, g s
  rw [ae_restrict_iff' measurableSet_Ioo]
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ i, (t ∈ Set.Ioo a b →
      inner ℝ (f t - (∫ s in a..t, g s)) (e i) = c (e i)) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [hc (e i)] with t ht htI
    have hii : IntervalIntegrable g volume a t := by
      have hcont : ContinuousOn g (Set.uIcc a t) := by
        rw [Set.uIcc_of_le htI.1.le]
        exact hg.mono (Set.Icc_subset_Icc_right htI.2.le)
      exact hcont.intervalIntegrable
    have hcomp := intervalIntegral_inner_eq (g := g) (w := e i) hii
    rw [inner_sub_left, ← hcomp]
    exact ht htI
  filter_upwards [hall] with t ht htI
  have hgoal : f t - (∫ s in a..t, g s) = ∑ i, c (e i) • e i := by
    rw [← e.sum_repr' (f t - (∫ s in a..t, g s))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci : inner ℝ (e i) (f t - (∫ s in a..t, g s)) = c (e i) := by
      rw [real_inner_comm]; exact ht i htI
    rw [hci]
  rw [← hgoal, sub_add_cancel]

end Commons.Analysis.Calculus