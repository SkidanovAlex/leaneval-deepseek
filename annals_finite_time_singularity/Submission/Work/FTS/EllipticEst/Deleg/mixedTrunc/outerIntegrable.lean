/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedTrunc/outerIntegrable`

The outer (`z`-)integrability of the four `(χ_n, ψ_δ)`-truncated angular energies of the
cut-off chain for `i1Paper_weakMixed`:

`z ↦ χ_n(z)·w(z)²·∫_θ σ(θ)·κ(θ)·(X(z,θ))²`

where the angular factor `κ` is supported in the compact interval `[δ/4, π/2 - δ/4] ⊂ (0, π/2)`
(`κ = ψ_δ` or `κ = ψ_δ''`), and `X` is one of `U = z∂_zu`, `V = z∂_z∂_θu`, or the mixed slot
`V - (1+η)U·cos(2θ)·sin(2θ)^{-1}`.

Everything is elementary but needs care: there is **no** hypothesis of decay of `u` at
`z = 0` or `z = ∞` — the *radial cut-off* `χ_n` is what makes the outer integral finite.  The
argument is:

* `χ_n` is supported in the compact set `[1/(n+1), 3(n+1)] ⊂ (0,∞)`;
* on the compact rectangle `[1/(n+1), 3(n+1)] × [δ/4, π/2 - δ/4]` (inside the open quadrant) the
  continuous angular integrand is bounded, and `χ_n·w²` is bounded as well;
* the θ-integrand vanishes off `[δ/4, π/2 - δ/4]`, so the θ-integral is bounded uniformly;
* this gives `IntegrableOn` on the compact interval, and off it the integrand is literally `0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.mixedTrunc.QuadBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg.mixedTrunc

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Elementary continuity facts -/

/-- `σ θ = sin(2θ)^{-η}` is continuous on the open angular interval `(0, π/2)`. -/
theorem oi_continuousOn_sigθ :
    ContinuousOn Work.FTS.EllipticEst.AeColl.sigθ (Set.Ioo 0 (Real.pi / 2)) := by
  have h : Work.FTS.EllipticEst.AeColl.sigθ
      = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := rfl
  rw [h]
  refine ContinuousOn.rpow_const ?_ ?_
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.mono
      (Set.subset_univ _)
  · intro θ hθ
    left
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2]))

/-- `w z ²` is continuous on the open half-line (the pole at `z = 0` is not met). -/
theorem oi_continuousOn_wt :
    ContinuousOn Work.FTS.EllipticEst.AeColl.wt (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ContinuousOn.pow ((continuous_const.add continuous_id).continuousOn) 2
    · exact ContinuousOn.pow (continuous_id.continuousOn) 2
    · intro z hz
      exact pow_ne_zero 2 (ne_of_gt hz)
  have h : Work.FTS.EllipticEst.AeColl.wt = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
  rw [h]
  exact ContinuousOn.pow hw 2

/-- `ψ_δ''` vanishes off the closed interval `[δ/4, π/2 - δ/4]`: `ψ_δ` is identically zero on a
whole *neighbourhood* of every point of the complement (no hypothesis on `δ` is needed). -/
theorem oi_psiD2_eq_zero_of_notMem (δ : ℝ) :
    ∀ θ : ℝ, θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) →
      deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 := by
  intro θ hθ
  have hpsi : ∀ θ' : ℝ, θ' ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) →
      Work.FTS.EllipticEst.AeColl.psiD δ θ' = 0 :=
    fun θ' h' => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ' h'
  -- `ψ_δ` vanishes on a whole neighbourhood of `θ` ...
  have hmem : Set.Iio (δ / 4) ∈ 𝓝 θ ∨ Set.Ioi (Real.pi / 2 - δ / 4) ∈ 𝓝 θ := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with h | h
    · exact Or.inl (isOpen_Iio.mem_nhds h)
    · exact Or.inr (isOpen_Ioi.mem_nhds h)
  -- ... hence so does its first derivative, and then its second derivative vanishes
  have h1 : deriv (Work.FTS.EllipticEst.AeColl.psiD δ) =ᶠ[𝓝 θ] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hmem with hmem | hmem
    · filter_upwards [hmem] with θ' hθ'
      have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ'] (fun _ : ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hθ') (fun θ'' hθ'' => hpsi θ'' (by
          rw [Set.mem_Icc, not_and_or, not_le, not_le]
          exact Or.inl hθ''))
      simpa using heq.deriv_eq
    · filter_upwards [hmem] with θ' hθ'
      have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ'] (fun _ : ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hθ') (fun θ'' hθ'' => hpsi θ'' (by
          rw [Set.mem_Icc, not_and_or, not_le, not_le]
          exact Or.inr hθ''))
      simpa using heq.deriv_eq
  calc deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = deriv (fun _ : ℝ => (0 : ℝ)) θ := h1.deriv_eq
    _ = 0 := by simp

/-! ## The general shape -/

/-- **The outer integrability of one truncated angular energy.**  For an angular factor `κ`
supported in `[δ/4, π/2 - δ/4]` and an angular `X` whose joint composite with `σ` and `κ` is
continuous on the open quadrant, the radial integral of `χ_n·w²·∫_θ σ κ X²` is finite. -/
theorem oi_shape (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2)
    (κ : ℝ → ℝ) (X : ℝ → ℝ → ℝ)
    (hκ : ∀ θ : ℝ, θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) → κ θ = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2 * κ p.2
      * (X p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Ioi 0) := by
  set a : ℝ := 1 / ((n : ℝ) + 1) with ha
  set b : ℝ := 3 * ((n : ℝ) + 1) with hb
  set c : ℝ := δ / 4 with hc
  set c' : ℝ := Real.pi / 2 - δ / 4 with hc'
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha_pos : 0 < a := by rw [ha]; positivity
  have hab : a < b := by
    rw [ha, hb, div_lt_iff₀ hn1]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    nlinarith [h1]
  have hc_pos : 0 < c := by rw [hc]; linarith
  have hc'_lt : c' < Real.pi / 2 := by rw [hc']; linarith
  have hcc' : c < c' := by rw [hc, hc']; linarith [hδ2, Real.pi_pos]
  have hIcc_sub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha_pos hz.1
  have hsub : Set.Icc c c' ⊆ Set.Ioo 0 (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_lt_of_le hc_pos hθ.1, lt_of_le_of_lt hθ.2 hc'_lt⟩
  have hRsub : (Set.Icc a b ×ˢ Set.Icc c c') ⊆
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun p hp => ⟨hIcc_sub hp.1, hsub hp.2⟩
  -- a uniform bound for the angular integrand on the compact rectangle
  obtain ⟨M₂, hM₂⟩ := ((isCompact_Icc (a := a) (b := b)).prod
    (isCompact_Icc (a := c) (b := c'))).exists_bound_of_continuousOn (hcont.mono hRsub)
  have hM₂nn : 0 ≤ M₂ := by
    have hmem : (a, c) ∈ Set.Icc a b ×ˢ Set.Icc c c' :=
      ⟨⟨le_rfl, le_of_lt hab⟩, ⟨le_rfl, le_of_lt hcc'⟩⟩
    exact le_trans (norm_nonneg _) (hM₂ (a, c) hmem)
  -- a uniform bound for `χ_n · w²`
  have hcutwt_cont : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z) (Set.Icc a b) :=
    ((Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn).mul
      (oi_continuousOn_wt.mono hIcc_sub)
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hcutwt_cont
  -- a.e. strong measurability
  have haesm0 : MeasureTheory.AEStronglyMeasurable (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ * (X z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    aesm_thetaIntegral_Ioi hcont measurableSet_Ioo (fun θ hθ =>
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (hcutwt_cont.aestronglyMeasurable measurableSet_Icc).mul
      (haesm0.mono_measure (MeasureTheory.Measure.restrict_mono hIcc_sub le_rfl))
  -- the inner `θ`-integral is uniformly bounded on the radial support
  have hinner_bound : ∀ z ∈ Set.Icc a b,
      ‖∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2‖
        ≤ M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2))) := by
    intro z hz
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const ?_ (fun θ hθ => ?_)
    · exact lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioo_subset_Icc_self)
        isCompact_Icc.measure_lt_top
    · by_cases h : θ ∈ Set.Icc c c'
      · exact hM₂ (z, θ) ⟨hz, h⟩
      · have h' : θ ∉ Set.Icc (δ / 4) (Real.pi / 2 - δ / 4) := by rwa [hc, hc'] at h
        rw [show Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ * (X z θ) ^ 2 = 0 by
          rw [hκ θ h', mul_zero, zero_mul]]
        simpa using hM₂nn
  -- the resulting bound for the full outer integrand
  have hf_bound : ∀ z ∈ Set.Icc a b,
      ‖Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
            * (X z θ) ^ 2)‖
        ≤ M₁ * (M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2)))) := by
    intro z hz
    refine le_trans (le_of_eq (norm_mul (Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z)
      (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
        * (X z θ) ^ 2))) ?_
    exact mul_le_mul (hM₁ z hz) (hinner_bound z hz) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hM₁ z hz))
  -- integrability on the compact radial support
  have h1 : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.of_bound
      (isCompact_Icc (a := a) (b := b)).measure_lt_top haesm
      (M₁ * (M₂ * (MeasureTheory.volume.real (Set.Ioo 0 (Real.pi / 2))))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    exact hf_bound z hz
  -- the integrand vanishes off the radial support
  have h2 : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AeColl.wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * κ θ
          * (X z θ) ^ 2)) (Set.Ioi 0 \ Set.Icc a b) := by
    refine MeasureTheory.IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      MeasureTheory.integrableOn_zero (fun z hz => ?_)
      (measurableSet_Ioi.diff measurableSet_Icc)
    have hz1 : z ∉ Set.Icc a b := hz.2
    have hzero : Work.FTS.EllipticEst.cut n z = 0 := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz1
      rcases hz1 with h | h
      · have h1 : z < 1 / ((n : ℝ) + 1) := by rwa [ha] at h
        exact Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_of_lt h1)
      · have h1 : 3 * ((n : ℝ) + 1) < z := by rwa [hb] at h
        exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n (le_of_lt h1)
    rw [hzero, zero_mul, zero_mul]
  refine (h1.union h2).mono_set (fun z hz => ?_)
  by_cases h : z ∈ Set.Icc a b
  · exact Or.inl h
  · exact Or.inr ⟨hz, h⟩

/-! ## The target -/

theorem outerIntegrable (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ)
    (hu : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.psiD δ θ
            * (Work.FTS.EllipticEst.AeColl.Vz u z θ
                - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
                  * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)) (Set.Ioi 0)
    ∧ MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
            * (Work.FTS.EllipticEst.AeColl.Uz u z θ) ^ 2)) (Set.Ioi 0) := by
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContinuousOn.comp oi_continuousOn_sigθ
      (ContinuousOn.mono (continuous_snd.continuousOn) (Set.subset_univ _))
      (fun p hp => hp.2)
  have hUz : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_Uz_quad hu
  have hVz : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := continuousOn_Vz_quad hu
  have hpsi : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.psiD δ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (((Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).continuous.comp
      continuous_snd).continuousOn).mono (Set.subset_univ _)
  have hd2 : Continuous (deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ))) := by
    have h1' : ContDiff ℝ 1 (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) := by
      simpa only [Nat.reduceAdd] using (Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).deriv'
    exact h1'.continuous_deriv_one
  have hd2c : ContinuousOn (fun p : ℝ × ℝ =>
      deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hd2.comp continuous_snd).continuousOn).mono (Set.subset_univ _)
  have hmixed : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2
      - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2) * Real.cos (2 * p.2)
      * (Real.sin (2 * p.2)) ^ (-(1 : ℝ))) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hcos : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (Set.subset_univ _)
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).mono
        (Set.subset_univ _)
    have hsinpow : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(1 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
        (by linarith [hp.2.1]) (by linarith [hp.2.2]))))
    exact hVz.sub (((hUz.const_mul (1 + Work.Spaces.eta)).mul hcos).mul hsinpow)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hUz.pow 2))
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Vz u z θ)
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hVz.pow 2))
  · exact oi_shape n δ hδ hδ2 (Work.FTS.EllipticEst.AeColl.psiD δ)
      (fun z θ => Work.FTS.EllipticEst.AeColl.Vz u z θ
        - (1 + Work.Spaces.eta) * (Work.FTS.EllipticEst.AeColl.Uz u z θ) * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 : ℝ)))
      (fun θ hθ => Work.FTS.EllipticEst.AeColl.psiD_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hpsi).mul (hmixed.pow 2))
  · exact oi_shape n δ hδ hδ2 (deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)))
      (fun z θ => Work.FTS.EllipticEst.AeColl.Uz u z θ)
      (fun θ hθ => oi_psiD2_eq_zero_of_notMem δ θ hθ)
      ((hsig.mul hd2c).mul (hUz.pow 2))

end Work.FTS.EllipticEst.Deleg.mixedTrunc
