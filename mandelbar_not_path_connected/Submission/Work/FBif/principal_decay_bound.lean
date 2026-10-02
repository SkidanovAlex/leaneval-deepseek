import Mathlib
import Submission.Work.MRMT.Found.M
import Submission.Work.MRMT.Found.mollify_admissible
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.inverse_limit
import Submission.Work.MRMT.Found.records_agree_pd
import Submission.Work.MRMT.Found.sqrt_volume_closedBall
import Submission.Work.FBif.exists_moll_spec
import Submission.Work.FBif.qc_decay_uniform
import Submission.Work.FBif.tendsto_principal_of_approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

noncomputable section

/-! ## The chosen decay constant -/

/-- **The far-field decay constant.**  For a coefficient of `L∞` bound `k` whose support is
contained in the closed ball of radius `M`, the Cauchy-transform estimate
`‖C ω z‖ ≤ 2‖ω‖₁/(π‖z‖)` together with `‖ω‖₁ ≤ E √(area)`, `E = k √(area)/(1-k)` gives the
far-field bound with the constant `2 k (area)/(π (1-k))`, which is `rcCd k M`. -/
noncomputable def rcCd (k M : ℝ) : ℝ :=
  2 * (k * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / (1 - k))
    * Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) / Real.pi

lemma rcCd_nonneg {k M : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) : 0 ≤ rcCd k M := by
  rw [rcCd]
  have h1 : 0 < 1 - k := by linarith
  have hs : 0 ≤ Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal) := Real.sqrt_nonneg _
  positivity

/-- `rcCd k M ≤ 4 k M²` for `k ≤ 1/2`: the area of the disc is `π M²`, so the constant is
`2kM²/(1-k)`, and `1 - k ≥ 1/2`. -/
lemma rcCd_le {k M : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 2) : rcCd k M ≤ 4 * k * M ^ 2 := by
  rw [rcCd]
  by_cases hM : 0 ≤ M
  · have hV := Work.MRMT.Found.sqrt_volume_closedBall M hM
    have hs : Real.sqrt ((volume (Metric.closedBall (0 : ℂ) M)).toReal)
        = Real.sqrt Real.pi * M := by
      rw [hV, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hM]
    rw [hs]
    have h1k : (0:ℝ) < 1 - k := by linarith
    have h1kn : (1:ℝ) - k ≠ 0 := ne_of_gt h1k
    have hstep : 2 * (k * (Real.sqrt Real.pi * M) / (1 - k))
          * (Real.sqrt Real.pi * M) / Real.pi = 2 * k * M ^ 2 / (1 - k) := by
      have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      field_simp
      ring_nf
      rw [hsq]
      ring
    rw [hstep]
    rw [div_le_iff₀ h1k]
    nlinarith [mul_nonneg hk0 (sq_nonneg M), sq_nonneg M, hk0, hk1]
  · rw [not_le] at hM
    have hzero : volume (Metric.closedBall (0 : ℂ) M) = 0 := by
      rw [Metric.closedBall_eq_empty.mpr hM, measure_empty]
    rw [hzero]
    simp only [ENNReal.toReal_zero, Real.sqrt_zero, mul_zero, zero_div]
    positivity

/-! ## The far-field bound for a family of approximating coefficients -/

/-- **The far-field normalisation of the principal solution, quantitatively.**  If `μ` is
admissible with `‖μ‖ ≤ k` a.e. and if `μn` is a family of smooth compactly supported
coefficients with `‖μn‖ ≤ k`, supported in the closed ball of radius `M`, converging to `μ`
almost everywhere, then the principal solution of `μ` satisfies
`‖principal μ z - z‖ ≤ rcCd k M / ‖z‖` for `‖z‖ ≥ max (2 M) 1`. -/
theorem principal_decay_of_approx {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {k M : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M)
    (hμb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    {μn : ℕ → ℂ → ℂ}
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnS : ∀ n, HasCompactSupport (μn n))
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hμnT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) :
    ∀ z : ℂ, max (2 * M) 1 ≤ ‖z‖ →
      ‖Work.MRMT.Found.principal μ z - z‖ ≤ rcCd k M / ‖z‖ := by
  classical
  choose F hFC hFCS hFB hFD using fun n =>
    Work.MRMT.Found.exists_contDiff_principal_of_contDiff (hμnC n) (hμnS n) hk1 (hμnB n)
  have hFdec : ∀ n z, max (2 * M) 1 ≤ ‖z‖ → ‖F n z - z‖ ≤ rcCd k M / ‖z‖ := by
    intro n z hz
    simpa only [rcCd] using
      qc_decay_uniform hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hFC hFB hFD n z hz
  have hconv : TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ))
      (Work.MRMT.Found.principal μ : ℂ → ℂ) Filter.atTop :=
    tendsto_principal_of_approx hμ hk0 hk1 hM0 hμb hμnC hμnS hμnB hμnSp hμnT hFC hFCS hFB hFD
  intro z hz
  have hpt : Filter.Tendsto (fun n => (F n : ℂ → ℂ) z) Filter.atTop
      (nhds (Work.MRMT.Found.principal μ z)) :=
    hconv.tendsto_comp (Work.MRMT.Found.principal μ).continuous.continuousAt tendsto_const_nhds
  have hlim : Filter.Tendsto (fun n => ‖(F n : ℂ → ℂ) z - z‖) Filter.atTop
      (nhds ‖Work.MRMT.Found.principal μ z - z‖) :=
    (continuous_norm.tendsto _).comp (hpt.sub tendsto_const_nhds)
  exact le_of_tendsto hlim (Eventually.of_forall fun n => hFdec n z hz)

/-- **The quantitative far-field normalisation of the principal solution.**  If `μ` is admissible,
supported in `ball 0 R` and bounded by `k ≤ 1/2` a.e., then the principal solution satisfies
`‖principal μ z - z‖ ≤ C/‖z‖` for `‖z‖ ≥ max (2(R+1)) 1`, with an explicit constant
`C ≤ 4 k (R+1)²`; in particular `C → 0` as `k → 0` for fixed `R`.

This is the quantitative part of MRMT `M1`.  With `h` the `L²` solution of `h = μ(1 + Sh)`, the
principal solution is `z + C h`, the `L²` norm of `h` is at most `k √π (R+1)/(1-k)`, and the
far-field decay of the Cauchy transform of a compactly supported `L²` function is
`‖C ω z‖ ≤ ‖ω‖₁/(π (‖z‖ - M))` with `M = R+1`; this gives the stated bound.  The same argument
sits inside `Work.MRMT.Found.qc_approx_decay_uniform`, but that module cannot be imported
(it, `record_modulus_uniform` and `modulus_of_records` form a build cycle), so the bound has to
be re-derived here from the non-cyclic pieces.  Concretely the three non-cyclic pieces live in
the sibling modules `Submission/Work/FBif/exists_moll_spec.lean`,
`…/qc_decay_uniform.lean` and `…/tendsto_principal_of_approx.lean`. -/
theorem principal_decay_bound {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {R k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1 / 2)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 4 * k * (R + 1) ^ 2 ∧
      ∀ z : ℂ, max (2 * (R + 1)) 1 ≤ ‖z‖ →
        ‖Work.MRMT.Found.principal μ z - z‖ ≤ C / ‖z‖ := by
  have hk1' : k < 1 := by linarith
  by_cases hR : 0 ≤ R
  · -- ## The non-degenerate case: `μ` is supported in a genuine disc of radius `R`.
    obtain ⟨μn, hμnC, hμnS, hμnB, hμnSp, hμnT⟩ :=
      exists_moll_spec hk0 hk1' hR (Work.MRMT.Found.mollify_admissible_locallyIntegrable hμ)
        hb hsupp
    refine ⟨rcCd k (R + 1), rcCd_nonneg hk0 hk1', rcCd_le hk0 hk1, fun z hz => ?_⟩
    exact principal_decay_of_approx hμ hk0 hk1' (by linarith) hb hμnC hμnS hμnB hμnSp hμnT z hz
  · -- ## The degenerate case `R < 0`: the support condition forces `μ = 0`.
    rw [not_le] at hR
    have hzero : ∀ z : ℂ, μ z = 0 := by
      intro z
      by_contra hz
      have hmem : z ∈ Function.support μ := Function.mem_support.mpr hz
      have hb' := hsupp hmem
      rw [Metric.mem_closedBall, dist_zero_right] at hb'
      linarith [norm_nonneg z]
    -- the constant family `μn = 0` is an admissible approximation of `μ`
    have hcs0 : HasCompactSupport (fun _ : ℂ => (0 : ℂ)) := by
      have hsub : Function.support (fun _ : ℂ => (0 : ℂ)) ⊆ Metric.closedBall 0 0 := by
        intro z hz
        simp at hz
      have hbdd : Bornology.IsBounded (Function.support (fun _ : ℂ => (0 : ℂ))) :=
        Metric.isBounded_closedBall.subset hsub
      simpa [HasCompactSupport, tsupport] using hbdd.isCompact_closure
    have hdec : ∀ z : ℂ, max (2 * (0:ℝ)) 1 ≤ ‖z‖ →
        ‖Work.MRMT.Found.principal μ z - z‖ ≤ rcCd 0 0 / ‖z‖ :=
      principal_decay_of_approx hμ (k := 0) (M := 0) le_rfl one_pos le_rfl
        (μn := fun _ _ => (0 : ℂ))
        (by filter_upwards with z; rw [hzero z]; simp)
        (fun _ => contDiff_const)
        (fun _ => hcs0)
        (fun _ _ => by simp)
        (fun _ z hz => absurd rfl hz)
        (by filter_upwards with z; rw [hzero z]; exact tendsto_const_nhds)
    refine ⟨4 * k * (R + 1) ^ 2, by positivity, le_rfl, fun z hz => ?_⟩
    have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (le_max_right _ _) hz
    have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le zero_lt_one hz1
    have h := hdec z (by simpa using hz1)
    have hrc : rcCd 0 0 = 0 := by simp [rcCd]
    rw [hrc, zero_div] at h
    exact le_trans h (div_nonneg (by positivity) hz0.le)

end

end Work.FBif
