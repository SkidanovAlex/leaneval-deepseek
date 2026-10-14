import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.Prop.Ang2.Sig2
import Submission.Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts.sigTruncId
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.SolutionDelivery.DatumOdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `truncRadialIbpSig` — the `σ`-weighted truncated radial integration by parts

The `σ`-weighted (`σ = sEta θ = sin(2θ)^{-η}`) version of the radial integration by parts of
the elliptic equation, for a compactly supported `C²` weight `ω` on `(0,∞)`:

`∫_z ω z (∫_θ σ θ ((α²z²∂_z²u + α(5+α)z∂_zu)·u))
   = -α² ∫_z ω z (∫_θ σ θ (z∂_zu)²)
     + (α²/2) ∫_z (z²ω)'' z (∫_θ σ θ u²)
     - (α(5+α)/2) ∫_z (zω)' z (∫_θ σ θ u²)`,

together with the integrability of the left-hand integrand.

## Route

For every `θ ∈ (0,π/2)` the slice `Φ_θ := fun z => u z θ` is `C²` on `(0,∞)`, so the
one-dimensional identity `Work.FTS.EllipticEst.Honest.zIBP_compact` applies to `Φ_θ`
(it proves all the integrability and boundary vanishing internally from the support of `ω`).
Multiplying by `σ θ` and integrating in `θ` — the endpoints `θ = 0, π/2` are null, where
`σ` vanishes — then swapping the double integrals (`MeasureTheory.integral_integral_swap`)
gives the claim.  The joint integrability consumed by the swaps is supplied by the
`Dispatch` toolkit (`integrable_sigma_pair_of_HkIntegrable`,
`integrable_sigma_sq_of_HkIntegrable`) from the three `ℋ⁰`-memberships `hgrad`, `hrad2`,
`hu` and the coefficient bound `ω ≤ w²`; the two coefficients `(z²ω)''` and `(zω)'` are
bounded by a multiple of `w²` because they are `C⁰` on `(0,∞)` and vanish off the compact
`[a,b]`, where `w² ≥ 1`.
-/

namespace Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The radial pairing of the statement -/

/-- The radial pairing `(α²z²∂_z²u + α(5+α)z∂_zu)·u` of the statement. -/
private abbrev sigA (α : ℝ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
    + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ

/-! ## Vanishing of the two coefficients off the support of `ω` -/

private lemma deriv_mul_eq_zero_off (om : ℝ → ℝ) {a b : ℝ}
    (hom : ∀ z, z ∉ Set.Icc a b → om z = 0) :
    ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y * om y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y * om y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      rw [hom y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)]
      ring
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
      rw [hom y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)]
      ring
  rw [hev.deriv_eq]; simp

private lemma deriv_sq_mul_eq_zero_off (om : ℝ → ℝ) {a b : ℝ}
    (hom : ∀ z, z ∉ Set.Icc a b → om z = 0) :
    ∀ z, z ∉ Set.Icc a b → deriv (fun y : ℝ => y ^ 2 * om y) z = 0 := by
  intro z hz
  have hev : (fun y : ℝ => y ^ 2 * om y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      rw [hom y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)]
      ring
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
      rw [hom y (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)]
      ring
  rw [hev.deriv_eq]; simp

private lemma deriv_deriv_sq_mul_eq_zero_off (om : ℝ → ℝ) {a b : ℝ}
    (hom : ∀ z, z ∉ Set.Icc a b → om z = 0) :
    ∀ z, z ∉ Set.Icc a b → deriv (deriv (fun y : ℝ => y ^ 2 * om y)) z = 0 := by
  intro z hz
  have hz' : z < a ∨ b < z := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hz
  have hev : deriv (fun y : ℝ => y ^ 2 * om y) =ᶠ[𝓝 z] (fun _ : ℝ => (0 : ℝ)) := by
    rcases hz' with hlt | hgt
    · filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      exact deriv_sq_mul_eq_zero_off om hom y
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)
    · filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
      exact deriv_sq_mul_eq_zero_off om hom y
        (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)
  rw [hev.deriv_eq]; simp

/-! ## The two coefficient bounds `|(zω)'| ≤ C w²`, `|(z²ω)''| ≤ C w²` -/

private lemma exists_abs_deriv_mul_le (om : ℝ → ℝ) (hωd : ContDiffOn ℝ 2 om (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hom : ∀ z, z ∉ Set.Icc a b → om z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |deriv (fun y : ℝ => y * om y) z| ≤ C * (Work.Spaces.w z) ^ 2 := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have h2 : ContDiffOn ℝ 2 (fun y : ℝ => y * om y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have h1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y * om y)) (Set.Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcont : ContinuousOn (fun z : ℝ => deriv (fun y : ℝ => y * om y) z) (Set.Icc a b) :=
    h1.continuousOn.mono hsub
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  by_cases hzab : z ∈ Set.Icc a b
  · have h1' : |deriv (fun y : ℝ => y * om y) z| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM z hzab
    have hw : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 :=
      one_le_pow₀ (Work.FTS.EllipticEst.Dispatch.one_le_w_D hz)
    calc |deriv (fun y : ℝ => y * om y) z| ≤ M := h1'
      _ ≤ max M 0 := le_max_left _ _
      _ = max M 0 * 1 := (mul_one _).symm
      _ ≤ max M 0 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hw (le_max_right _ _)
  · rw [deriv_mul_eq_zero_off om hom z hzab, abs_zero]
    exact mul_nonneg (le_max_right _ _) (sq_nonneg _)

private lemma exists_abs_deriv_deriv_sq_mul_le (om : ℝ → ℝ) (hωd : ContDiffOn ℝ 2 om (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hom : ∀ z, z ∉ Set.Icc a b → om z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z →
      |deriv (deriv (fun y : ℝ => y ^ 2 * om y)) z| ≤ C * (Work.Spaces.w z) ^ 2 := by
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have h2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * om y) (Set.Ioi 0) :=
    ContDiffOn.mul (by fun_prop) hωd
  have h1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * om y)) (Set.Ioi 0) :=
    h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h0 : ContDiffOn ℝ 0 (deriv (deriv (fun y : ℝ => y ^ 2 * om y))) (Set.Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi le_rfl
  have hcont : ContinuousOn (fun z : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * om y)) z)
      (Set.Icc a b) := h0.continuousOn.mono hsub
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  by_cases hzab : z ∈ Set.Icc a b
  · have h1' : |deriv (deriv (fun y : ℝ => y ^ 2 * om y)) z| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM z hzab
    have hw : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 :=
      one_le_pow₀ (Work.FTS.EllipticEst.Dispatch.one_le_w_D hz)
    calc |deriv (deriv (fun y : ℝ => y ^ 2 * om y)) z| ≤ M := h1'
      _ ≤ max M 0 := le_max_left _ _
      _ = max M 0 * 1 := (mul_one _).symm
      _ ≤ max M 0 * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hw (le_max_right _ _)
  · rw [deriv_deriv_sq_mul_eq_zero_off om hom z hzab, abs_zero]
    exact mul_nonneg (le_max_right _ _) (sq_nonneg _)

/-! ## Generic helpers: Fubini for the two orders, and linearity in `θ` -/

private lemma integral_integral_swap_fts {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F) Work.FTS.EllipticEst.Dispatch.nuFts) :
    (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ), F z θ :=
  MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) (f := F) hF

private lemma integral_integral_swap_fts_symm {F : ℝ → ℝ → ℝ}
    (hF : MeasureTheory.Integrable (Function.uncurry F) Work.FTS.EllipticEst.Dispatch.nuFts) :
    (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ), F z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, F z θ :=
  (MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) (f := F) hF).symm

private lemma integral_slice_lin {μ : MeasureTheory.Measure ℝ} {σ A B C : ℝ → ℝ} {a b c : ℝ}
    (hA : MeasureTheory.Integrable (fun θ => σ θ * A θ) μ)
    (hB : MeasureTheory.Integrable (fun θ => σ θ * B θ) μ)
    (hC : MeasureTheory.Integrable (fun θ => σ θ * C θ) μ) :
    (∫ θ, σ θ * (a * A θ + b * B θ - c * C θ) ∂μ)
      = a * (∫ θ, σ θ * A θ ∂μ) + b * (∫ θ, σ θ * B θ ∂μ)
        - c * (∫ θ, σ θ * C θ ∂μ) := by
  have hAB : MeasureTheory.Integrable
      (fun θ => a * (σ θ * A θ) + b * (σ θ * B θ)) μ :=
    (hA.const_mul a).add (hB.const_mul b)
  rw [show (fun θ => σ θ * (a * A θ + b * B θ - c * C θ))
      = fun θ => a * (σ θ * A θ) + b * (σ θ * B θ) - c * (σ θ * C θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_sub hAB (hC.const_mul c),
    MeasureTheory.integral_add (hA.const_mul a) (hB.const_mul b),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-! ## The theorem -/

theorem truncRadialIbpSig (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (ω : ℝ → ℝ) (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hωsupp : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωnn : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2) :
    (MeasureTheory.IntegrableOn (fun z => ω z * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ))) (Set.Ioi 0))
    ∧ (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  -- ## 0. smoothness and `ℋ⁰`-memberships
  have hU : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hU2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_zsq hU
  have hUg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz u) := hU.Dz
  have hIu : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hU hu
  have hIg : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz u) p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hUg hgrad
  have hIa : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) p.1 p.2)
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.integrable_HkIntegrand_of_smoothOpen hU2 hrad2
  -- ## 1. the weight bounds and the a.e. measurabilities
  have hωbnd : ∀ z, 0 < z → |ω z| ≤ 1 * (Work.Spaces.w z) ^ 2 := by
    intro z _
    rw [abs_of_nonneg (hωnn z), one_mul]
    exact hωle z
  have hωcont : ContinuousOn (fun p : ℝ × ℝ => ω p.1) Work.FTS.EllipticEst.Q0 :=
    hωd.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hA2cont : ContinuousOn
      (fun p : ℝ × ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) p.1)
      Work.FTS.EllipticEst.Q0 := by
    have h2 : ContDiffOn ℝ 2 (fun y : ℝ => y ^ 2 * ω y) (Set.Ioi 0) :=
      ContDiffOn.mul (by fun_prop) hωd
    have h1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y ^ 2 * ω y)) (Set.Ioi 0) :=
      h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have h0 : ContDiffOn ℝ 0 (deriv (deriv (fun y : ℝ => y ^ 2 * ω y))) (Set.Ioi 0) :=
      h1.deriv_of_isOpen isOpen_Ioi le_rfl
    exact h0.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hA1cont : ContinuousOn
      (fun p : ℝ × ℝ => deriv (fun y : ℝ => y * ω y) p.1) Work.FTS.EllipticEst.Q0 := by
    have h2 : ContDiffOn ℝ 2 (fun y : ℝ => y * ω y) (Set.Ioi 0) :=
      ContDiffOn.mul (by fun_prop) hωd
    have h1 : ContDiffOn ℝ 1 (deriv (fun y : ℝ => y * ω y)) (Set.Ioi 0) :=
      h2.deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact h1.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  -- ## 2. joint integrability of the four integrands
  have hJ1 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
        ((α ^ 2 * p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2
          + (α * (5 + α) * p.1) * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    have h1 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
          ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)))
        Work.FTS.EllipticEst.Dispatch.nuFts :=
      Work.FTS.EllipticEst.Dispatch.integrable_sigma_pair_of_HkIntegrable
        (α := α) (C := 1) (A := ω) (f := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        (g := u) zero_le_one hωbnd
        (Work.FTS.EllipticEst.Dispatch.aesm_sigma_pair hωcont hU2.continuousOn hU.continuousOn)
        hIa hIu
    have h2 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
          ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2)))
        Work.FTS.EllipticEst.Dispatch.nuFts :=
      Work.FTS.EllipticEst.Dispatch.integrable_sigma_pair_of_HkIntegrable
        (α := α) (C := 1) (A := ω) (f := fun z θ => z * Work.Spaces.pz u z θ)
        (g := u) zero_le_one hωbnd
        (Work.FTS.EllipticEst.Dispatch.aesm_sigma_pair hωcont hUg.continuousOn hU.continuousOn)
        hIg hIu
    have hsum : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => α ^ 2 * (ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
            ((p.1 ^ 2 * Work.Spaces.pzIter 2 u p.1 p.2) * u p.1 p.2)))
          + (α * (5 + α)) * (ω p.1 * (Work.FTS.EllipticEst.sEta p.2 *
            ((p.1 * Work.Spaces.pz u p.1 p.2) * u p.1 p.2))))
        Work.FTS.EllipticEst.Dispatch.nuFts :=
      (h1.const_mul (α ^ 2)).add (h2.const_mul (α * (5 + α)))
    refine hsum.congr (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨z, θ⟩ := p
    simp only
    ring
  have hJ2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
        (ω p.1 * (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts :=
    Work.FTS.EllipticEst.Dispatch.integrable_sigma_sq_of_HkIntegrable
      (α := α) (C := 1) (A := ω) (f := fun z θ => z * Work.Spaces.pz u z θ)
      zero_le_one hωbnd
      (Work.FTS.EllipticEst.Dispatch.aesm_sigma_sq hωcont hUg.continuousOn) hIg
  have hJ3 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
        (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    obtain ⟨C2, hC2nn, hC2⟩ := exists_abs_deriv_deriv_sq_mul_le ω hωd ha hωsupp
    exact Work.FTS.EllipticEst.Dispatch.integrable_sigma_sq_of_HkIntegrable
      (α := α) (C := C2) (A := fun z => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z)
      (f := u) hC2nn hC2
      (Work.FTS.EllipticEst.Dispatch.aesm_sigma_sq hA2cont hU.continuousOn) hIu
  have hJ4 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
        (deriv (fun y : ℝ => y * ω y) p.1 * (u p.1 p.2) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := by
    obtain ⟨C1, hC1nn, hC1⟩ := exists_abs_deriv_mul_le ω hωd ha hωsupp
    exact Work.FTS.EllipticEst.Dispatch.integrable_sigma_sq_of_HkIntegrable
      (α := α) (C := C1) (A := fun z => deriv (fun y : ℝ => y * ω y) z)
      (f := u) hC1nn hC1
      (Work.FTS.EllipticEst.Dispatch.aesm_sigma_sq hA1cont hU.continuousOn) hIu
  have hJ1u : MeasureTheory.Integrable
      (Function.uncurry fun z θ => ω z * (Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
      Work.FTS.EllipticEst.Dispatch.nuFts := hJ1
  have hJ2u : MeasureTheory.Integrable
      (Function.uncurry fun z θ => Work.FTS.EllipticEst.sEta θ *
        (ω z * (z * Work.Spaces.pz u z θ) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := hJ2
  have hJ3u : MeasureTheory.Integrable
      (Function.uncurry fun z θ => Work.FTS.EllipticEst.sEta θ *
        (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := hJ3
  have hJ4u : MeasureTheory.Integrable
      (Function.uncurry fun z θ => Work.FTS.EllipticEst.sEta θ *
        (deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2))
      Work.FTS.EllipticEst.Dispatch.nuFts := hJ4
  refine ⟨?_, ?_⟩
  · -- ## the integrability of the left-hand integrand
    change MeasureTheory.IntegrableOn (fun z => ω z * (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.sEta θ * sigA α u z θ)) (Set.Ioi 0)
    refine hJ1.integral_prod_left.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [MeasureTheory.integral_const_mul]
  · -- ## the identity
    change (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
      = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
    -- ## Step 1: pull `ω z` inside the angular integral and swap the two integrations
    have step1 : (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
            ω z * (Work.FTS.EllipticEst.sEta θ * sigA α u z θ) := by
      rw [show (∫ z in Set.Ioi (0 : ℝ), ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
          = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
              ω z * (Work.FTS.EllipticEst.sEta θ * sigA α u z θ) from by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
        rw [MeasureTheory.integral_const_mul]]
      exact integral_integral_swap_fts hJ1u
    -- ## Step 2: pull `σ θ` outside the radial integral
    have step2 : (∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
          ω z * (Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (∫ z in Set.Ioi (0 : ℝ), ω z * sigA α u z θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only []
      rw [show (fun z : ℝ => ω z * (Work.FTS.EllipticEst.sEta θ * sigA α u z θ))
          = fun z : ℝ => Work.FTS.EllipticEst.sEta θ * (ω z * sigA α u z θ) from by
        funext z; ring]
      rw [MeasureTheory.integral_const_mul]
    -- ## Step 3: the slicewise one-dimensional identity, a.e. in `θ`
    have hper : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.FTS.EllipticEst.sEta θ * (∫ z in Set.Ioi (0 : ℝ), ω z * sigA α u z θ)
          = Work.FTS.EllipticEst.sEta θ *
            (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2)
              + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
                  deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2)
              - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
                  deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2)) := by
      have haeIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ae_mem_Ioo_of_mem_Icc
      filter_upwards [haeIoo] with θ hθ
      have hslice : ContDiffOn ℝ 2 (fun z : ℝ => u z θ) (Set.Ioi 0) :=
        Work.FTS.EllipticEst.AngAWeak.contDiffOn_slice_z hsm hθ 2
      have hkey := Work.FTS.EllipticEst.Honest.zIBP_compact α ω (fun z : ℝ => u z θ)
        ha hab hωsupp hωd hslice
      have hbridge : (∫ z in Set.Ioi (0 : ℝ), ω z * sigA α u z θ)
          = ∫ z in Set.Ioi (0 : ℝ), ω z * (α ^ 2 * z ^ 2 *
                deriv (deriv (fun z : ℝ => u z θ)) z
              + (α * (5 + α) * z) * deriv (fun z : ℝ => u z θ) z)
              * (fun z : ℝ => u z θ) z := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
        simp only [sigA, Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
        ring
      rw [hbridge, hkey]
      first | rfl | (simp only [Work.Spaces.pz]; ring)
    have step3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
          (∫ z in Set.Ioi (0 : ℝ), ω z * sigA α u z θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (-α ^ 2 * (∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2)
              + (α ^ 2 / 2) * (∫ z in Set.Ioi (0 : ℝ),
                  deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2)
              - (α * (5 + α) / 2) * (∫ z in Set.Ioi (0 : ℝ),
                  deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2)) :=
      MeasureTheory.integral_congr_ae hper
    -- ## Step 4: linearity in `θ`
    have intQ : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ *
        (∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine hJ2.integral_prod_right.congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only []
      rw [MeasureTheory.integral_const_mul]
    have intR2 : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ *
        (∫ z in Set.Ioi (0 : ℝ),
          deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine hJ3.integral_prod_right.congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only []
      rw [MeasureTheory.integral_const_mul]
    have intR1 : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ *
        (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine hJ4.integral_prod_right.congr (Filter.Eventually.of_forall fun θ => ?_)
      simp only []
      rw [MeasureTheory.integral_const_mul]
    have hlin := integral_slice_lin
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (σ := Work.FTS.EllipticEst.sEta)
      (A := fun θ => ∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2)
      (B := fun θ => ∫ z in Set.Ioi (0 : ℝ),
        deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2)
      (C := fun θ => ∫ z in Set.Ioi (0 : ℝ),
        deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2)
      (a := -α ^ 2) (b := α ^ 2 / 2) (c := α * (5 + α) / 2) intQ intR2 intR1
    -- ## Step 5: the three weighted Fubini identities
    have fQ : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
          (∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2))
        = ∫ z in Set.Ioi (0 : ℝ), ω z *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2) := by
      rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (∫ z in Set.Ioi (0 : ℝ), ω z * (z * Work.Spaces.pz u z θ) ^ 2))
          = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
              Work.FTS.EllipticEst.sEta θ * (ω z * (z * Work.Spaces.pz u z θ) ^ 2) from by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only []
        rw [MeasureTheory.integral_const_mul]]
      rw [integral_integral_swap_fts_symm hJ2u]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [show (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ *
            (ω z * (z * Work.Spaces.pz u z θ) ^ 2))
          = fun θ : ℝ => ω z *
              (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2) from by
        funext θ; ring]
      rw [MeasureTheory.integral_const_mul]
    have fR2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
          (∫ z in Set.Ioi (0 : ℝ),
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2))
        = ∫ z in Set.Ioi (0 : ℝ), deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
      rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (∫ z in Set.Ioi (0 : ℝ),
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2))
          = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
              Work.FTS.EllipticEst.sEta θ *
                (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2) from by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only []
        rw [MeasureTheory.integral_const_mul]]
      rw [integral_integral_swap_fts_symm hJ3u]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [show (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ *
            (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * (u z θ) ^ 2))
          = fun θ : ℝ => deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) from by
        funext θ; ring]
      rw [MeasureTheory.integral_const_mul]
    have fR1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
          (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2))
        = ∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
      rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (∫ z in Set.Ioi (0 : ℝ), deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2))
          = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioi (0 : ℝ),
              Work.FTS.EllipticEst.sEta θ *
                (deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2) from by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        simp only []
        rw [MeasureTheory.integral_const_mul]]
      rw [integral_integral_swap_fts_symm hJ4u]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [show (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ *
            (deriv (fun y : ℝ => y * ω y) z * (u z θ) ^ 2))
          = fun θ : ℝ => deriv (fun y : ℝ => y * ω y) z *
              (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) from by
        funext θ; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [step1, step2, step3, hlin, fQ, fR2, fR1]

end

end Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts
