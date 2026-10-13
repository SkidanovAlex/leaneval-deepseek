/-
Copyright: work module for the Elgindi finite-time singularity project.

# The derivative of the `I₄`-primitive and its vanishing at the angular endpoints

This module proves `I4_Gprim_deriv`: the primitive
`Gprim u θ = (1/2)·sin θ cos θ·σ(θ)·((u/cos)'(θ)² - (u/cos)(θ)²)` (with `σ θ = sin(2θ)^{-η}`)
has derivative `Hintegrand u θ` at every `θ ∈ (0, π/2)`, and tends to `0` at both endpoints of
the quadrant.  This is the fundamental-theorem-of-calculus input of the `I₄`-identity
`∫ Hintegrand u = 0`, hence of the paper's Step 2 lower bound for `I₄` (Elgindi, Annals 194 (3)
2021, tex 895–915).

Write `c = cos θ`, `s = sin θ`, `Ψ̄ = u / cos`, `a(θ) = s·c·σ(θ)`.  Since
`σ'(θ) = -2η cos 2θ sin(2θ)^{-(1+η)}` and `2 sin θ cos θ = sin 2θ`, the product rule gives
`a'(θ) = (1-η) cos 2θ·σ(θ)`; and the relation `u = c·Ψ̄` gives
`u'' = c·Ψ̄'' - 2s·Ψ̄' - c·Ψ̄`, so that with `A(θ) = ((1-η)/2)cos 2θ + 2 sin²θ`

  `G' = (1/2)a'((Ψ̄')² - Ψ̄²) + (1/2)a(2Ψ̄'Ψ̄'' - 2Ψ̄Ψ̄')
     = A(θ)(Ψ̄')²σ + s Ψ̄' u'' σ - ((1-η)/2)cos 2θ Ψ̄²σ`,

which is `Hintegrand u θ`.  The endpoint limits are read off from `|Ψ̄|, |Ψ̄'| ≤ C` and
`sin θ cos θ σ(θ) = (1/2) sin(2θ)^{1-η} → 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option linter.unusedSimpArgs false

/-! ## Elementary angular identities -/

/-- **The weight identity.**  On the open quadrant
`sin θ cos θ σ(θ) = (1/2) sin(2θ)^{1-η}`, the form in which the vanishing at the two
endpoints is visible (`1 - η = 1/100 > 0`). -/
private lemma sin_cos_sig_eq (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin θ * Real.cos θ * sig θ
      = (1 / 2) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hkey : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
      Real.rpow_add hx, Real.rpow_one]
  have hsc : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
    rw [Real.sin_two_mul]; ring
  simp only [sig]
  rw [hkey, hsc]
  ring

/-- The coefficient `A` of the `I₄`-identity, in the form in which the `cos 2θ` terms cancel:
`A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ`. -/
private lemma acoef_eq_cos_two_mul (θ : ℝ) :
    acoef θ = ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2 := by
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
  rw [acoef_eq, Real.cos_two_mul', hc]
  ring

/-- **The `σ`-derivative identity.**  `(cos²θ - sin²θ)σ(θ) + sin θ cos θ σ'(θ)
= (1-η) cos 2θ σ(θ)`, i.e. the derivative of `sin θ cos θ σ(θ)` in the shape needed below. -/
private lemma sig_deriv_identity (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
        + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ
      = (1 - Work.Spaces.eta) * Real.cos (2 * θ) * sig θ := by
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hcos2 : Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ) = Real.cos (2 * θ) := by
    rw [Real.cos_two_mul']; ring
  have hkey : 2 * Real.sin θ * Real.cos θ * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← Real.sin_two_mul θ]
  have hkey2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    rw [show -(Work.Spaces.eta) = 1 + (-(1 + Work.Spaces.eta)) by ring,
      Real.rpow_add hx, Real.rpow_one]
  have hrpow : Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ
      = -(Work.Spaces.eta) * Real.cos (2 * θ) * sig θ := by
    simp only [sigD_apply, sig]
    rw [show Real.sin θ * Real.cos θ
          * (-2 * Work.Spaces.eta * Real.cos (2 * θ)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        = -(Work.Spaces.eta) * Real.cos (2 * θ)
          * (2 * Real.sin θ * Real.cos θ
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) by ring,
      hkey.trans hkey2.symm]
  rw [hrpow, hcos2]
  ring

/-! ## The second derivative of `Ψ̄ = u / cos` -/

/-- **The chain rule for `u = cos θ · Ψ̄`.**  If `u` is `C²` at `θ` and `cos θ ≠ 0`, then
`u''(θ) = Ψ̄''(θ) cos θ - 2 Ψ̄'(θ) sin θ - Ψ̄(θ) cos θ`. -/
private lemma psi_second_deriv (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    deriv (deriv u) θ
      = deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ * Real.cos θ
        - 2 * deriv (fun t : ℝ => u t / Real.cos t) θ * Real.sin θ
        - (u θ / Real.cos θ) * Real.cos θ := by
  obtain ⟨s, hs_mem, hs_reg⟩ := hu.contDiffOn le_rfl (by simp)
  have hmem : interior s ∈ 𝓝 θ :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hs_mem)
  have hreg : ContDiffOn ℝ 2 u (interior s) := hs_reg.mono interior_subset
  have hdiff : ∀ t ∈ interior s, DifferentiableAt ℝ u t := fun t ht =>
    (hreg.differentiableOn (by simp)).differentiableAt (isOpen_interior.mem_nhds ht)
  have hcos_nhds : ∀ᶠ t in 𝓝 θ, Real.cos t ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hcos
  -- `u' = Ψ̄' cos - Ψ̄ sin`, as an eventual equality of functions
  have heq_deriv : deriv u =ᶠ[𝓝 θ]
      fun t : ℝ =>
        deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t - (u t / Real.cos t) * Real.sin t := by
    filter_upwards [hcos_nhds, hmem] with t ht hts
    have heqt : u =ᶠ[𝓝 t] fun s : ℝ => (u s / Real.cos s) * Real.cos s := by
      filter_upwards [Real.continuous_cos.continuousAt.eventually_ne ht] with s hs
      exact (div_mul_cancel₀ (u s) hs).symm
    have hd : deriv (fun s : ℝ => (u s / Real.cos s) * Real.cos s) t
        = deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
          + (u t / Real.cos t) * (-Real.sin t) := by
      have hVt : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) t :=
        (hdiff t hts).div Real.differentiableAt_cos ht
      have h3 : HasDerivAt (fun s : ℝ => (u s / Real.cos s) * Real.cos s)
          (deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
            + (u t / Real.cos t) * (-Real.sin t)) t :=
        hVt.hasDerivAt.mul (Real.hasDerivAt_cos t)
      exact h3.deriv
    rw [heqt.deriv_eq, hd]
    ring
  rw [heq_deriv.deriv_eq]
  -- the two factors of the explicit function are differentiable at `θ`
  have hVd : DifferentiableAt ℝ (fun s : ℝ => u s / Real.cos s) θ :=
    (hu.div (Real.contDiff_cos.contDiffAt) hcos).differentiableAt (by simp)
  have hDd : DifferentiableAt ℝ (deriv (fun s : ℝ => u s / Real.cos s)) θ :=
    ((hu.div (Real.contDiff_cos.contDiffAt) hcos).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by simp)
  have h1 : HasDerivAt
      (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t)
      (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
        + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ)) θ :=
    hDd.hasDerivAt.mul (Real.hasDerivAt_cos θ)
  have h2 : HasDerivAt (fun t : ℝ => (u t / Real.cos t) * Real.sin t)
      (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
        + (u θ / Real.cos θ) * Real.cos θ) θ :=
    hVd.hasDerivAt.mul (Real.hasDerivAt_sin θ)
  have h3 := h1.sub h2
  have h4 : deriv (fun t : ℝ => deriv (fun s : ℝ => u s / Real.cos s) t * Real.cos t
        - (u t / Real.cos t) * Real.sin t) θ
      = (deriv (deriv (fun s : ℝ => u s / Real.cos s)) θ * Real.cos θ
          + deriv (fun s : ℝ => u s / Real.cos s) θ * (-Real.sin θ))
        - (deriv (fun s : ℝ => u s / Real.cos s) θ * Real.sin θ
            + (u θ / Real.cos θ) * Real.cos θ) := h3.deriv
  rw [h4]
  ring

/-! ## The derivative of `σ` and the endpoint limits of the weight -/

/-- **The derivative of the angular weight.**  `σ'(θ) = sigD η θ` on the open quadrant,
where `sigD η θ = -2η cos 2θ sin(2θ)^{-(1+η)}`. -/
private lemma sig_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt sig (sigD Work.Spaces.eta θ) θ := by
  change HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta)))
    (-2 * Work.Spaces.eta * Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) θ
  have hx : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    exact h
  have h4 : HasDerivAt (fun t : ℝ => Real.sin (2 * t) ^ (-(Work.Spaces.eta)))
      ((Real.cos (2 * θ) * 2) * (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1)) θ :=
    h3.rpow_const (p := -(Work.Spaces.eta)) (Or.inl (ne_of_gt hx))
  have hexp : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta) - 1)
      = (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
    congr 1
    ring
  rw [hexp] at h4
  have hval : (Real.cos (2 * θ) * 2) * (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = -2 * Work.Spaces.eta * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by ring
  rw [hval] at h4
  exact h4

/-- **The endpoint vanishing of the weight.**  For any `g` bounded on the open quadrant,
`(1/2) sin θ cos θ σ(θ) g(θ) → 0` both as `θ → 0⁺` and as `θ → (π/2)⁻`. -/
private lemma weight_tendsto (g : ℝ → ℝ) (C : ℝ)
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |g θ| ≤ C) :
    Filter.Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => (1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have heta : 0 < 1 - Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _)
      (hg (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hweight : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
        = (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
    intro θ hθ
    rw [sin_cos_sig_eq θ hθ]
    ring
  have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(1 / 2) * (Real.sin θ * Real.cos θ * sig θ) * g θ‖
        ≤ (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
    intro θ hθ
    have hx : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hnn : 0 ≤ (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hx _)
    rw [hweight θ hθ, Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    calc (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * |g θ|
        ≤ (1 / 4) * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) * C :=
          mul_le_mul_of_nonneg_left (hg θ hθ) hnn
      _ = (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by ring
  have hcont : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hs0 : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := hcont.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have hspi : Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h := hcont.tendsto (Real.pi / 2)
    have h0 : Real.sin (2 * (Real.pi / 2)) = 0 := by
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : ∀ a : Filter ℝ, Filter.Tendsto (fun θ : ℝ => Real.sin (2 * θ)) a (nhds 0) →
      Filter.Tendsto (fun θ : ℝ => (1 / 4) * C * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta))
        a (nhds 0) := by
    intro a ha
    have h := ha.rpow tendsto_const_nhds (Or.inr heta)
    rw [Real.zero_rpow (ne_of_gt heta)] at h
    simpa using h.const_mul ((1 / 4) * C)
  have hmem0 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) := by
    have h2 : Set.Iio (Real.pi / 2) ∈ 𝓝[>] (0 : ℝ) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    exact Filter.inter_mem self_mem_nhdsWithin h2
  have hmempi : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝[<] (Real.pi / 2) := by
    have h1 : Set.Ioi (0 : ℝ) ∈ 𝓝[<] (Real.pi / 2) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    exact Filter.inter_mem h1 self_mem_nhdsWithin
  refine ⟨?_, ?_⟩
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) ?_ (hlim _ hs0))
    filter_upwards [hmem0] with θ hθ
    exact hbnd θ hθ
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _) ?_ (hlim _ hspi))
    filter_upwards [hmempi] with θ hθ
    exact hbnd θ hθ

/-- The primitive `Gprim u` (defined in `Submission.Work.FTS.EllipticEst.AngSecond.I4_aux_defs`
as `(1/2)·sin θ cos θ·σ(θ)·((u/cos)'(θ)² - (u/cos)(θ)²)`, with `σ(θ) = sin(2θ)^{-η}`) has
derivative `Hintegrand u θ` at every `θ ∈ (0, π/2)`, and tends to `0` at both endpoints `0` and
`π/2` from within the interval.

Route: write `c = cos θ`, `s = sin θ`, `Ψ̄ = u/c`, `a(θ) = s·c·σ(θ)`.  On `(0,π/2)`,
`a'(θ) = ((1-η)/2)·cos(2θ)·σ(θ)` (from `σ' = -η·2cos(2θ)·sin(2θ)^{-η-1}`), and
`G' = (a'/2)((Ψ̄')² - Ψ̄²) + a(Ψ̄'Ψ̄'' - Ψ̄Ψ̄')`.  The relation `u = c·Ψ̄` gives
`u'' = -c·Ψ̄ - 2s·Ψ̄' + c·Ψ̄''`, which turns the second term into
`s·Ψ̄'·u'' = scσ(Ψ̄'Ψ̄'' - Ψ̄Ψ̄') - 2s²σ(Ψ̄')²`, so that
`G' = Acoef(θ)(Ψ̄')²σ + s·Ψ̄'·u''·σ - ((1-η)/2)cos 2θ·Ψ̄²σ` with
`Acoef(θ) = ((1-η)/2)cos 2θ + 2 sin²θ`; this is `Hintegrand u θ`.  The endpoint limits follow
from `|Ψ̄|, |Ψ̄'| ≤ C` (the hypothesis `hbdd`) and `a(θ) → 0` at both endpoints. -/
theorem I4_Gprim_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hu1 : u (Real.pi / 2) = 0)
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |u θ / Real.cos θ| ≤ C ∧ |deriv (fun θ' => u θ' / Real.cos θ') θ| ≤ C) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Gprim u) (Hintegrand u θ) θ) ∧
      Filter.Tendsto (Gprim u) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (Gprim u) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the derivative on the open quadrant
    intro θ hθ
    have hθI : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have huAt : ContDiffAt ℝ 2 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
    have hVAt : ContDiffAt ℝ 2 (fun t : ℝ => u t / Real.cos t) θ :=
      huAt.div (Real.contDiff_cos.contDiffAt) hc
    have hVd : DifferentiableAt ℝ (fun t : ℝ => u t / Real.cos t) θ :=
      hVAt.differentiableAt (by simp)
    have hDd : DifferentiableAt ℝ (deriv (fun t : ℝ => u t / Real.cos t)) θ :=
      (hVAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by simp)
    have hdu := psi_second_deriv u huAt hc
    have hsig := sig_hasDerivAt hθ
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    have hA : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t * sig t)
        ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
          + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ) θ := by
      have h2 := ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).mul hsig
      convert h2 using 1 <;> ring
    have hF : HasDerivAt
        (fun y : ℝ => (deriv (fun t : ℝ => u t / Real.cos t) y) ^ 2 - (u y / Real.cos y) ^ 2)
        (2 * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
          - 2 * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ) θ := by
      have hp1 := hDd.hasDerivAt.pow 2
      have hp2 := hVd.hasDerivAt.pow 2
      convert hp1.sub hp2 using 1 <;> simp only [h21, pow_one] <;> ring
    have hA2 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * (Real.sin t * Real.cos t * sig t))
        ((1 / 2 : ℝ) * ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) * sig θ
          + Real.sin θ * Real.cos θ * sigD Work.Spaces.eta θ)) θ := by
      have h2 := hA.const_mul (1 / 2 : ℝ)
      convert h2 using 1 <;> ring
    have hprod := hA2.mul hF
    change HasDerivAt (fun t : ℝ => (1 / 2) * (Real.sin t * Real.cos t * sig t)
        * ((deriv (fun t' : ℝ => u t' / Real.cos t') t) ^ 2 - (u t / Real.cos t) ^ 2))
      (Hintegrand u θ) θ
    convert hprod using 1 <;> simp only [Hintegrand, sig_deriv_identity θ hθ, hdu,
      acoef_eq_cos_two_mul θ, h21, pow_one] <;> ring
  · -- vanishing at `θ → 0⁺`
    obtain ⟨C, hC0, hC⟩ := hbdd
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      obtain ⟨h1, h2⟩ := hC θ hθ
      obtain ⟨hu1', hu2'⟩ := abs_le.mp h1
      obtain ⟨hd1, hd2⟩ := abs_le.mp h2
      have h3 : (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]
      have h4 : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (u θ / Real.cos θ)]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg (u θ / Real.cos θ)],
        by nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]⟩
    obtain ⟨hw1, hw2⟩ :=
      weight_tendsto (fun θ => (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        - (u θ / Real.cos θ) ^ 2) (C ^ 2) hbnd
    have hGeq : Gprim u = fun θ : ℝ =>
        (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
          * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2) := by
      funext θ
      simp only [Gprim]
    rw [hGeq]
    exact hw1
  · -- vanishing at `θ → (π/2)⁻`
    obtain ⟨C, hC0, hC⟩ := hbdd
    have hbnd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2| ≤ C ^ 2 := by
      intro θ hθ
      obtain ⟨h1, h2⟩ := hC θ hθ
      obtain ⟨hu1', hu2'⟩ := abs_le.mp h1
      obtain ⟨hd1, hd2⟩ := abs_le.mp h2
      have h3 : (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]
      have h4 : (u θ / Real.cos θ) ^ 2 ≤ C ^ 2 := by
        nlinarith [sq_nonneg (u θ / Real.cos θ)]
      rw [abs_le]
      exact ⟨by nlinarith [sq_nonneg (u θ / Real.cos θ)],
        by nlinarith [sq_nonneg (deriv (fun t : ℝ => u t / Real.cos t) θ)]⟩
    obtain ⟨hw1, hw2⟩ :=
      weight_tendsto (fun θ => (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        - (u θ / Real.cos θ) ^ 2) (C ^ 2) hbnd
    have hGeq : Gprim u = fun θ : ℝ =>
        (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
          * ((deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2 - (u θ / Real.cos θ) ^ 2) := by
      funext θ
      simp only [Gprim]
    rw [hGeq]
    exact hw2

end Work.FTS.EllipticEst.AngSecond
