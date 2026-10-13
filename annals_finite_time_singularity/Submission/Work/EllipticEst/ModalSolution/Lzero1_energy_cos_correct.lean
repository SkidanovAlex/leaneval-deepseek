/-
Copyright: work module for the Elgindi finite-time singularity project.

# The cos-weighted energy identity for the angular operator `Lzero1`

`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` is formally self-adjoint for the weight `cos θ`,
and its associated quadratic form is

  `∫_{Iθ} (Lzero1 v) · v · cos θ = ∫_{Iθ} (v')² cos θ + ∫_{Iθ} (v/cos θ)² cos θ
      - 6 ∫_{Iθ} v² cos θ`

for a `C²` function on `[0, π/2]` vanishing at both endpoints.  (The middle coefficient is
`1`, not `1/2`; the sibling statement with `1/2` is refuted in
`Submission/Work/EllipticEst/ModalSolution/Lzero1_energy_cos_refute.lean`.)

The proof is a one-line integration by parts.  On `(0, π/2)` the exact pointwise identity

  `(Lzero1 v) · v · cos θ = (v')² cos θ + (v/cos θ)² cos θ - 6 v² cos θ
      + ((-v v' cos θ))'`

holds (see `hasDerivAt_primitive` below).  Its primitive `-v v' cos θ` vanishes at `θ = 0`
and `θ = π/2` because `v 0 = v (π/2) = 0`, so by the fundamental theorem of calculus the
last term integrates to `0`; splitting the remaining integral with the four integrability
hypotheses gives the claim.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

/-- The pointwise form of the cos-weighted self-pairing of `Lzero1`: on the open interval
the difference between `(Lzero1 v)·v·cos θ` and the quadratic form
`(v')² cos θ + (v/cos θ)² cos θ - 6 v² cos θ` is the derivative of the primitive
`θ ↦ -v θ · v' θ · cos θ` (whose endpoints values vanish when `v 0 = v (π/2) = 0`). -/
private theorem hasDerivAt_primitive {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t => -(v t * deriv v t * Real.cos t))
      (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
        - (deriv v θ) ^ 2 * Real.cos θ
        - (v θ / Real.cos θ) ^ 2 * Real.cos θ
        + 6 * (v θ ^ 2 * Real.cos θ)) θ := by
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hθ.1]
    · exact hθ.2
  have hmem : Set.Icc 0 (Real.pi / 2) ∈ 𝓝 θ := Icc_mem_nhds hθ.1 hθ.2
  have hdv : HasDerivAt v (deriv v θ) θ :=
    ((hv.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hUicc : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc (by positivity)
  have hg1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hUicc (by norm_num)
  have hg : HasDerivAt (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (deriv (derivWithin v (Set.Icc 0 (Real.pi / 2))) θ) θ :=
    ((hg1.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hev : (deriv v) =ᶠ[𝓝 θ] (derivWithin v (Set.Icc 0 (Real.pi / 2))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm
  have hddv : HasDerivAt (deriv v) (deriv (deriv v) θ) θ := by
    have h := hg.congr_of_eventuallyEq hev
    rwa [h.deriv]
  have htan : HasDerivAt (fun t => Real.tan t * v t)
      (1 / Real.cos θ ^ 2 * v θ + Real.tan θ * deriv v θ) θ :=
    (Real.hasDerivAt_tan hcos).mul hdv
  have hprod : HasDerivAt (fun t => -(v t * deriv v t * Real.cos t))
      (-((deriv v θ * deriv v θ + v θ * deriv (deriv v) θ) * Real.cos θ
          + (v θ * deriv v θ) * (-Real.sin θ))) θ :=
    ((hdv.mul hddv).mul (Real.hasDerivAt_cos θ)).neg
  refine hprod.congr_deriv ?_
  have htan_d := htan.deriv
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [show deriv (fun t => deriv v t) θ = deriv (deriv v) θ from rfl, htan_d]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem Lzero1_energy_cos_correct (v : ℝ → ℝ) (hv : ContDiffOn ℝ 2 v (Set.Icc 0 (Real.pi / 2)))
    (h0 : v 0 = 0) (h1 : v (Real.pi / 2) = 0)
    (hL : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ) Work.Spaces.Iθ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv v θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (v θ / Real.cos θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    (hC : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ)
        + (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ)
        - 6 * ∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  -- the primitive `F` and the integrand `g` of the pointwise identity
  set F : ℝ → ℝ := fun t => -(v t * deriv v t * Real.cos t) with hF
  set g : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
      - (deriv v θ) ^ 2 * Real.cos θ
      - (v θ / Real.cos θ) ^ 2 * Real.cos θ
      + 6 * (v θ ^ 2 * Real.cos θ) with hg
  -- `F` is continuous on `[0, π/2]`: on the interior because `v` and `v'` are, at the
  -- endpoints because `v` vanishes there (`F = -v · (derivWithin v Icc) · cos` on all
  -- of `Icc`, a product of functions continuous on `Icc`).
  have hU : UniqueDiffOn ℝ (Set.Icc 0 (Real.pi / 2)) := uniqueDiffOn_Icc hlt
  have hg1 : ContDiffOn ℝ 1 (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hv.derivWithin hU (by norm_num)
  have hdvW : ContinuousOn (derivWithin v (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) := hg1.continuousOn
  have hWcont : ContinuousOn
      (fun t => -(v t * derivWithin v (Set.Icc 0 (Real.pi / 2)) t * Real.cos t))
      (Set.Icc 0 (Real.pi / 2)) :=
    (((hv.continuousOn.mul hdvW).mul Real.continuous_cos.continuousOn)).neg
  have hFcont : ContinuousOn F (Set.Icc 0 (Real.pi / 2)) := by
    refine hWcont.congr (fun t ht => ?_)
    simp only [hF]
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, h0]; simp
    · rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2, h1]; simp
      · rw [derivWithin_of_mem_nhds (Icc_mem_nhds h h2)]
  -- and its derivative is `g` on the interior
  have hderiv : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt F (g x) x := by
    intro x hx
    simpa only [hF, hg] using hasDerivAt_primitive hv hx
  have h6int : IntegrableOn (fun θ => (6 : ℝ) * (v θ ^ 2 * Real.cos θ)) Work.Spaces.Iθ :=
    hC.const_mul (6 : ℝ)
  have hgint : IntegrableOn g Work.Spaces.Iθ :=
    ((hL.sub hA).sub hB).add h6int
  have hint : IntervalIntegrable g volume (0 : ℝ) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
      (by simpa [Work.Spaces.Iθ] using hgint)
  -- fundamental theorem of calculus: the primitive vanishes at both endpoints
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), g θ) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hFcont hderiv hint]
    simp [hF, h0, h1]
  have hIθ_g : (∫ θ in Work.Spaces.Iθ, g θ) = 0 := by
    rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, hFTC]
  -- rewrite the integral of `g` in the split form used below
  have hIθ : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ)
          + 6 * (v θ ^ 2 * Real.cos θ)) = 0 := by
    simpa only [hg, Pi.add_apply, Pi.sub_apply] using hIθ_g
  -- split the integral of the sum of the four terms
  have e1 : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ)
          + 6 * (v θ ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ))
        + (∫ θ in Work.Spaces.Iθ, 6 * (v θ ^ 2 * Real.cos θ)) :=
    MeasureTheory.integral_add ((hL.sub hA).sub hB) h6int
  have e2 : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ - (v θ / Real.cos θ) ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ))
        - (∫ θ in Work.Spaces.Iθ, (v θ / Real.cos θ) ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_sub (hL.sub hA) hB
  have e3 : (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ
            - (deriv v θ) ^ 2 * Real.cos θ))
      = (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 v θ * v θ * Real.cos θ)
        - (∫ θ in Work.Spaces.Iθ, (deriv v θ) ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_sub hL hA
  have e4 : (∫ θ in Work.Spaces.Iθ, 6 * (v θ ^ 2 * Real.cos θ))
      = 6 * (∫ θ in Work.Spaces.Iθ, v θ ^ 2 * Real.cos θ) :=
    MeasureTheory.integral_const_mul 6 (fun θ => v θ ^ 2 * Real.cos θ)
  linarith [hIθ, e1, e2, e3, e4]

end Work.EllipticEst.ModalSolution
