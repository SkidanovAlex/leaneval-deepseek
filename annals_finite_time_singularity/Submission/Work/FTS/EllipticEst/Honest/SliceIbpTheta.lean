/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slice integration by parts of the elliptic estimates

`Work.FTS.EllipticEst.Honest.SliceIbpTheta`: for `η ∈ [0,1)` and `f` of class `C²` on the
closed angular interval `[0, π/2]` with `f 0 = f (π/2) = 0`,

  `∫_θ f f'' sin(2θ)^{-η} = -∫_θ (f')² sin(2θ)^{-η} + 2η ∫_θ f² sin(2θ)^{-η}
      + 2η(1+η) ∫_θ f² cos²(2θ) sin(2θ)^{-(2+η)}`,

an identity obtained by two integrations by parts against the singular weight
`σ θ = sin(2θ)^{-η}` (`σ` is integrable at both endpoints precisely because `η < 1`).

Route.  Write `σ = sig η`, `σ' = -2η cos(2θ) sin(2θ)^{-η-1}` and
`ρ θ = cos(2θ) sin(2θ)^{-η-1}` (so `σ' = -2η ρ`).

* First integration by parts: `G = σ f f'` has
  `G' = σ (f')² + σ f f'' + σ' f f'` and `G → 0` at `0⁺` and `(π/2)⁻`; the fundamental
  theorem of calculus on the *open* interval (with the two one-sided limits) gives
  `∫ σ (f')² + ∫ σ f f'' + ∫ σ' f f' = 0`.
* Second integration by parts (`∫ ρ f f' = -(1/2) ∫ ρ' f²`, again with vanishing boundary
  terms) turns `∫ σ' f f'` into `η ∫ ρ' f²`, and
  `ρ' = -2 σ - 2(η+1) cos²(2θ) sin(2θ)^{-(2+η)}`.

The two integration by parts are `integral_Ioo_eq_sub_of_tendsto` and
`integral_Ioo_mul_deriv_eq_neg_half` of `Honest.SliceSetup`.  The auxiliary inputs are:

* `Honest.SliceBounds` -- `|f θ| ≤ C θ`, `|f θ| ≤ C (π/2 - θ)`, `|f'| ≤ C`, `|f''| ≤ C` on
  `(0, π/2)`;
* `Honest.SliceIntegrable` -- integrability of the seven integrands occurring above;
* `Honest.SliceBoundary` -- the vanishing of the two pairs of boundary terms;
* `Honest.SliceWeightDeriv` -- the derivatives of `σ` and `ρ`.

The weight objects `Iθo`, `sig`, `sigD`, `rho`, `rhoD` are defined in `Honest.SliceIbpDefs`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.SliceBounds
import Submission.Work.FTS.EllipticEst.Honest.SliceWeightDeriv
import Submission.Work.FTS.EllipticEst.Honest.SliceIntegrable
import Submission.Work.FTS.EllipticEst.Honest.SliceBoundary

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- The `θ`-slice integration by parts behind Elgindi's elliptic estimates. -/
theorem SliceIbpTheta (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
      (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
        = - (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * η * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * η * (1 + η) * (∫ θ in Work.Spaces.Iθ,
              f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
  intro f hf h0 hπ
  -- ===== Step 0: replace the integrals over `Iθ = Icc 0 (π/2)` by integrals over `Iθo`. =====
  have hIcc : ∀ g : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in Iθo, g θ := by
    intro g
    simp only [Work.Spaces.Iθ, Iθo]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hIcc (fun θ => f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η)),
    hIcc (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
    hIcc (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)),
    hIcc (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))]
  -- ===== Step 1: the four ingredients obtained from the auxiliary lemmas. =====
  have hBounds : ∃ C : ℝ, 0 ≤ C ∧
      (∀ θ ∈ Iθo, |f θ| ≤ C * θ) ∧
      (∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Iθo, |deriv f θ| ≤ C) ∧
      (∀ θ ∈ Iθo, |deriv (deriv f) θ| ≤ C) :=
    SliceBounds f hf h0 hπ
  obtain ⟨C, hC0, hb1, hb2, hb3, hb4⟩ := hBounds
  have hIntegrable :
      IntegrableOn (fun θ => sig η θ * (deriv f θ) ^ 2) Iθo ∧
      IntegrableOn (fun θ => sig η θ * (f θ * deriv (deriv f) θ)) Iθo ∧
      IntegrableOn (fun θ => sigD η θ * (f θ * deriv f θ)) Iθo ∧
      IntegrableOn (fun θ => rho η θ * f θ * deriv f θ) Iθo ∧
      IntegrableOn (fun θ => rhoD η θ * f θ ^ 2) Iθo ∧
      IntegrableOn (fun θ => f θ ^ 2 * sig η θ) Iθo ∧
      IntegrableOn (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
        Iθo :=
    SliceIntegrable f η C hf h0 hπ hη0 hη1 hC0 hb1 hb2 hb3 hb4
  obtain ⟨hIA, hIB, hIC, hIrho, hIrhoD, hIsq, hIcos⟩ := hIntegrable
  have hBoundary :
      Tendsto (fun θ => sig η θ * f θ * deriv f θ) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ => sig η θ * f θ * deriv f θ)
        (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) ∧
      Tendsto (fun θ => rho η θ * f θ ^ 2) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ => rho η θ * f θ ^ 2)
        (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) :=
    SliceBoundary f η C hη0 hη1 hC0 hb1 hb2 hb3
  obtain ⟨hbd0, hbdπ, hbrho0, hbrhoπ⟩ := hBoundary
  have hSigRhoDeriv :
      (∀ θ ∈ Iθo, HasDerivAt (sig η) (sigD η θ) θ) ∧
      (∀ θ ∈ Iθo, HasDerivAt (rho η) (rhoD η θ) θ) :=
    SliceWeightDeriv η
  obtain ⟨hsig_d, hrho_d⟩ := hSigRhoDeriv
  -- ===== Step 2: derivative facts for `f`. =====
  have hmemIcc : ∀ θ ∈ Iθo, Set.Icc (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := by
    intro θ hθ
    refine mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hθ) ?_
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hdf : ∀ θ ∈ Iθo, HasDerivAt f (deriv f θ) θ := by
    intro θ hθ
    exact ((hf.contDiffAt (hmemIcc θ hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Iθo, HasDerivAt (deriv f) (deriv (deriv f) θ) θ := by
    intro θ hθ
    have hmono : ContDiffOn ℝ 2 f Iθo :=
      hf.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    have h1 : ContDiffOn ℝ 1 (deriv f) Iθo := hmono.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((h1.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hθ)).differentiableAt (by norm_num)).hasDerivAt
  -- ===== Step 3: the first integration by parts, through `G = σ f f'`. =====
  have hderivG : ∀ θ ∈ Iθo,
      HasDerivAt (fun θ => sig η θ * f θ * deriv f θ)
        (sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ)
          + sigD η θ * (f θ * deriv f θ)) θ := by
    intro θ hθ
    have h := ((hsig_d θ hθ).mul (hdf θ hθ)).mul (hddf θ hθ)
    have hfun : (sig η * f * deriv f) = fun θ => sig η θ * f θ * deriv f θ := by
      funext x; simp only [Pi.mul_apply]
    rw [hfun] at h
    have hval : (sigD η θ * f θ + sig η θ * deriv f θ) * deriv f θ
        + (sig η * f) θ * deriv (deriv f) θ
        = sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ)
          + sigD η θ * (f θ * deriv f θ) := by
      simp only [Pi.mul_apply]
      ring
    rw [hval] at h
    exact h
  have hintG : IntegrableOn
      (fun θ => sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ)
        + sigD η θ * (f θ * deriv f θ)) Iθo := by
    have h1 : IntegrableOn (fun θ => sig η θ * (deriv f θ) ^ 2
        + sig η θ * (f θ * deriv (deriv f) θ)) Iθo := hIA.add hIB
    exact h1.add hIC
  have hFTC := integral_Ioo_eq_sub_of_tendsto (a := 0) (b := Real.pi / 2) (m := 0) (l := 0)
    (by linarith [Real.pi_pos]) hderivG hintG hbd0 hbdπ
  have hGzero : (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ)
      + sigD η θ * (f θ * deriv f θ)) = 0 := by
    have h := hFTC
    simp only [sub_self] at h
    simpa only [Iθo] using h
  have hABC : (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2)
      + (∫ θ in Iθo, sig η θ * (f θ * deriv (deriv f) θ))
      + (∫ θ in Iθo, sigD η θ * (f θ * deriv f θ)) = 0 := by
    have h1 : IntegrableOn (fun θ => sig η θ * (deriv f θ) ^ 2
        + sig η θ * (f θ * deriv (deriv f) θ)) Iθo := hIA.add hIB
    have hsplit : (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ)
        + sigD η θ * (f θ * deriv f θ))
        = (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ))
          + (∫ θ in Iθo, sigD η θ * (f θ * deriv f θ)) := integral_add h1 hIC
    have hsplit2 : (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2 + sig η θ * (f θ * deriv (deriv f) θ))
        = (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2)
          + (∫ θ in Iθo, sig η θ * (f θ * deriv (deriv f) θ)) := integral_add hIA hIB
    linarith [hGzero, hsplit, hsplit2]
  -- ===== Step 4: the second integration by parts, against `ρ`. =====
  have hIBPrho : (∫ θ in Iθo, rho η θ * f θ * deriv f θ)
      = -(1 / 2) * (∫ θ in Iθo, rhoD η θ * f θ ^ 2) :=
    integral_Ioo_mul_deriv_eq_neg_half (a := 0) (b := Real.pi / 2) (by linarith [Real.pi_pos])
      (ρ := rho η) (ρ' := rhoD η) (f := f) (f' := deriv f) hrho_d hdf hIrhoD hIrho hbrho0 hbrhoπ
  have hICrho : (∫ θ in Iθo, sigD η θ * (f θ * deriv f θ))
      = -2 * η * (∫ θ in Iθo, rho η θ * f θ * deriv f θ) := by
    rw [← integral_const_mul (-2 * η) (fun θ => rho η θ * f θ * deriv f θ)]
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro θ hθ
    show sigD η θ * (f θ * deriv f θ) = -2 * η * (rho η θ * f θ * deriv f θ)
    rw [sigD_eq_neg_two_mul_rho]
    ring
  have hRhoDSplit : (∫ θ in Iθo, rhoD η θ * f θ ^ 2)
      = -2 * (∫ θ in Iθo, f θ ^ 2 * sig η θ)
        - 2 * (η + 1) * (∫ θ in Iθo,
            f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
    have h1 : IntegrableOn (fun θ => (-2 : ℝ) * (f θ ^ 2 * sig η θ)) Iθo :=
      hIsq.const_mul (-2)
    have h2 : IntegrableOn (fun θ => (-2 * (η + 1)) *
        (f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))) Iθo :=
      hIcos.const_mul (-2 * (η + 1))
    have he : (∫ θ in Iθo, rhoD η θ * f θ ^ 2)
        = ∫ θ in Iθo, (-2 : ℝ) * (f θ ^ 2 * sig η θ)
            + (-2 * (η + 1)) * (f θ ^ 2 * (Real.cos (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro θ hθ
      simp only [rhoD, sig]
      ring
    rw [he, integral_add h1 h2, integral_const_mul (-2) (fun θ => f θ ^ 2 * sig η θ),
      integral_const_mul (-2 * (η + 1))
        (fun θ => f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))]
    ring
  -- ===== Step 5: the algebra. =====
  have hBmain : (∫ θ in Iθo, sig η θ * (f θ * deriv (deriv f) θ))
      = - (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2)
        + 2 * η * (∫ θ in Iθo, f θ ^ 2 * sig η θ)
        + 2 * η * (1 + η) * (∫ θ in Iθo,
            f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
    have h1 : (∫ θ in Iθo, sig η θ * (f θ * deriv (deriv f) θ))
        = - (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2)
          - (∫ θ in Iθo, sigD η θ * (f θ * deriv f θ)) := by
      linarith only [hABC]
    rw [h1, hICrho, hIBPrho, hRhoDSplit]
    ring
  -- ===== Step 6: match the goal. =====
  have eL : (∫ θ in Iθo, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
      = (∫ θ in Iθo, sig η θ * (f θ * deriv (deriv f) θ)) := by
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro θ hθ
    simp only [sig]
    ring
  have eA : (∫ θ in Iθo, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = (∫ θ in Iθo, sig η θ * (deriv f θ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro θ hθ
    simp only [sig]
    ring
  have eS : (∫ θ in Iθo, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
      = (∫ θ in Iθo, f θ ^ 2 * sig η θ) := by
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro θ hθ
    simp only [sig]
  rw [eL, eA, eS, hBmain]

end Work.FTS.EllipticEst.Honest
