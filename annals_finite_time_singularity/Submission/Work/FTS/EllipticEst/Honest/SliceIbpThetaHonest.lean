import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpTheta
import Submission.Work.FTS.EllipticEst.Honest.HonSliceDerivBdd
import Submission.Work.FTS.EllipticEst.Honest.HonSliceAbsLe
import Submission.Work.FTS.EllipticEst.Honest.HonSliceIntegrable7

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

/-- The `θ`-slice integration by parts behind Elgindi's elliptic estimates, in the *honest*
form: `f` is only `C²` on the **open** interval `(0, π/2)`, only the endpoint *limits*
`f → 0` are assumed, and the three weighted `L²`-integrability conditions on
`f`, `f'`, `f''` replace the global boundedness of `f, f', f''`.

The proof is the one of `Honest.SliceIbpTheta` (`σ = sig η`, `ρ = rho η`, two integrations
by parts), with the three auxiliary inputs `SliceBounds`, `SliceIntegrable`, `SliceBoundary`
replaced by their honest counterparts `HonSliceDerivBdd` (boundedness of `f'` from the
integrability of `f''² σ`), `HonSliceAbsLe` (the endpoint bound `|f| ≤ C·min(θ, π/2-θ)`
from the limits and the bounded derivative) and `HonSliceIntegrable7` (the integrability of
the seven integrands), while `SliceBoundary` and `SliceWeightDeriv` are reused verbatim. -/
theorem SliceIbpThetaHonest (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        (Set.Ioo 0 (Real.pi / 2)) →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
        = - (∫ θ in Set.Ioo 0 (Real.pi / 2), (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * η * (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
          + 2 * η * (1 + η) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) := by
  intro f hf h0 hπ hA hB hC2
  -- Rewrite the goal with the abbreviation `Iθo = (0, π/2)` used throughout.
  change (∫ θ in Iθo, f θ * deriv (deriv f) θ * (Real.sin (2 * θ)) ^ (-η))
      = - (∫ θ in Iθo, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (∫ θ in Iθo, f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + 2 * η * (1 + η) * (∫ θ in Iθo,
            f θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
  -- ===== Step 1: the three honest ingredients. =====
  -- `f'` is bounded on `(0, π/2)` ...
  obtain ⟨C, hC0, hbd⟩ := HonSliceDerivBdd η hη0 f hf hC2
  -- ... hence `|f θ| ≤ C θ` and `|f θ| ≤ C (π/2 - θ)`, from the two endpoint limits ...
  obtain ⟨hb1, hb2⟩ := HonSliceAbsLe C hC0 f hf h0 hπ hbd
  -- ... and the seven integrands of the two integrations by parts are integrable.
  have hIntegrable :=
    HonSliceIntegrable7 η C hη0 hη1 hC0 f hf hb1 hb2 hbd hA hB hC2
  obtain ⟨hIA, hIB, hIC, hIrho, hIrhoD, hIsq, hIcos⟩ := hIntegrable
  -- ===== Step 2: the boundary terms vanish. =====
  have hBoundary :
      Tendsto (fun θ => sig η θ * f θ * deriv f θ) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ => sig η θ * f θ * deriv f θ)
        (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) ∧
      Tendsto (fun θ => rho η θ * f θ ^ 2) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
      Tendsto (fun θ => rho η θ * f θ ^ 2)
        (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) (nhds 0) :=
    SliceBoundary f η C hη0 hη1 hC0 hb1 hb2 hbd
  obtain ⟨hbd0, hbdπ, hbrho0, hbrhoπ⟩ := hBoundary
  have hSigRhoDeriv :
      (∀ θ ∈ Iθo, HasDerivAt (sig η) (sigD η θ) θ) ∧
      (∀ θ ∈ Iθo, HasDerivAt (rho η) (rhoD η θ) θ) :=
    SliceWeightDeriv η
  obtain ⟨hsig_d, hrho_d⟩ := hSigRhoDeriv
  -- ===== Step 3: derivative facts for `f`. =====
  have hmemIoo : ∀ θ ∈ Iθo, Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ :=
    fun θ hθ => IsOpen.mem_nhds isOpen_Ioo hθ
  have hdf : ∀ θ ∈ Iθo, HasDerivAt f (deriv f θ) θ := by
    intro θ hθ
    exact ((hf.contDiffAt (hmemIoo θ hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hddf : ∀ θ ∈ Iθo, HasDerivAt (deriv f) (deriv (deriv f) θ) θ := by
    intro θ hθ
    have h1 : ContDiffOn ℝ 1 (deriv f) Iθo := hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((h1.contDiffAt (hmemIoo θ hθ)).differentiableAt (by norm_num)).hasDerivAt
  -- ===== Step 4: the first integration by parts, through `G = σ f f'`. =====
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
  -- ===== Step 5: the second integration by parts, against `ρ`. =====
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
  -- ===== Step 6: the algebra. =====
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
  -- ===== Step 7: match the goal. =====
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
