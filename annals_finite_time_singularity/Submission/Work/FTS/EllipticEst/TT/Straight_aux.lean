/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary certificates for the straightened-solution estimates

This module collects the auxiliary analytic facts used by
`Submission/Work/FTS/EllipticEst/TT/Straight_certs.lean`:

* the square-integrability of the angular moment `F_*(g)²` from `g ∈ ℋ^k` and the smoothness of
  `g` on a neighbourhood of the closed quadrant (`Fstar_sq_integrable`);
* the corresponding statement for `F_*(D_zΨ)` for the data of `EllHyp`, from the ODE
  `α²z²m'' + α(5+α)zm' = -F_*(F)` of `Work.Elliptic.PsiStar_ode`;
* the square-integrability of the right-hand side of the moment identity
  (`integrableOn_moment_rhs_sq_aux`);
* the moment identity `L₁₂(F)(z) = 15αF_*(Ψ)(z) + 3α²F_*(D_zΨ)(z)` in the `α ≤ 1` form used by
  the straightened-solution certificates (`L12_moment_eq_a1`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk
import Submission.Work.FTS.EllipticEst.Cert.L12Aux.L12_moment_eq
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.seq_tendsto_zero_of_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of the square of the angular moment -/

/-- On the domain `(0,∞)` the radial weight satisfies `1 ≤ w`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have h : Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  rw [h]
  nlinarith [one_div_pos.mpr hz]

/-- The slice of a `SmoothNbhd` function at a positive radius is a.e. strongly measurable on
`Iθ`. -/
theorem aesm_slice_of_smoothNbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : 0 < z) : AEStronglyMeasurable (fun θ : ℝ => g z θ) (volume.restrict Work.Spaces.Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2)
    (hg.continuousOn.mono (fun p hp => by
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], ⟨by linarith [hp.2.1],
        by linarith [hp.2.2, Real.pi_pos]⟩⟩)) hz

/-- **The square of the angular moment is integrable** for a function which is smooth on a
neighbourhood of the closed quadrant and in `ℋ^k`.

Indeed `F_*(g)(z)² ≤ (π/2)∫_θ g(z,θ)² ≤ (π/2)∫_θ HkIntegrand α k g z θ`
(`Work.Elliptic.Fstar_sq_le`, and the `i = 0` radial summand of the `ℋ^k`-integrand dominates
`g²` because `1 ≤ w`), and `z ↦ ∫_θ HkIntegrand α k g z θ` is integrable on `Iz` by `HkMem`. -/
theorem Fstar_sq_integrable_of_continuousOn (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFstar : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar g z) (Set.Ioi 0))
    (hmem : Work.Spaces.HkMem α k g) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar g z) ^ 2) (Set.Ioi 0) := by
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    intro θ hθ
    exact Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _
  -- the pointwise domination on the open quadrant
  have hdom : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz θ hθ
    have hsinposθ : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsp : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hsinposθ _
    have hsin : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 := by
      refine Real.rpow_le_one (le_of_lt hsinposθ) (Real.sin_le_one (2 * θ)) ?_
      rw [Work.Spaces.eta]; norm_num
    have hzpos : (0 : ℝ) < z := hz
    have hH : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
      rw [one_le_div hsp]
      linarith [one_le_w hzpos]
    have hstep : (g z θ) ^ 2
        ≤ (Work.Spaces.DzIter 0 g z θ * (Work.Spaces.w z
            / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [Work.Spaces.DzIter_zero, mul_pow]
      simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hH) (sq_nonneg (g z θ))
    exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ 0 (Nat.zero_le k))
  -- the slices of `g²` are integrable on `Iθ`
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (g z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) ≤ volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_mono (fun x hx => by
        rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩) le_rfl
    have h1 : IntegrableOn (fun θ : ℝ => (g z θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
      refine MeasureTheory.Integrable.mono' ((hmem.1 z hzI).congr_set_ae hIoo)
        ((Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg
          hzpos).pow 2 |>.mono_measure hμ) ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hdom z hz θ hθ
    exact h1.congr_set_ae hIoo.symm
  -- the pointwise bound on the moment
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.Fstar g z) ^ 2
        ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have h1 := Work.Elliptic.Fstar_sq_le g z (hslice z hz)
    have h2 : (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
      rw [MeasureTheory.setIntegral_congr_set hIoo.symm,
        MeasureTheory.setIntegral_congr_set hIoo.symm]
      exact MeasureTheory.setIntegral_mono_on ((hslice z hz).congr_set_ae hIoo)
        ((hmem.1 z hzI).congr_set_ae hIoo) measurableSet_Ioo
        (fun θ hθ => hdom z hz θ hθ)
    have h3 : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ
    calc (Work.Elliptic.Fstar g z) ^ 2
        ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 := h1
      _ ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  -- measurability of `z ↦ F_*(g)(z)²`
  have haesm : AEStronglyMeasurable (fun z : ℝ => (Work.Elliptic.Fstar g z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (hFstar.aestronglyMeasurable measurableSet_Ioi).pow 2
  refine MeasureTheory.Integrable.mono'
    (g := fun z : ℝ => (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
    ?_ haesm ?_
  · exact (hmem.2.mono_set (fun z hz => by
      rw [Work.Spaces.Iz]; exact le_of_lt (show (0 : ℝ) < z from hz))).const_mul (π / 2)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt z hz


/-- The `SmoothNbhd` version of `Fstar_sq_integrable_of_continuousOn`. -/
theorem Fstar_sq_integrable (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hg : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α k g) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar g z) ^ 2) (Set.Ioi 0) :=
  Fstar_sq_integrable_of_continuousOn α k hα
    (hg.continuousOn.mono (fun p hp => by
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], ⟨by linarith [hp.2.1],
        by linarith [hp.2.2, Real.pi_pos]⟩⟩))
    (fun z hz => (Work.FTS.EllipticEst.Cert.L12Aux.continuousAt_Fstar g hg hz).continuousWithinAt)
    hmem

/-- The `ℋ^k`-integrability of `F_*(F)²` for the source `F` of an `EllHyp` datum: `F` is only
`C^∞` on the *open* quadrant, so the smoothness input is replaced by the continuity of
`F_*(F)` on `(0,∞)`. -/
theorem Fstar_F_sq_integrable_of_EllHyp (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar F z) ^ 2) (Set.Ioi 0) := by
  have hSm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ h.smoothNbhd)
      (fun z θ hz hθ0 hθ1 => h.sol.1 z hz θ hθ0 hθ1)
  exact Fstar_sq_integrable_of_continuousOn α k (g := F) hα hSm.continuousOn
    (Work.FTS.EllipticEst.Cert.L12Aux.continuousOn_Fstar_of_EllHyp α k F Ψ hα h) h.memF

/-! ## Smoothness of the two radial functions used in the ODE argument -/

/-- `z² ∂_z²Ψ` is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_zsq_pzIter_two {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
  Work.FTS.EllipticEst.Cert.smoothNbhd_mul' (Work.FTS.EllipticEst.Cert.smoothNbhd_pow_fst 2)
    (Work.Spaces.smoothNbhd_pzIter h 2)

/-- `D_zΨ` is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_Dz {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.Dz Ψ) :=
  Work.FTS.EllipticEst.Cert.smoothNbhd_mul' (Work.FTS.EllipticEst.Cert.smoothNbhd_fst)
    (Work.Spaces.smoothNbhd_pzIter h 1)

/-! ## `F_*(D_zΨ)²` for the data of `EllHyp` -/

/-- `z² F_*(∂_z²Ψ)(z) = F_*(z² ∂_z²Ψ)(z)`: the radial factor is constant in `θ`. -/
theorem zsq_mul_Fstar {g : ℝ → ℝ → ℝ} (z : ℝ) :
    z ^ 2 * Work.Elliptic.Fstar g z
      = Work.Elliptic.Fstar (fun z' θ => z ^ 2 * g z' θ) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)

/-- **`F_*(D_zΨ)²` is integrable** for the data of `EllHyp`.  The moment `m = F_*(Ψ)` satisfies
`α²z²m'' + α(5+α)zm' = -F_*(F)` (`Work.Elliptic.PsiStar_ode`), and `F_*(D_zΨ)(z) = z m'(z)`,
`m''(z) = F_*(∂_z²Ψ)(z)`; hence `F_*(D_zΨ)(z)²` is dominated by `F_*(F)(z)²` and
`z⁴F_*(∂_z²Ψ)(z)² = F_*(z²∂_z²Ψ)(z)²`, both of which are integrable by the ODE and
`Fstar_sq_integrable`. -/
theorem Fstar_DzIter_one_sq_integrable (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2)
      (Set.Ioi 0) := by
  have hF : IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar F z) ^ 2) (Set.Ioi 0) :=
    Fstar_F_sq_integrable_of_EllHyp α k F Ψ hα h
  have hZ : IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) (Set.Ioi 0) :=
    Fstar_sq_integrable α k hα (smoothNbhd_zsq_pzIter_two h.smoothNbhd) h.memZ2
  have hα5 : (0 : ℝ) < α * (5 + α) := by positivity
  have hA : (0 : ℝ) < (α * (5 + α)) ^ 2 := by positivity
  -- the pointwise bound
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2
        ≤ (2 / (α * (5 + α)) ^ 2)
          * ((Work.Elliptic.Fstar F z) ^ 2
            + α ^ 4 * (Work.Elliptic.Fstar
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hm1 : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
        = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z :=
      Work.FTS.EllipticEst.Cert.L12Aux.Fstar_DzIter_one_eq Ψ h.smoothNbhd hzpos
    have hm2 : deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
        = Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z :=
      (Work.FTS.EllipticEst.Cert.L12Aux.hasDerivAt_deriv_Fstar Ψ h.smoothNbhd hzpos).deriv
    have hscale : z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
        = Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z :=
      zsq_mul_Fstar z
    have hodeB : α ^ 2 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)
        + α * (5 + α) * (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)
        = -Work.Elliptic.Fstar F z := by
      have h := Work.Elliptic.PsiStar_ode α F Ψ z hα hzpos h.smoothNbhd h.sol
      rw [hm2] at h
      rw [show α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
          = α ^ 2 * (z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z)
          from by ring, hscale] at h
      simpa only [mul_assoc] using h
    have hneg : Work.Elliptic.Fstar F z + α ^ 2 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)
        = -(α * (5 + α) * (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z)) := by
      linarith
    have hApos : (0 : ℝ) < (α * (5 + α)) ^ 2 := by positivity
    have hmain : (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z) ^ 2
        = (Work.Elliptic.Fstar F z + α ^ 2 * (Work.Elliptic.Fstar
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)) ^ 2
          / (α * (5 + α)) ^ 2 := by
      rw [hneg, neg_sq, eq_div_iff (ne_of_gt hApos)]
      ring
    have hexp : (Work.Elliptic.Fstar F z + α ^ 2 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)) ^ 2
        ≤ 2 * ((Work.Elliptic.Fstar F z) ^ 2 + (α ^ 2 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)) ^ 2) := by
      nlinarith [sq_nonneg (Work.Elliptic.Fstar F z - α ^ 2 * (Work.Elliptic.Fstar
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z))]
    have hone : (α ^ 2 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)) ^ 2
        = α ^ 4 * (Work.Elliptic.Fstar
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2 := by ring
    rw [hone] at hexp
    rw [hm1]
    calc (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z) ^ 2
        = (Work.Elliptic.Fstar F z + α ^ 2 * (Work.Elliptic.Fstar
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z)) ^ 2
          / (α * (5 + α)) ^ 2 := hmain
      _ ≤ (2 / (α * (5 + α)) ^ 2) * ((Work.Elliptic.Fstar F z) ^ 2
            + α ^ 4 * (Work.Elliptic.Fstar
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) := by
          rw [div_le_iff₀ hApos]
          have h2 : (2 / (α * (5 + α)) ^ 2) * ((Work.Elliptic.Fstar F z) ^ 2
                + α ^ 4 * (Work.Elliptic.Fstar
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2)
                * (α * (5 + α)) ^ 2
              = 2 * ((Work.Elliptic.Fstar F z) ^ 2
                + α ^ 4 * (Work.Elliptic.Fstar
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) := by
            field_simp
          rw [h2]
          exact hexp
  -- integrability by domination
  have hcont : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
      (Set.Ioi 0) :=
    fun z hz => (Work.FTS.EllipticEst.Cert.L12Aux.continuousAt_Fstar
      (Work.Spaces.DzIter 1 Ψ) (smoothNbhd_Dz h.smoothNbhd) hz).continuousWithinAt
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (hcont.aestronglyMeasurable measurableSet_Ioi).pow 2
  refine MeasureTheory.Integrable.mono'
    (g := fun z : ℝ => (2 / (α * (5 + α)) ^ 2)
      * ((Work.Elliptic.Fstar F z) ^ 2
        + α ^ 4 * (Work.Elliptic.Fstar
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2))
    ?_ haesm ?_
  · exact (hF.add (hZ.const_mul (α ^ 4))).const_mul (2 / (α * (5 + α)) ^ 2)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpt z hz


/-! ## The moment identity -/

/-- **The right-hand side of the moment identity is square integrable**: this is the input which
turns `L₁₂(F) - (15αF_*(Ψ) + 3α²F_*(D_zΨ))` into a constant vanishing along a sequence at
infinity. -/
theorem integrableOn_moment_rhs_sq_aux (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn (fun z : ℝ => (Work.Elliptic.Fstar Ψ z) ^ 2)
      (Set.Ioi 0) := Fstar_sq_integrable α k hα h.smoothNbhd h.memPsi
  have h2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) :=
    Fstar_DzIter_one_sq_integrable α k F Ψ hα h
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ =>
      2 * ((15 * α) ^ 2 * (Work.Elliptic.Fstar Ψ z) ^ 2)
        + 2 * ((3 * α ^ 2) ^ 2 * (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2))
      (Set.Ioi 0) :=
    ((h1.const_mul ((15 * α) ^ 2)).const_mul 2).add
      ((h2.const_mul ((3 * α ^ 2) ^ 2)).const_mul 2)
  show MeasureTheory.Integrable _ (volume.restrict (Set.Ioi 0))
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · have hm1 : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar Ψ z) (Set.Ioi 0) :=
      fun z hz => (Work.FTS.EllipticEst.Cert.L12Aux.continuousAt_Fstar Ψ h.smoothNbhd hz).continuousWithinAt
    have hm2 : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)
        (Set.Ioi 0) :=
      fun z hz => (Work.FTS.EllipticEst.Cert.L12Aux.continuousAt_Fstar
        (Work.Spaces.DzIter 1 Ψ) (smoothNbhd_Dz h.smoothNbhd) hz).continuousWithinAt
    exact (((continuousOn_const.mul hm1).add (continuousOn_const.mul hm2)).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards with z
    have hrw : 2 * ((15 * α) ^ 2 * (Work.Elliptic.Fstar Ψ z) ^ 2)
        + 2 * ((3 * α ^ 2) ^ 2 * (Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2)
        = 2 * (15 * α * Work.Elliptic.Fstar Ψ z) ^ 2
          + 2 * (3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2 := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, hrw,
      abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (15 * α * Work.Elliptic.Fstar Ψ z
      - 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z)]

/-- **The moment identity at `α ≤ 1`**: `L₁₂(F)(z) = 15α F_*(Ψ)(z) + 3α² F_*(D_zΨ)(z)` for every
`z > 0`, for the data of `EllHyp α k F Ψ` and `0 < α ≤ 1`.

The difference `K` of the two sides has vanishing derivative on `(0,∞)` (`L₁₂(F)' = -3F_*(F)/z`
and the chain rule for the angular moment), and the right-hand side is square integrable on
`(0,∞)`; hence `K` is constant on `(0,∞)` and, by `L₁₂(F) → 0` at infinity, identically zero. -/
theorem L12_moment_eq_a1 (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.L12 F z
      = 15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z := by
  set K : ℝ → ℝ := Work.Elliptic.L12 F
    - (fun z => 15 * α * Work.Elliptic.Fstar Ψ z
      + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) with hK
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ h.smoothNbhd h.sol
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.FstarDivIntegrableOfSolHk α k F Ψ hα h.smoothNbhd h.sol h.memF
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts F hFsm hFint
  have hR : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun w => 15 * α * Work.Elliptic.Fstar Ψ w
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) w)
        (-(3 * Work.Elliptic.Fstar F z / z)) z :=
    Work.FTS.EllipticEst.Cert.L12Aux.hasDerivAt_moment_rhs α k F Ψ hα h
  have hKd : ∀ z ∈ Set.Ioi (0 : ℝ), deriv K z = 0 := by
    intro z hz
    rw [hK]
    simpa only [sub_self] using ((hL12 z hz).sub (hR z hz)).deriv
  have hKconst : ∀ a ∈ Set.Ioi (0 : ℝ), ∀ b ∈ Set.Ioi (0 : ℝ), K a = K b := by
    intro a ha b hb
    refine IsOpen.is_const_of_deriv_eq_zero (𝕜 := ℝ) isOpen_Ioi isPreconnected_Ioi ?_ ?_ ha hb
    · intro w hw
      exact ((hL12 w hw).sub (hR w hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      exact hKd w hw
  have hL12tend : Filter.Tendsto (Work.Elliptic.L12 F) Filter.atTop (nhds 0) :=
    Work.FTS.EllipticEst.Cert.L12Aux.tendsto_L12_atTop F hFint
  have hH2 : MeasureTheory.IntegrableOn
      (fun z : ℝ => (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) ^ 2) (Set.Ioi 0) :=
    integrableOn_moment_rhs_sq_aux α k F Ψ hα h
  obtain ⟨u, hu, hu2⟩ := Work.FTS.EllipticEst.seq_tendsto_zero_of_integrableOn hH2
  have hHtend : Filter.Tendsto (fun j : ℕ => 15 * α * Work.Elliptic.Fstar Ψ (u j)
      + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) Filter.atTop
      (nhds 0) := by
    have hsqrt : Filter.Tendsto
        (fun j : ℕ => Real.sqrt ((15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) ^ 2))
        Filter.atTop (nhds 0) := by
      have h' := Real.continuous_sqrt.continuousAt.tendsto.comp hu2
      simpa only [Function.comp_def, Real.sqrt_zero] using h'
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hfun : (fun j : ℕ => ‖(15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) - 0‖)
        = fun j : ℕ => Real.sqrt ((15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j)) ^ 2) := by
      funext j
      rw [sub_zero, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    rw [hfun]
    exact hsqrt
  have hKlim : Filter.Tendsto (fun j : ℕ => K (u j)) Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun j : ℕ => Work.Elliptic.L12 F (u j)
        - (15 * α * Work.Elliptic.Fstar Ψ (u j)
          + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) (u j))) Filter.atTop
        (nhds 0) := by
      have h' := (hL12tend.comp hu).sub hHtend
      simpa only [Function.comp_def, sub_zero] using h'
    rw [hK]
    exact hsub
  intro z hz
  have hzeq : K z = 0 := by
    have hu_pos : ∀ᶠ j : ℕ in Filter.atTop, 0 < u j := hu.eventually (eventually_gt_atTop 0)
    have hconst : ∀ᶠ j : ℕ in Filter.atTop, K (u j) = K z := by
      filter_upwards [hu_pos] with j hj
      exact hKconst (u j) hj z hz
    exact tendsto_nhds_unique (tendsto_nhds_of_eventually_eq hconst) hKlim
  rw [hK] at hzeq
  have hz' : Work.Elliptic.L12 F z
      - (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z) = 0 := by
    simpa only [Pi.sub_apply] using hzeq
  linarith


/-! ## Weighted integrability of the angular moments

The estimates below are the *weighted* (`w²`) versions of `Fstar_sq_integrable`; they are what the
membership statements `R·sin 2θ ∈ ℋ^k` need, since the `ℋ^k`-integrand of a separated function
`R(z)·sin 2θ` is dominated by `w(z)²·Σ_{j≤k}(D_z^jR)(z)²` times an angular profile. -/

/-- `z ↦ w(z)²` is continuous on `(0,∞)`. -/
theorem continuousOn_w_sq : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => (1 + z) ^ 4 / z ^ 4 := by
    funext z
    rw [Work.Spaces.w]
    field_simp
  rw [hfun]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  exact pow_ne_zero 4 (ne_of_gt (Set.mem_Ioi.mp hz))

/-- **A general weighted moment bound**: if `g` is continuous on the open quadrant, `F_*(g)` is
continuous on `(0,∞)` and `g ∈ ℋ^k`, then `w²·F_*(g)²` is integrable on `(0,∞)`.

Indeed `F_*(g)(z)² ≤ (π/2)∫_θ g(z,θ)²` (Cauchy–Schwarz, `Work.Elliptic.Fstar_sq_le`) and,
after multiplying by `w(z)²`, the pointwise domination `w²g² ≤ HkIntegrand α k g` (which holds
because `w² ≤ w²·sin(2θ)^{-η}`) turns the right-hand side into `(π/2)∫_θ HkIntegrand α k g`, an
integrable function of `z` by `HkMem`. -/
theorem w_sq_mul_Fstar_sq_integrable_of_majorant {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hFstar : ContinuousOn (fun z : ℝ => Work.Elliptic.Fstar g z) (Set.Ioi 0))
    {M : ℝ → ℝ → ℝ}
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2 ≤ M z θ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar g z) ^ 2)
      (Set.Ioi 0) := by
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    intro θ hθ
    exact Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _
  have hsinle : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
    intro θ hθ
    have hsp : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 := by
      refine Real.rpow_le_one (le_of_lt hsp) (Real.sin_le_one (2 * θ)) ?_
      rw [Work.Spaces.eta]; norm_num
    have h2 : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := le_of_lt (Real.rpow_pos_of_pos hsp _)
    nlinarith
  -- the `θ`-slices
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => (g z θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) ≤ volume.restrict Work.Spaces.Iθ :=
      MeasureTheory.Measure.restrict_mono (fun x hx => by
        rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩) le_rfl
    have hMw : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
      nlinarith [one_le_w hzpos]
    refine MeasureTheory.Integrable.mono'
      (((hMslice z hzI).congr_set_ae hIoo).const_mul ((Work.Spaces.w z) ^ 2)⁻¹)
      (((Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg
        hzpos).pow 2).mono_measure hμ) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h3 : (g z θ) ^ 2
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2 * (g z θ) ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hMw), one_mul]
      rw [h3]
      exact mul_le_mul_of_nonneg_left (hle z hz θ hθ) (by positivity)
  -- the pointwise bound in `z`
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar g z) ^ 2
        ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, M z θ := by
    intro z hz
    have hzpos : (0 : ℝ) < z := hz
    have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
    have hw2pos : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
      nlinarith [one_le_w hzpos]
    have h1 : (Work.Elliptic.Fstar g z) ^ 2
        ≤ (π / 2) * ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2 := by
      have hFs := Work.Elliptic.Fstar_sq_le g z ((hslice z hz).congr_set_ae hIoo.symm)
      have heq : (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2)
          = ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2 :=
        MeasureTheory.setIntegral_congr_set hIoo.symm
      calc (Work.Elliptic.Fstar g z) ^ 2
          ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 := hFs
        _ = (π / 2) * ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2 := by rw [heq]
    have h2 : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2)
        ≤ ((Work.Spaces.w z) ^ 2)⁻¹ * ∫ θ in Work.Spaces.Iθ, M z θ := by
      have hMI : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), M z θ)
          = ∫ θ in Work.Spaces.Iθ, M z θ :=
        (MeasureTheory.setIntegral_congr_set hIoo.symm).symm
      rw [← hMI]
      have hfun : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2)
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
              (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul, ← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hw2pos), one_mul]
      have hmono : (∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2)
          ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), M z θ :=
        MeasureTheory.setIntegral_mono_on
          (((hslice z hz).const_mul ((Work.Spaces.w z) ^ 2)).congr
            (Filter.Eventually.of_forall fun θ => by ring))
          ((hMslice z hzI).congr_set_ae hIoo) measurableSet_Ioo (fun θ hθ => hle z hz θ hθ)
      rw [hfun]
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    have h3 : (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar g z) ^ 2
        ≤ (π / 2) * ((Work.Spaces.w z) ^ 2
            * ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hw2pos)
      linarith
    have h4 : (Work.Spaces.w z) ^ 2 * ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (g z θ) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, M z θ := by
      have h := mul_le_mul_of_nonneg_left h2 (le_of_lt hw2pos)
      have h5 : (Work.Spaces.w z) ^ 2 * (((Work.Spaces.w z) ^ 2)⁻¹
            * ∫ θ in Work.Spaces.Iθ, M z θ)
          = ∫ θ in Work.Spaces.Iθ, M z θ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw2pos), one_mul]
      linarith [h, h5]
    have h6 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ π / 2)
    linarith [h3, h6]
  -- measurability and integrability
  have haesm : AEStronglyMeasurable
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar g z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi).mul
      ((hFstar.aestronglyMeasurable measurableSet_Ioi).pow 2)
  refine MeasureTheory.Integrable.mono'
    (g := fun z : ℝ => (π / 2) * ∫ θ in Work.Spaces.Iθ, M z θ)
    ?_ haesm ?_
  · exact (hMz.mono_set (fun z hz => by
      rw [Work.Spaces.Iz]; exact le_of_lt (show (0 : ℝ) < z from hz))).const_mul (π / 2)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hpt z hz


/-! ## Weighted moment bounds for the radial iterates of the straightened pieces

These are the inputs of the membership statements `R·sin 2θ ∈ ℋ^k`: the sharp form of
`Work.FTS.EllipticEst.Cert.HkMem_radialSin_of_bound` needs the integrability of the weighted
radial iterates of `R`, and for the radial pieces `R` occurring here (`F_*(F)`,
`F_*(D_z^jΨ)`, …) that integrability comes from the weighted moment bounds above. -/

/-- `D_z^jΨ` is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_DzIter {Ψ : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd Ψ) (j : ℕ) :
    Work.Spaces.SmoothNbhd (Work.Spaces.DzIter j Ψ) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ]
      exact Work.FTS.EllipticEst.Cert.smoothNbhd_mul' Work.FTS.EllipticEst.Cert.smoothNbhd_fst
        (Work.Spaces.smoothNbhd_pzIter ih 1)

/-- The `SmoothNbhd` form of the weighted moment bound. -/
theorem w_sq_mul_Fstar_sq_integrable_nbhd {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {M : ℝ → ℝ → ℝ}
    (hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ : ℝ => M z θ) Work.Spaces.Iθ)
    (hMz : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2 ≤ M z θ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar g z) ^ 2)
      (Set.Ioi 0) :=
  w_sq_mul_Fstar_sq_integrable_of_majorant (g := g)
    (Work.FTS.EllipticEst.SmoothNbhd_smoothOpen hg).continuousOn
    (fun z hz =>
      (Work.FTS.EllipticEst.Cert.L12Aux.continuousAt_Fstar g hg hz).continuousWithinAt)
    hMslice hMz hle

/-- The pointwise domination `w(z)²·h² ≤ HkIntegrand α k g` given by the `i`-th radial summand,
on the *open* angular interval (at the endpoints `sin 2θ = 0` the domination can fail). -/
theorem w_sq_mul_sq_le_HkIntegrand {α : ℝ} {k i : ℕ} (hi : i ≤ k) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ z θ, h z θ = Work.Spaces.DzIter i g z θ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsp : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    refine Real.rpow_le_one (le_of_lt hsp) (Real.sin_le_one (2 * θ)) ?_
    rw [Work.Spaces.eta]; norm_num
  have hstep : (Work.Spaces.w z) ^ 2 * (h z θ) ^ 2
      ≤ (Work.Spaces.DzIter i g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hgh z θ, mul_pow, div_pow, ← mul_div_assoc]
    rw [le_div_iff₀ (pow_pos (Real.rpow_pos_of_pos hsp _) 2)]
    have hsp' := Real.rpow_pos_of_pos hsp (Work.Spaces.eta / 2)
    have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 ≤ 1 := by
      nlinarith [hsin, hsp']
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i g z θ) ^ 2
            * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i g z θ) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
  exact le_trans hstep (Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi)

/-- The weighted moment of `F_*(Ψ)`. -/
theorem w_sq_Fstar_psi (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar Ψ z) ^ 2)
      (Set.Ioi 0) :=
  w_sq_mul_Fstar_sq_integrable_nbhd h.smoothNbhd
    (M := Work.Spaces.HkIntegrand α k Ψ) h.memPsi.1 h.memPsi.2
    (fun z _ θ hθ => w_sq_mul_sq_le_HkIntegrand (g := Ψ) (h := Ψ) (Nat.zero_le k)
      (fun _ _ => rfl) hθ)

/-- The weighted moment of `F_*(F)` — the source is only `C^∞` on the open quadrant, so the
smoothness input is replaced by the continuity of the integrand. -/
theorem w_sq_Fstar_F (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar F z) ^ 2)
      (Set.Ioi 0) := by
  have hSm : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp α Ψ h.smoothNbhd)
      (fun z θ hz hθ0 hθ1 => h.sol.1 z hz θ hθ0 hθ1)
  exact w_sq_mul_Fstar_sq_integrable_of_majorant (g := F) hSm.continuousOn
    (Work.FTS.EllipticEst.Cert.L12Aux.continuousOn_Fstar_of_EllHyp α k F Ψ hα h)
    h.memF.1 h.memF.2
    (fun z _ θ hθ => w_sq_mul_sq_le_HkIntegrand (g := F) (h := F) (Nat.zero_le k)
      (fun _ _ => rfl) hθ)

/-- The weighted moment of `F_*(z²∂_z²Ψ)`. -/
theorem w_sq_Fstar_zsq_pzIter_two (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Work.Elliptic.Fstar
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z) ^ 2) (Set.Ioi 0) :=
  w_sq_mul_Fstar_sq_integrable_nbhd (smoothNbhd_zsq_pzIter_two h.smoothNbhd)
    (M := Work.Spaces.HkIntegrand α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    h.memZ2.1 h.memZ2.2
    (fun z _ θ hθ => w_sq_mul_sq_le_HkIntegrand (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (h := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Nat.zero_le k)
      (fun _ _ => rfl) hθ)

/-- The weighted moment of `F_*(D_z^jΨ)` for `j ≤ k`. -/
theorem w_sq_Fstar_DzIter_le (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (fun z : ℝ => (Work.Spaces.w z) ^ 2
      * (Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z) ^ 2) (Set.Ioi 0) :=
  w_sq_mul_Fstar_sq_integrable_nbhd (smoothNbhd_DzIter h.smoothNbhd j)
    (M := Work.Spaces.HkIntegrand α k Ψ) h.memPsi.1 h.memPsi.2
    (fun z _ θ hθ => w_sq_mul_sq_le_HkIntegrand (g := Ψ) (h := Work.Spaces.DzIter j Ψ) hj
      (fun _ _ => rfl) hθ)

end Work.FTS.EllipticEst.TT
