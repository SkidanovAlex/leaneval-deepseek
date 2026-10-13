/-
Copyright: work module for the Elgindi finite-time singularity project.

# The moment identity `L₁₂(F) = 15α F_*(Ψ) + 3α² F_*(D_zΨ)` and the certificate `L₁₂(F)·sin 2θ ∈ ℋ^k`

The helpers of this module are adapted (with the integrability chain of the angular moment)
from the unfinished development `Submission/Work/FTS/EllipticEst/TT/Straight_aux.lean`, whose
two unproved inputs `Cert.L12Aux.Fstar_L2_of_EllHyp` and
`Cert.L12Aux.Fstar_DzIter_one_L2_of_EllHyp` are replaced here by the self-contained proofs
below (`Fstar_sq_integrable_of_continuousOn`, `Fstar_F_sq_integrable_of_EllHyp`,
`Fstar_DzIter_one_sq_integrable`).  The main outputs are the moment identity
`Work.FTS.EllipticEst.TTL12M.L12_moment_eq_a1` and the certificates
`Work.FTS.EllipticEst.TTL12M.L12Sin_mem_a1` (`0 < α ≤ 1`) and
`Work.FTS.EllipticEst.TTL12M.L12Sin_mem_aux` (`0 < α ≤ 1/4`), all resting on
`[propext, Classical.choice, Quot.sound]`.

## Route

`L₁₂(F) = 3∫_z^∞ F_*(F)(r)/r dr = 15α F_*(Ψ)(z) + 3α² F_*(D_zΨ)(z)` on `(0,∞)`: the
difference of the two sides has vanishing derivative there (`HasDerivAt_L12_of_Fstar_facts`
and the chain rule for the angular moment), i.e. is constant, and the constant vanishes
because the right-hand side is square integrable while `L₁₂(F) → 0` at infinity.

For the certificate, the moment identity identifies `L₁₂(F)·sin 2θ` on the open quadrant with
`(15α F_*(Ψ) + 3α² F_*(D_zΨ))·sin 2θ`; the ODE `PsiStar_ode` rewrites the second moment as a
combination of `F_*(F)` and `F_*(z²∂_z²Ψ)`, and each of the three terms `F_*(g)·sin 2θ` lies
in `ℋ^k` by `Cert.HkMem_Fstar_sin_open`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.EllHyp_F_smoothOpen
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.EllipticEst.seq_tendsto_zero_of_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TTL12M

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


/-! ## The moment ODE, and the main certificate -/

/-- `SmoothOpen` is closed under pointwise sums. -/
theorem smoothOpen_add_tt {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p from rfl]
  exact hf.add hg

/-- **The ODE for the angular moment of a solution** (rewritten form of `PsiStar_ode`). -/
theorem FstarOde (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (h : Work.FTS.EllipticEst.EllHyp α k F Ψ) :
    ∀ z : ℝ, 0 < z →
      α ^ 2 * Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z
        + α * (5 + α) * Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z
      = -Work.Elliptic.Fstar F z := by
  intro z hz
  have hm1 : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z :=
    Work.FTS.EllipticEst.Cert.L12Aux.Fstar_DzIter_one_eq Ψ h.smoothNbhd hz
  have hm2 : deriv (fun z' => deriv (fun z'' => Work.Elliptic.Fstar Ψ z'') z') z
      = Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z :=
    (Work.FTS.EllipticEst.Cert.L12Aux.hasDerivAt_deriv_Fstar Ψ h.smoothNbhd hz).deriv
  have hscale : z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
      = Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z :=
    zsq_mul_Fstar z
  have hode := Work.Elliptic.PsiStar_ode α F Ψ z hα hz h.smoothNbhd h.sol
  rw [hm2] at hode
  rw [show α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
      = α ^ 2 * (z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) from by ring,
    hscale] at hode
  have hm1' : Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z
      = z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hm1
  rw [show α * (5 + α) * z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z
      = α * (5 + α) * (z * deriv (fun z' => Work.Elliptic.Fstar Ψ z') z) from by ring] at hode
  rw [← hm1'] at hode
  exact hode

/-- **`L₁₂(F)·sin 2θ ∈ ℋ^k`** for `0 < α ≤ 1` and the data of `EllHyp`. -/
theorem L12Sin_mem_gen (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  intro α F Ψ hα hα1 h
  have hαpos : (0 : ℝ) < α := hα
  have hmom := L12_moment_eq_a1 α k F Ψ hα hα1 h
  have hode := FstarOde α k F Ψ hα h
  set Z : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hZ
  have hSZ : Work.FTS.EllipticEst.SmoothOpen Z := by
    rw [hZ]
    exact Work.FTS.EllipticEst.SmoothOpen.zsq_mul
      (Work.FTS.EllipticEst.SmoothOpen.pzIter
        (Work.FTS.EllipticEst.SmoothNbhd_smoothOpen h.smoothNbhd) 2)
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.SmoothNbhd_smoothOpen h.smoothNbhd
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.EllipticEst.EllHyp_F_smoothOpen α k F Ψ hα h)
  have hZN : Work.Spaces.SmoothNbhd Z := by rw [hZ]; exact smoothNbhd_zsq_pzIter_two h.smoothNbhd
  have hZmem : Work.Spaces.HkMem α k Z := by rw [hZ]; exact h.memZ2
  have hSin : ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.contDiffOn_fstar_of_smoothNbhd Ψ h.smoothNbhd) hSin
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.fstar_smooth_of_sol_fts α F Ψ h.smoothNbhd h.sol) hSin
  have hsm3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Fstar Z z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.SmoothOpen.sep_mul
      (Work.FTS.EllipticEst.Cert.contDiffOn_fstar_of_smoothNbhd Z hZN) hSin
  have hM1 : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Ψ hα hα1 hSΨ h.memPsi
  have hM2 : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k F hα hα1 hSF h.memF
  have hM3 : Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar Z z * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin_open α k Z hα hα1 hSZ hZmem
  have h5α : (0 : ℝ) < 5 + α := by linarith
  have hc1 : (15 * α) ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 15 * α)
  have hc2 : (-(3 * α / (5 + α))) ≠ 0 := by
    rw [neg_ne_zero]
    exact div_ne_zero (ne_of_gt (by linarith : (0 : ℝ) < 3 * α)) (ne_of_gt h5α)
  have hc3 : (-(3 * α ^ 3 / (5 + α))) ≠ 0 := by
    rw [neg_ne_zero]
    exact div_ne_zero (ne_of_gt (by positivity : (0 : ℝ) < 3 * α ^ 3)) (ne_of_gt h5α)
  have hK1 : Work.Spaces.HkMem α k
      (fun z θ => (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_smul hc1 α k hM1
  have hK2 : Work.Spaces.HkMem α k
      (fun z θ => (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_smul hc2 α k hM2
  have hK3 : Work.Spaces.HkMem α k
      (fun z θ => (-(3 * α ^ 3 / (5 + α))) * (Work.Elliptic.Fstar Z z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_smul hc3 α k hM3
  have hS1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' _ hsm1
  have hS2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' _ hsm2
  have hS3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(3 * α ^ 3 / (5 + α))) * (Work.Elliptic.Fstar Z z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' _ hsm3
  have hS12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))) :=
    smoothOpen_add_tt hS1 hS2
  have hK12 : Work.Spaces.HkMem α k
      (fun z θ => (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_add_open hS1 hS2 hK1 hK2
  have hK123 : Work.Spaces.HkMem α k
      (fun z θ => (15 * α) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))
        + (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        + (-(3 * α ^ 3 / (5 + α))) * (Work.Elliptic.Fstar Z z * Real.sin (2 * θ))) :=
    Work.FTS.EllipticEst.HkMem_add_open hS12 hS3 hK12 hK3
  -- step 1: replace `F_*(D_zΨ)` by the other two moments on the open quadrant
  have hstep1 : Work.Spaces.HkMem α k
      (fun z θ => (15 * α * Work.Elliptic.Fstar Ψ z
        + 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z) * Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hK123
      (fun z hz θ hθ => by
        have hz' := hode z hz
        have hQ : 3 * α ^ 2 * Work.Elliptic.Fstar (Work.Spaces.Dz Ψ) z
            = (-(3 * α / (5 + α))) * (Work.Elliptic.Fstar F z
              + α ^ 2 * Work.Elliptic.Fstar Z z) := by
          have h5 : ((5 : ℝ) + α) ≠ 0 := ne_of_gt h5α
          have hα0 : α ≠ 0 := ne_of_gt hαpos
          field_simp
          linarith [hz']
        rw [hQ, hZ]
        ring)
  -- step 2: the moment identity identifies the two sides
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hstep1 ?_
  intro z hz θ hθ
  exact (congrArg (fun t : ℝ => t * Real.sin (2 * θ)) (hmom z hz)).symm

/-- **`L₁₂(F)·sin 2θ ∈ ℋ^k`** at `α ≤ 1` (the form used by the `Straight_certs` assembly). -/
theorem L12Sin_mem_a1 (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) :=
  L12Sin_mem_gen k

/-- **`L₁₂(F)·sin 2θ ∈ ℋ^k`** for `0 < α ≤ 1/4` and the data of `EllHyp`. -/
theorem L12Sin_mem_aux (k : ℕ) : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 / 4 → Work.FTS.EllipticEst.EllHyp α k F Ψ →
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.L12 F z * Real.sin (2 * θ)) := by
  intro α F Ψ hα hα4 h
  exact L12Sin_mem_gen k α F Ψ hα (by linarith) h

end Work.FTS.EllipticEst.TTL12M
