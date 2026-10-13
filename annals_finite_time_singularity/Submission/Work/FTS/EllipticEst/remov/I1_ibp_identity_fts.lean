/-
Work module for the Elgindi finite-time singularity project (area: `FTS/EllipticEst/remov`).

# The radial (`z`) integration by parts of `I₁`, in the weakened honesty form

This is `Work.FTS.EllipticEst.AngSecond.I1_ibp_identity` of
`Submission/Work/FTS/EllipticEst/AngClean/I1_ibp.lean`, with the hypothesis
`IPMem (H Ψ) (H Ψ)` replaced by the mixed honesty `IPMem (G Ψ) (H Ψ)` (obtainable in the
application from the angular integration by parts, cf. `remov.IPMem_G_H_fts`).  The only place
where the original uses the diagonal honesty of `H Ψ` is the call to `I1_honesty`, which
produces `IPMem (G Ψ) (Phi Ψ)`; here that is obtained from `hU`, `hφ` by the AM-GM
polarisation `Work.AngSecond.IPMem_of_diag_smooth`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngClean.I1_ibp
import Submission.Work.AngSecond.I1_honesty
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real ContDiff

namespace Work.FTS.EllipticEst.remov

open Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000


/-! ## The limit `n → ∞` -/

/-- **The radial integration by parts of `I₁`.** -/
theorem I1_ibp_identity_fts (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.Spaces.SmoothNbhd Ψ)
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hU : IPMem (G Ψ) (G Ψ)) (hφ : IPMem (Phi Ψ) (Phi Ψ)) (hUH : IPMem (G Ψ) (H Ψ)) :
    IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      = - IP (G Ψ) (H Ψ) - IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
  have hUφ : IPMem (G Ψ) (Phi Ψ) :=
    Work.AngSecond.IPMem_of_diag_smooth (smoothNbhd_G Ψ hΨ) (smoothNbhd_Phi Ψ hΨ) hU hφ
  have hAfun : IntegrableOn (Afun Ψ) Work.Spaces.Iz := integrableOn_Afun Ψ hQ
  have hPhi1 : IntegrableOn (Phi1 Ψ) Work.Spaces.Iz := integrableOn_Phi1 Ψ hUφ
  have hBfun : IntegrableOn (Bfun Ψ) Work.Spaces.Iz := integrableOn_Bfun Ψ hUφ hUH
  have hkey : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Bfun Ψ z))
        - (∫ z in Work.Spaces.Iz, Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
    intro n
    have h1 := I1_cutoff_identity_alt n Ψ hΨ
    rw [IP_cut_eq n Ψ] at h1
    have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ * nice n Ψ z θ)
        = (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Bfun Ψ z)
          + (∫ z in Work.Spaces.Iz,
              Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) := by
      rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.sig θ * nice n Ψ z θ)
          = ∫ z in Work.Spaces.Iz, (Work.FTS.EllipticEst.cut n z * Bfun Ψ z
              + Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) from
          setIntegral_congr_fun measurableSet_Ici (fun z hz => nfun_eq n Ψ hUφ hUH hz)]
      exact MeasureTheory.integral_add (integrableOn_cut_mul hBfun n)
        (integrableOn_cutDeriv_mul hPhi1 n)
    rw [h1, h2]
    ring
  have htA := tendsto_setIntegral_cut_mul hAfun
  have htB := tendsto_setIntegral_cut_mul hBfun
  have htC := tendsto_setIntegral_cutDeriv_mul hPhi1
  have hseq : (fun n : ℕ => ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Afun Ψ z)
      = fun n : ℕ => (- (∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.cut n z * Bfun Ψ z))
          - (∫ z in Work.Spaces.Iz,
              Phi1 Ψ z * (z * deriv (Work.FTS.EllipticEst.cut n) z)) :=
    funext hkey
  rw [hseq] at htA
  have hlim : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = (- (∫ z in Work.Spaces.Iz, Bfun Ψ z)) - 0 := tendsto_nhds_unique htA (htB.neg.sub htC)
  have hA : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ) := by
    rw [IP]
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [Akern])
  have hPhi1c : (∫ z in Work.Spaces.Iz, cw z * Phi1 Ψ z)
      = IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    rw [show (∫ z in Work.Spaces.Iz, cw z * Phi1 Ψ z)
        = ∫ z in Work.Spaces.Iz, Cwfun Ψ z from
        setIntegral_congr_fun measurableSet_Ici (fun z _ => by
          rw [Cwfun, Phi1, ← MeasureTheory.integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))]
    rw [IP]
    exact setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBHc : (∫ z in Work.Spaces.Iz, BHfun Ψ z) = IP (G Ψ) (H Ψ) := by
    rw [IP]
    exact setIntegral_congr_fun measurableSet_Ici (fun z _ =>
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring))
  have hBZ : (∫ z in Work.Spaces.Iz, Bfun Ψ z)
      = IP (G Ψ) (H Ψ) + IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    have hsplit : (∫ z in Work.Spaces.Iz, Bfun Ψ z)
        = ∫ z in Work.Spaces.Iz, (cw z * Phi1 Ψ z + BHfun Ψ z) :=
      setIntegral_congr_fun measurableSet_Ici (fun z hz => Bfun_eq Ψ hUφ hUH hz)
    rw [hsplit, MeasureTheory.integral_add (integrableOn_cwPhi1 Ψ hPhi1)
      (integrableOn_BHfun Ψ hUH), hPhi1c, hBHc]
    ring
  have hgoal : (∫ z in Work.Spaces.Iz, Afun Ψ z)
      = - IP (G Ψ) (H Ψ) - IP (G Ψ) (fun z θ => cw z * Phi Ψ z θ) := by
    rw [hlim, hBZ]
    ring
  rw [← hA]
  exact hgoal



end Work.FTS.EllipticEst.remov
