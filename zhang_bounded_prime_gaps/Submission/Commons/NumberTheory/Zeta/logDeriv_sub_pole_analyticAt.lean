import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.NumberTheory.Zeta.lSeries_mangoldt_integral_eq_zeta_logDeriv

open Filter
open scoped Topology

/-!
# P1 (generic core): per-zero log-derivative pole removal

If `f` is analytic at `ρ`, vanishes there, and factorises near `ρ` as `f(s) = (s−ρ)^m·g(s)`
with `g` analytic, `g(ρ) ≠ 0`, `m ≥ 1`, then the pole of `logDeriv f` at `ρ` is removable
with residue `m`: there is an analytic `F` with `F s = logDeriv f s − m/(s−ρ)` eventually on
the punctured neighbourhood of `ρ`.

This is the T-R3.1/P1 stone (see Submission/Work/NumberTheory/Robin/r3.lean design): at a zero
`ρ` of `ζ₁` of multiplicity `m` it removes the log-derivative pole so that P2/P4 can assemble
the rectangle contour identity `rectInt z w (psiIntF x) = 2πi·(x − Σ m_ρ x^ρ/ρ)`.

Mirror this proof in the commons module (statement in `Commons.NumberTheory.Zeta`, namespace
`Commons.NumberTheory.Zeta`, proof below verbatim with all names fully qualified if needed).
-/

namespace Commons.NumberTheory.Zeta

noncomputable section

theorem logDeriv_sub_pole_analyticAt {f g : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f ρ) (hρ : f ρ = 0) (hg : AnalyticAt ℂ g ρ) (hgρ : g ρ ≠ 0)
    (hfac : Filter.EventuallyEq (nhds ρ) f (fun s => (s - ρ) ^ m * g s))
    (hm : 1 ≤ m) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      Filter.Eventually (fun s => F s = logDeriv f s - m / (s - ρ))
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
  refine ⟨fun s => logDeriv g s, ?_, ?_⟩
  · change AnalyticAt ℂ (fun s : ℂ => deriv g s / g s) ρ
    exact AnalyticAt.div hg.deriv hg hgρ
  · let P : ℂ → ℂ := fun s => (s - ρ) ^ m * g s
    have hcong : logDeriv f =ᶠ[𝓝 ρ] logDeriv P := by
      exact logDeriv_congr_nhds (by simpa [P] using hfac)
    have hg_nz : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hgρ
    have hg_an : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hg.eventually_analyticAt
    have hdf1 : ∀ s : ℂ, DifferentiableAt ℂ (fun s => (s - ρ) ^ m) s := by
      intro s
      exact (AnalyticAt.pow (AnalyticAt.sub analyticAt_id analyticAt_const) m).differentiableAt
    have hld_aff : ∀ s : ℂ, s ≠ ρ → logDeriv (fun s => s - ρ) s = 1 / (s - ρ) := by
      intro s hsne
      unfold logDeriv
      have hd : deriv (fun s : ℂ => s - ρ) s = 1 := by
        simpa using ((hasDerivAt_id s).sub_const ρ).deriv
      change (deriv (fun s : ℂ => s - ρ) s) / (s - ρ) = 1 / (s - ρ)
      rw [hd]
    have hP_ld : ∀ᶠ s in 𝓝 ρ, s ≠ ρ →
        logDeriv P s = logDeriv (fun s => (s - ρ) ^ m) s + logDeriv g s := by
      filter_upwards [hg_nz, hg_an] with s hgne hga hsne
      unfold P
      rw [logDeriv_fun_mul (f := fun s => (s - ρ) ^ m) (g := g) s
        (pow_ne_zero m (sub_ne_zero.mpr hsne)) hgne (hdf1 s) hga.differentiableAt]
    have hP_pow : ∀ᶠ s in 𝓝 ρ, s ≠ ρ →
        logDeriv (fun s => (s - ρ) ^ m) s = m / (s - ρ) := by
      filter_upwards with s hsne
      have hdaff : DifferentiableAt ℂ (fun s : ℂ => s - ρ) s := by
        exact (AnalyticAt.sub analyticAt_id analyticAt_const).differentiableAt
      rw [logDeriv_fun_pow hdaff m, hld_aff s hsne]
      ring
    have hmain : ∀ᶠ s in 𝓝 ρ, s ≠ ρ →
        logDeriv f s - m / (s - ρ) = logDeriv g s := by
      filter_upwards [hcong, hP_ld, hP_pow] with s hsf hPld hPpow hsne
      calc
        logDeriv f s - m / (s - ρ) = logDeriv P s - m / (s - ρ) := by rw [hsf]
        _ = (logDeriv (fun s => (s - ρ) ^ m) s + logDeriv g s) - m / (s - ρ) := by
              rw [hPld hsne]
        _ = logDeriv g s := by
              rw [hPpow hsne]
              ring
    have h_ev : ∀ᶠ s in 𝓝[≠] ρ, logDeriv g s = logDeriv f s - m / (s - ρ) := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hmain] with s hs hsne
      exact (hs hsne).symm
    exact h_ev

end
end Commons.NumberTheory.Zeta