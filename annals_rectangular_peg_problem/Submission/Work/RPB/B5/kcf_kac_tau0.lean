import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kA0_spec

namespace Work.RPB.B5

theorem kcf_kac_tau0 (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ)
    (hsl : ∀ σ : ℝ, -(δ / 4) < σ → ∀ t : ℝ,
      Work.RPB.B5.kgam CI W ρh δ k 0 σ t = Work.RPB.B5.ktarg δ k σ t)
    (hflux : ∀ σ : ℝ, 0 ≤ σ → ∀ u : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k s u) σ)
        (deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k σ s) u) = 1) :
    ∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ,
      Work.RPB.B5.kac CI W ρh δ k 0 σ t
        = t + Work.RPB.B5.kphc δ k σ + Real.pi / 2 + 2 * Real.pi * (k : ℝ) := by
  intro σ hσ t
  -- `σ ≥ 0 > -δ/4`: the `τ = 0` slice of `kgam` agrees with the target circle near `σ`
  have hlt : -(δ / 4) < σ := by linarith
  -- the flux integrand is identically `1` along the `τ = 0` slice
  have hint : (∫ u in (0 : ℝ)..t,
      Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 s u) σ)
        (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 σ s) u)) = t := by
    have hfun : ∀ u : ℝ,
        Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 s u) σ)
          (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 σ s) u) = 1 := by
      intro u
      -- `σ`-derivative: `kgam` agrees with `ktarg` on a neighbourhood of `σ`
      have h1 : deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 s u) σ
          = deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k s u) σ := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [Ioi_mem_nhds hlt] with s hs
        exact hsl s hs u
      -- `t`-derivative: the two curves coincide for *all* parameters
      have h2 : deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 σ s) u
          = deriv (fun s : ℝ => Work.RPB.B5.ktarg δ k σ s) u := by
        rw [show (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 σ s)
            = (fun s : ℝ => Work.RPB.B5.ktarg δ k σ s) from
          funext (fun x => hsl σ hlt x)]
      rw [h1, h2]
      exact hflux σ hσ u
    rw [show (fun u : ℝ =>
        Work.RPV.ωC (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 s u) σ)
          (deriv (fun s : ℝ => Work.RPB.B5.kgam CI W ρh δ k 0 σ s) u)) = fun _ => (1 : ℝ) from
      funext hfun]
    simp
  unfold Work.RPB.B5.kac
  rw [Work.RPB.B5.kA0_tau_zero, hint]
  ring

end Work.RPB.B5
