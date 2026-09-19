import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Zeta.logDeriv_sub_pole_analyticAt
import Submission.Commons.NumberTheory.Zeta.xiE_noZero_ball

open Filter
open scoped Topology

namespace Commons.NumberTheory.Zeta

noncomputable section

/-- `riemannZeta₁` is not eventually zero at any point (it is entire and non-identically
zero: `riemannZeta₁ 1 = 1`), so every zero is isolated with a well-defined finite
multiplicity. -/
lemma riemannZeta₁_not_eventually_zero (ρ : ℂ) : ¬(riemannZeta₁ =ᶠ[𝓝 ρ] 0) := by
  intro hz
  have hAn : AnalyticOnNhd ℂ riemannZeta₁ (Set.univ : Set ℂ) := by
    intro z hzmem
    exact differentiable_riemannZeta₁.analyticAt z
  have hzeroAn : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) (Set.univ : Set ℂ) := by
    intro z hzmem
    exact analyticAt_const
  have hz' : ∀ᶠ z in 𝓝 ρ, riemannZeta₁ z = 0 := by
    simpa [Filter.EventuallyEq] using hz
  have hev : ∀ᶠ z in 𝓝[{ρ}ᶜ] ρ, riemannZeta₁ z = 0 := hz'.filter_mono nhdsWithin_le_nhds
  have hfw : ∃ᶠ z in 𝓝[{ρ}ᶜ] ρ, riemannZeta₁ z = 0 := hev.frequently
  have hEq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hAn hzeroAn
    (PreconnectedSpace.isPreconnected_univ (α := ℂ)) (by simp : ρ ∈ (Set.univ : Set ℂ)) hfw
  have h1 : riemannZeta₁ 1 = (0 : ℂ) := hEq (by simp)
  exact zero_ne_one (h1.symm.trans riemannZeta₁_one)

/-- At a zero `ρ` of `riemannZeta₁` of (finite, ≥ 1) multiplicity `m`, the log-derivative
pole is removable: `riemannZeta₁′/riemannZeta₁ − m/(s−ρ)` extends analytically through `ρ`. -/
theorem zeta1_logDeriv_pole_removal (ρ : ℂ) (hρ : riemannZeta₁ ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ρ ∧
      Filter.Eventually (fun s => F s = logDeriv riemannZeta₁ s - m / (s - ρ))
        (nhdsWithin ρ {s : ℂ | s ≠ ρ}) := by
  have hAn : AnalyticAt ℂ riemannZeta₁ ρ := differentiable_riemannZeta₁.analyticAt ρ
  have hnot : ¬(riemannZeta₁ =ᶠ[𝓝 ρ] 0) := riemannZeta₁_not_eventually_zero ρ
  rcases (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hAn).mpr hnot with ⟨n, g, hg, hgρ, hfac⟩
  have hn1 : 1 ≤ n := by
    by_contra hn0
    have hnz : n = 0 := by omega
    have hfacE : ∀ᶠ z in 𝓝 ρ, riemannZeta₁ z = (z - ρ) ^ n * g z := by
      simpa [Filter.EventuallyEq] using hfac
    subst n
    have hfac0E : ∀ᶠ z in 𝓝 ρ, riemannZeta₁ z = g z := hfacE.mono (by
      intro z hz
      simpa using hz)
    have hρg : riemannZeta₁ ρ = g ρ := hfac0E.self_of_nhds
    exact hgρ (hρg.symm.trans hρ)
  have hcore := logDeriv_sub_pole_analyticAt (f := riemannZeta₁) (g := g) (ρ := ρ) (m := n)
    hAn hρ hg hgρ hfac hn1
  rcases hcore with ⟨F, hF, hEv⟩
  exact ⟨n, hn1, F, hF, hEv⟩

end
end Commons.NumberTheory.Zeta