import Mathlib

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory
open scoped Topology
open Filter

/-- **The zeros of `Λ = completedRiemannZeta` in the closed critical strip are exactly the zeros
of `ζ` there, with multiplicity.**  For `1/2 ≤ Re ρ ≤ 1` the vanishing order of the completed zeta
function at `ρ` is non-zero if and only if `riemannZeta ρ = 0`.  (`Λ(s) = π^{-s/2}Γ(s/2)ζ(s)`, and
the Euler factor `π^{-s/2}Γ(s/2)` is analytic and non-vanishing for `re s > 0`.) -/
theorem zetaZeroBridge (ρ : ℂ) (h0 : (1 : ℝ) / 2 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    analyticOrderNatAt completedRiemannZeta ρ ≠ 0 ↔ riemannZeta ρ = 0 := by
  -- `ρ` lies in the open right half-plane, so in particular `ρ ≠ 0`.
  have hρ0 : ρ ≠ 0 := by
    intro h
    have hre : ρ.re = 0 := by rw [h]; simp
    rw [hre] at h0
    norm_num at h0
  have hρre : 0 < ρ.re := lt_of_lt_of_le (by norm_num) h0
  constructor
  · -- Forward: a zero of `Λ` is a zero of `ζ` (as `Λ = Γℝ · ζ` away from `0`).
    intro hord
    have hΛ : completedRiemannZeta ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
    rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]
  · -- Backward: a zero of `ζ` is a zero of `Λ`, with the same multiplicity.
    intro hζ
    rcases eq_or_ne ρ 1 with rfl | hρ1
    · -- `ρ = 1` is the junk-value case: `Λ` has a pole there, and `ζ 1 ≠ 0`.
      exact absurd hζ riemannZeta_one_ne_zero
    · have hρc : ρ ∈ ({1}ᶜ : Set ℂ) := by simpa using hρ1
      have hζan : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρc
      -- `ζ` is not identically zero near `ρ` (it has value `π²/6 ≠ 0` at `2`, and `{1}ᶜ` is
      -- preconnected), so its vanishing order at `ρ` is finite.
      have hne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
        intro htop
        have hloc : riemannZeta =ᶠ[𝓝 ρ] fun _ => (0 : ℂ) := by
          filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
          simpa using hz
        have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
          (𝕜 := ℂ) (f := riemannZeta) (g := fun _ => (0 : ℂ)) (U := ({1}ᶜ : Set ℂ))
          analyticOn_riemannZeta analyticOnNhd_const
          (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected hρc hloc
        have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
        have h2' : riemannZeta 2 = 0 := by simpa using heq h2
        exact absurd h2' (riemannZeta_ne_zero_of_one_le_re (s := (2 : ℂ)) (by norm_num))
      -- the order of `ζ` at `ρ` is a positive natural number
      have hne_zero : analyticOrderAt riemannZeta ρ ≠ 0 := hζan.analyticOrderAt_ne_zero.mpr hζ
      -- analyticity of `Λ` at `ρ` (where `ρ ≠ 0, 1`)
      have hΛan : AnalyticAt ℂ completedRiemannZeta ρ := by
        refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
        filter_upwards [eventually_ne_nhds hρ0, isOpen_ne.mem_nhds hρ1] with z hz0 hz1
        exact differentiableAt_completedZeta hz0 hz1
      have hΓρ : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hρre
      -- `(Γℝ)⁻¹` is entire, so we may factor `ζ = (Γℝ)⁻¹ * Λ` near `ρ`
      have hΓinv_an : AnalyticAt ℂ (fun z => (Complex.Gammaℝ z)⁻¹) ρ :=
        Complex.differentiable_Gammaℝ_inv.analyticAt ρ
      have hζeq : riemannZeta =ᶠ[𝓝 ρ] (fun z => (Complex.Gammaℝ z)⁻¹) * completedRiemannZeta := by
        filter_upwards [eventually_ne_nhds hρ0] with z hz
        simp only [Pi.mul_apply]
        rw [riemannZeta_def_of_ne_zero hz, div_eq_inv_mul]
      have hΓinv0 : analyticOrderAt (fun z => (Complex.Gammaℝ z)⁻¹) ρ = 0 :=
        hΓinv_an.analyticOrderAt_eq_zero.mpr (inv_ne_zero hΓρ)
      -- multiplicativity of the vanishing order
      have hord : analyticOrderAt riemannZeta ρ = analyticOrderAt completedRiemannZeta ρ := by
        rw [analyticOrderAt_congr hζeq,
          analyticOrderAt_mul hΓinv_an hΛan, hΓinv0, zero_add]
      have hΛne_top : analyticOrderAt completedRiemannZeta ρ ≠ ⊤ := hord ▸ hne_top
      have hnatζ : analyticOrderNatAt riemannZeta ρ ≠ 0 := by
        intro h
        have h' : (analyticOrderNatAt riemannZeta ρ : ℕ∞) = 0 := by rw [h]; rfl
        rw [Nat.cast_analyticOrderNatAt hne_top] at h'
        exact hne_zero h'
      have hnat_eq : analyticOrderNatAt completedRiemannZeta ρ = analyticOrderNatAt riemannZeta ρ := by
        apply Nat.cast_injective (R := ℕ∞)
        rw [Nat.cast_analyticOrderNatAt hΛne_top, Nat.cast_analyticOrderNatAt hne_top, hord]
      rw [hnat_eq]
      exact hnatζ

end Work.ZeroDensity.Ingham
