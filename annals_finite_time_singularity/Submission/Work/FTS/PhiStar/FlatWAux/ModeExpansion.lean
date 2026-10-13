/-
# `Work.FTS.PhiStar.FlatWAux.ModeExpansion` — the mode expansion of `psiSeries α (RemSource α ψ)`

`RemSource α ψ = fun z θ => α²·(𝒜φ)(z)·ψ(θ)` is separable, so the `m`-th mode coefficient of the
`z`-slice is `α²(𝒜φ)(z)` times the `z`-independent coefficient `b_m = bmode m ψ`, and `radGreen`
is linear in its source.  Hence

`psiSeries α (RemSource α ψ) z θ = α² Σ_m b_m · radGreen α m (𝒜φ)(z) · eFam m θ`,

the mode expansion on which the flat estimate of `PhiStar/FlatW_psiSeries.lean` runs.  The
consequence used there (`bmode_zero_of_moment`) is that for an `AngModel` the kernel coefficient
`b_0` vanishes, so the `λ_m = 0` mode never contributes.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.acoeff_zero_of_fstar
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- `radGreen` only depends on the source through its values. -/
theorem radGreen_congr (α : ℝ) (m : ℕ) {c c' : ℝ → ℝ} (h : ∀ t, c t = c' t) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z = Work.FTS.PhiStar.Radial.radGreen α m c' z := by
  have h1 : (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = ∫ t in (0 : ℝ)..z, c' t * t ^ ((2 * (m : ℝ) + 5) / α - 1) :=
    intervalIntegral.integral_congr (fun t _ => by rw [h t])
  have h2 : (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      = ∫ t in Set.Ioi z, c' t * t ^ (-(2 * (m : ℝ) / α) - 1) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by simp only [h t]))
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]

/-- `radGreen` is linear in its source. -/
theorem radGreen_const_mul (α : ℝ) (m : ℕ) (k : ℝ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun t => k * c t) z
      = k * Work.FTS.PhiStar.Radial.radGreen α m c z := by
  have h1 : (∫ t in (0 : ℝ)..z, (k * c t) * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      = k * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have h2 : (∫ t in Set.Ioi z, (k * c t) * t ^ (-(2 * (m : ℝ) / α) - 1))
      = k * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  simp only [Work.FTS.PhiStar.Radial.radGreen, h1, h2]
  ring

/-- The `m`-th slice coefficient of the separable source `RemSource α ψ`. -/
theorem cmode_remSource (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) t
      = (α ^ 2 * Work.FTS.VocabO.phiA α t)
          * Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0 := by
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        α ^ 2 * Work.FTS.VocabO.phiA α t * ψ θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = (α ^ 2 * Work.FTS.VocabO.phiA α t)
        * (∫ θ in (0 : ℝ)..(Real.pi / 2),
            ψ θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun θ _ => by ring)
  simp only [Work.FTS.PhiStar.Series.cmode, Work.FTS.PhiStar.RemSource]
  rw [hnum]
  ring

/-- **The mode expansion of the remainder series.** -/
theorem psiSeries_remSource_eq_tsum (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ
      = α ^ 2 * ∑' m : ℕ,
          Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * (Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hterm : ∀ m : ℕ,
      Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ
        = α ^ 2 * (Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
            * (Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    intro m
    have hfun : (fun t => Work.FTS.PhiStar.Series.cmode m
          (Work.FTS.PhiStar.RemSource α ψ) t)
        = fun t => (α ^ 2 * Work.FTS.VocabO.phiA α t)
            * (Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0) := by
      funext t
      exact cmode_remSource α ψ m t
    change Work.FTS.PhiStar.Radial.radGreen α m
        (fun t => Work.FTS.PhiStar.Series.cmode m
          (Work.FTS.PhiStar.RemSource α ψ) t) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ = _
    rw [hfun]
    rw [radGreen_congr α m
        (c' := fun t => (α ^ 2 * Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0)
            * Work.FTS.VocabO.phiA α t) (fun t => by ring) z, radGreen_const_mul]
    ring
  rw [Work.FTS.PhiStar.Series.psiSeries]
  rw [tsum_congr hterm]
  rw [tsum_mul_left]

/-- For an `AngModel` the kernel mode coefficient `bmode 0 ψ` vanishes. -/
theorem bmode_zero_of_moment {ψ : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  have h := Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact h

end Work.FTS.PhiStar.FlatWAux
