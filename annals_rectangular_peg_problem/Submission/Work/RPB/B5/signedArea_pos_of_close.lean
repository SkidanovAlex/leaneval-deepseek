import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.pos_area_of_close_family

/-!
# B5: positivity of the signed area is open in the `C¹` topology (uniform in the family)

`Work.RPB.B5.signedArea_pos_of_close`: let `γ : ℝ → ℝ → ℂ` be a family of curves whose slices
`t ↦ γ τ t`, `τ ∈ [0,1]`, are `C¹`, with `‖γ τ t‖ ≤ M` and `‖deriv (γ τ) t‖ ≤ M` for all `t`, and
suppose that the signed areas of the slices are *uniformly* bounded below by some `a > 0`.  Then
there is a single `ε > 0` such that every `C¹` curve `c` which is `ε`-close to some slice `γ τ` in
the uniform `C¹` norm (`‖c t - γ τ t‖ < ε` and `‖deriv c t - deriv (γ τ) t‖ < ε` for *all* `t`)
has positive signed area.

This is the version of `Work.RPB.B5.pos_area_of_close_family` that the B5 assembly needs: no
*joint* smoothness of `γ` in `(τ,t)` is assumed (only slicewise `C¹`), and the uniform positive
lower bound on the areas is a hypothesis rather than being extracted from compactness of `[0,1]`.
Consequently no continuity of `τ ↦ signedArea (γ τ)` is used at all.

## Proof

The estimate is the one of `Work.RPB.B5.signedArea_close_bound`, applied to the slice
`g = γ τ` and the perturbation `η = c - γ τ`:

`ω_ℂ (c, c') - ω_ℂ (g, g') = ω_ℂ (c - g, c') + ω_ℂ (g, c' - g')`,

and pointwise `|ω_ℂ (u,v)| ≤ ‖u‖ ‖v‖` bounds this by
`ε ‖c'‖ + M ε ≤ ε (M + ε) + M ε = 2Mε + ε²` (using `‖c' t‖ ≤ M + ε`).  Integrating over `[0,2π]`
and halving gives

`signedArea c ≥ signedArea g - π (2Mε + ε²) ≥ a - π (2Mε + ε²)`,

which is positive as soon as `π (2Mε + ε²) < a`.  The explicit choice

`ε = min 1 (a / (4π(M+1)))`

achieves this: `ε² ≤ ε` and `2ε (M+1) · (2π) ≤ a/2` give `π (2Mε + ε²) ≤ 2π ε (M+1) ≤ a/2 < a`.
-/

open MeasureTheory intervalIntegral
open scoped Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem signedArea_pos_of_close (γ : ℝ → ℝ → ℂ) (M : ℝ) (hM : 0 < M)
    (hC1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ContDiff ℝ 1 (fun t : ℝ => γ τ t))
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖γ τ t‖ ≤ M)
    (hb' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖deriv (fun t : ℝ => γ τ t) t‖ ≤ M)
    (hpos : ∃ a : ℝ, 0 < a ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      a ≤ Work.RPB.signedArea (fun t : ℝ => γ τ t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ c : ℝ → ℂ, ContDiff ℝ 1 c →
      (∀ t : ℝ, ‖c t - γ τ t‖ < ε) →
      (∀ t : ℝ, ‖deriv c t - deriv (fun t : ℝ => γ τ t) t‖ < ε) →
      0 < Work.RPB.signedArea c := by
  obtain ⟨a, ha, hlea⟩ := hpos
  have hden : 0 < 4 * Real.pi * (M + 1) := by positivity
  set ε : ℝ := min 1 (a / (4 * Real.pi * (M + 1))) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min one_pos (by positivity)
  have hεle1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεlem : ε * (4 * Real.pi * (M + 1)) ≤ a := by
    rw [hεdef]
    calc min 1 (a / (4 * Real.pi * (M + 1))) * (4 * Real.pi * (M + 1))
        ≤ (a / (4 * Real.pi * (M + 1))) * (4 * Real.pi * (M + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hden)
      _ = a := by field_simp
  refine ⟨ε, hεpos, ?_⟩
  intro τ hτ c hc hc1 hc2
  -- the slice of the family and the perturbation
  set g : ℝ → ℂ := fun t : ℝ => γ τ t with hgdef
  set η : ℝ → ℂ := fun t : ℝ => c t - g t with hηdef
  have hg : ContDiff ℝ 1 g := hC1 τ hτ
  have hη : ContDiff ℝ 1 η := hc.sub hg
  have hηd : ∀ t : ℝ, deriv η t = deriv c t - deriv g t := fun t =>
    deriv_sub (hc.differentiable (by norm_num) t) (hg.differentiable (by norm_num) t)
  have h1 : ∀ t : ℝ, ‖η t‖ < ε := by
    intro t
    rw [hηdef, hgdef, hεdef]
    exact hc1 t
  have h2 : ∀ t : ℝ, ‖deriv η t‖ < ε := by
    intro t
    rw [hηd t, hgdef, hεdef]
    exact hc2 t
  -- the perturbed curve is `c`
  have hsum : g + η = c := by
    funext t
    simp only [Pi.add_apply, hηdef, hgdef]
    ring

  -- the `C¹`-stability estimate for the signed area
  have hcore := signedArea_close_bound g η hg hη M ε
    (fun t => hb τ hτ t) (fun t => hb' τ hτ t) h1 h2
  rw [hsum] at hcore
  -- the explicit constant is small enough
  have hεsq : ε ^ 2 ≤ ε := by nlinarith [hεpos, hεle1]
  have hsmall : Real.pi * (2 * M * ε + ε ^ 2) < a := by
    have h4 : 2 * Real.pi * (M + 1) * ε ≤ a / 2 := by
      have h45 : 2 * Real.pi * (M + 1) * ε = (ε * (4 * Real.pi * (M + 1))) / 2 := by ring
      rw [h45]; linarith
    have h5 : Real.pi * (2 * M * ε + ε ^ 2) ≤ 2 * Real.pi * (M + 1) * ε := by
      nlinarith [Real.pi_pos, hεsq, hεpos, hM]
    linarith
  have hτa : a ≤ Work.RPB.signedArea g := hlea τ hτ
  linarith

end Work.RPB.B5
