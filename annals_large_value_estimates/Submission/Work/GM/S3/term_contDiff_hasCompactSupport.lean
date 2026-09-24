import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.hhat_defs
import Submission.Work.GM.S3.hfun_contDiff_compactSupport

/-!
# `u ↦ ψ₁(u+w) ψ₂ u · u^{iτ}` is `C^∞` with compact support

For `IsBumpAtOne ψ₁ C₀`, `IsBumpAtOne ψ₂ C₀` with `1 ≤ C₀`, the function
`u ↦ (ψ₁ (u+w) * ψ₂ u : ℂ) * phi τ u` is smooth and compactly supported.

Route (mirroring `hfun_contDiff`/`hfun_hasCompactSupport`):

* the product `g u = (ψ₁ (u+w) * ψ₂ u : ℂ)` is globally smooth (`hg`);
* `g` vanishes identically on the open half-line `u < 1/C₀` (because `ψ₂ u ≠ 0` forces
  `u ∈ [1/C₀, C₀]`), so `F = g * phi τ` is *eventually* `0` at every `u < 1/C₀`, hence
  smooth there; at `u ≥ 1/C₀ > 0` both factors are smooth, using `contDiffAt_phi`;
* `F x = 0` for `x ∉ [1/C₀, C₀]`, so the support is contained in the compact interval
  `[1/C₀, C₀]`.
-/

namespace Work.GM.S3

open Complex
open scoped Topology

theorem term_contDiff_hasCompactSupport (ψ₁ ψ₂ : ℝ → ℝ) (C₀ : ℝ) (hC₀ : 1 ≤ C₀)
    (h₁ : IsBumpAtOne ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀) (w τ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u) ∧
      HasCompactSupport (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u) := by
  have hCpos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hinvpos : 0 < 1 / C₀ := one_div_pos.mpr hCpos
  set F : ℝ → ℂ := fun u => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ) * phi τ u with hF
  have hψ2zero : ∀ x : ℝ, x ∉ Set.Icc (1 / C₀) C₀ → ψ₂ x = 0 := by
    intro x hx
    by_contra h
    exact hx (h₂.2.2.1 x h)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ((ψ₁ (u + w) * ψ₂ u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((h₁.1.comp (contDiff_id.add contDiff_const)).mul h₂.1)
  have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    rw [contDiff_iff_contDiffAt]
    intro u
    rcases lt_or_ge u (1 / C₀) with hu | hu
    · have hev : F =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
        filter_upwards [isOpen_Iio.mem_nhds hu] with x hx
        have hx' : x ∉ Set.Icc (1 / C₀) C₀ := by
          simp only [Set.mem_Iio] at hx
          intro h; linarith [h.1]
        rw [hF]
        simp [hψ2zero x hx']
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hev
    · have hupos : 0 < u := lt_of_lt_of_le hinvpos hu
      exact hg.contDiffAt.mul (contDiffAt_phi τ hupos)
  refine ⟨hFcd, ?_⟩
  rw [hF]
  refine HasCompactSupport.intro (K := Set.Icc (1 / C₀) C₀) isCompact_Icc (fun x hx => ?_)
  simp [hψ2zero x hx]

end Work.GM.S3
