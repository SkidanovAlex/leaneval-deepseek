import Mathlib
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_ne
import Submission.Work.Asymptotics.jDiff_lower_imagAxis

namespace Work.Asymptotics

open Filter
open scoped Topology

/-- **`j'` is bounded away from `0` near a non-elliptic point of the imaginary axis.**  For
`s₀ > 0` with `s₀ ≠ 1` (the only point of the imaginary axis that is `SL(2,ℤ)`-equivalent to an
elliptic point, where `jprime` vanishes), there are `η > 0` and `c > 0` such that
`c ≤ ‖j'(ζ)‖` for every `ζ : ℍ` with `‖ζ - i·s₀‖ < η`.

This is the uniform non-degeneracy input needed to apply the Lipschitz principal-part lemma
`Work.Asymptotics.Kfun_principal_part_z_lip` to the translate pole `z₀ = τ - n₀ ≈ i s₀` when
`τ` runs over a neighbourhood of the bad-line point `n₀ + i s₀`.

Proof route: `Work.Residues.jprime_ne_zero_iff` gives `jprime ζ = 0 ↔ E₄(ζ)·E₆(ζ) = 0`; the
imaginary axis meets the zero sets of `E₄` and `E₆` only at `t = 1`.  The workspace already has
this (`jDiff_lower_imagAxis.lean`: `E4Fun_imagAxis_ne_zero`, `E6Fun_imagAxis_ne_zero` — possibly
`private`, in which case re-derive them or re-export, e.g. from the theta representation
`E₄ = (U²+V²+W²)/2` with `U, V, W > 0` on the imaginary axis, resp. from the q-expansion of
`E₆`, whose coefficients are all negative, so that `E₆(it)` is strictly increasing with its
unique zero at `t = 1`; compare also `Work.Asymptotics.jInvariantFun_imagAxis_ne`).  With
`jprime (i s₀) ≠ 0` and `jprime` continuous (it is `MDiff`), take
`c := ‖jprime (i s₀)‖ / 2` and `η` from continuity. -/
theorem exists_jprime_lower_near_imagAxis {s₀ : ℝ} (hs₀ : 0 < s₀) (hne : s₀ ≠ 1) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - Complex.I * (s₀ : ℂ)‖ < η → c ≤ ‖Work.Residues.jprime ζ‖ := by
  -- The two-ball lower bound on the difference quotient of `j` at `z₀ = i s₀`
  -- (proved from `j' (z₀) ≠ 0`, i.e. from `E₄(z₀) ≠ 0` and `E₆(z₀) ≠ 0`).
  set z₀ : UpperHalfPlane := Work.Kernels.imagAxis s₀ hs₀ with hz₀
  have hcoe : (z₀ : ℂ) = Complex.I * (s₀ : ℂ) := by
    rw [hz₀]; simp [Work.Kernels.imagAxis, mul_comm]
  obtain ⟨ρ, c, hρ, hc, hb⟩ := jDiff_lower_imagAxis hs₀ hne
  refine ⟨ρ, c, hρ, hc, fun ζ hζ => ?_⟩
  have hζρ : ‖(ζ : ℂ) - (z₀ : ℂ)‖ < ρ := by rw [hcoe]; exact hζ
  -- Points close to `ζ` stay in the Euclidean ball used by `hb`.
  have hev_ball : ∀ᶠ (τ : UpperHalfPlane) in 𝓝 ζ, ‖(τ : ℂ) - (z₀ : ℂ)‖ < ρ := by
    have hopen : IsOpen {τ : UpperHalfPlane | ‖(τ : ℂ) - (z₀ : ℂ)‖ < ρ} :=
      isOpen_lt (continuous_norm.comp (UpperHalfPlane.continuous_coe.sub continuous_const))
        continuous_const
    exact hopen.mem_nhds hζρ
  -- Hence the difference quotient of `j` at `ζ` is bounded below by `c` near `ζ`.
  have hev : ∀ᶠ (τ : UpperHalfPlane) in 𝓝[≠] ζ,
      c ≤ ‖(Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun ζ) /
        ((τ : ℂ) - (ζ : ℂ))‖ := by
    have h1 : ∀ᶠ (τ : UpperHalfPlane) in 𝓝[≠] ζ, ‖(τ : ℂ) - (z₀ : ℂ)‖ < ρ :=
      hev_ball.filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, self_mem_nhdsWithin] with τ hτ hne'
    have hpos : 0 < ‖(τ : ℂ) - (ζ : ℂ)‖ := by
      rw [norm_pos_iff]
      intro h
      have h2 : (τ : ℂ) = (ζ : ℂ) := sub_eq_zero.mp h
      have h3 : τ = ζ := UpperHalfPlane.ext h2
      exact hne' (by simpa using h3)
    have hbnd := hb τ ζ hτ hζρ
    rw [norm_div, le_div_iff₀ hpos]
    exact hbnd
  -- Passing to the limit along `τ → ζ` gives `c ≤ ‖j' ζ‖`.
  exact ge_of_tendsto (Work.Residues.tendsto_slope_jprime ζ).norm hev

end Work.Asymptotics
