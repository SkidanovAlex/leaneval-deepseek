import Mathlib
import Submission.Work.OddVolterra.Defs

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-! ## The germ factorization of the radicand at the `y`-endpoint

At the right endpoint `t = y σ` of the section of slope `σ`, the profile value
`f (y σ)` agrees with the frozen line `line h σ (y σ)`, so the radicand
`ψ u (y σ) = f (y σ)² - line h u (y σ)²` factors through the two linear factors
`(σ - u)` and `(y σ + H(u,σ)) · (line h σ (y σ) + line h u (y σ))`.

This is the `y`-analogue of `psi_germ_factor` from the sibling file
`Submission.Work.OddVolterra.RowIdentity.odd_iteratedDeriv_momentF_eq_abel`; we
re-derive it here to keep this file self-contained. -/

/-- The factorization `ψ(u, y σ) = (σ - u) · ((y σ + H(u,σ)) · (L(σ, yσ) + L(u, yσ)))`
at the right endpoint, valid for every `u`. -/
theorem psi_y_germ_factor (h f y : ℝ → ℝ) (hh : ContDiff ℝ 1 h) {σ : ℝ}
    (hy : f (y σ) = σ * y σ + h σ) (u : ℝ) :
    psi h f u (y σ)
      = (σ - u) * ((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) := by
  have hlin : line h σ (y σ) - line h u (y σ) = (σ - u) * (y σ + hquot h u σ) := by
    have hq : h σ - h u = (σ - u) * hquot h u σ := sub_mul_hquot hh u σ
    rw [line, line]
    calc (σ * y σ + h σ) - (u * y σ + h u)
        = (σ - u) * y σ + (h σ - h u) := by ring
      _ = (σ - u) * y σ + (σ - u) * hquot h u σ := by rw [hq]
      _ = (σ - u) * (y σ + hquot h u σ) := by ring
  have hkey : psi h f u (y σ) = line h σ (y σ) ^ 2 - line h u (y σ) ^ 2 := by
    simp only [psi, line]
    rw [← hy]
  calc psi h f u (y σ)
      = (line h σ (y σ) - line h u (y σ)) * (line h σ (y σ) + line h u (y σ)) := by
        rw [hkey]; ring
    _ = (σ - u) * ((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) := by
        rw [hlin]; ring

/-! ## The germ of the moment integrand as a product of two half-integer powers -/

/-- Near `s`, where the second factor `Q(u,σ)` is positive and `u < σ`, the moment
integrand `ψ^n √ψ` coincides with the product `(σ - u)^{n+1/2} · Q(u,σ)^{n+1/2}`. -/
theorem yend_germ_rpow (n : ℕ) {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {s σ : ℝ} (hsσ : s < σ)
    (hy : f (y σ) = σ * y σ + h σ)
    (hQ : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε →
      0 < (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) :
    (fun u : ℝ => psi h f u (y σ) ^ n * Real.sqrt (psi h f u (y σ))) =ᶠ[𝓝 s]
      fun u : ℝ => (σ - u) ^ ((n : ℝ) + 1 / 2) *
        ((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) ^ ((n : ℝ) + 1 / 2) := by
  obtain ⟨ε, hε, hQε⟩ := hQ
  have hQev : ∀ᶠ u in 𝓝 s,
      0 < (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ)) := by
    rw [Metric.eventually_nhds_iff]
    exact ⟨ε, hε, fun u hu => hQε u (by simpa [Real.dist_eq] using hu)⟩
  have hlt : ∀ᶠ u in 𝓝 s, u < σ := isOpen_Iio.mem_nhds hsσ
  filter_upwards [hQev, hlt] with u hQu hltu
  have hσu : 0 ≤ σ - u := le_of_lt (sub_pos.mpr hltu)
  have hpsi := psi_y_germ_factor h f y hh hy u
  have hpsipos : 0 < psi h f u (y σ) := by
    rw [hpsi]; exact mul_pos (sub_pos.mpr hltu) hQu
  calc psi h f u (y σ) ^ n * Real.sqrt (psi h f u (y σ))
      = (psi h f u (y σ)) ^ ((n : ℝ) + 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (psi h f u (y σ)) n,
          ← Real.rpow_add hpsipos]
    _ = ((σ - u) * ((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))))
          ^ ((n : ℝ) + 1 / 2) := by rw [hpsi]
    _ = (σ - u) ^ ((n : ℝ) + 1 / 2) *
        ((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) ^ ((n : ℝ) + 1 / 2) :=
        Real.mul_rpow hσu (le_of_lt hQu)

/-- At the `y`-endpoint of the section of slope `σ`, the `(n+1)`-st derivative in `u` of the
moment integrand `u ↦ ψ(u,yσ)^n √ψ(u,yσ)` at `u = s` equals the `(n+1)`-st derivative of the
explicit fractional-power form `u ↦ (σ-u)^{n+1/2} · Q(u,σ)^{n+1/2}`, where
`Q(u,σ) = (yσ + hquot h u σ)·(line h σ (yσ) + line h u (yσ))` and `ψ(u,yσ) = (σ-u)·Q(u,σ)` (the
factorization `psi_germ_factor` of the sibling file).  The hypothesis `hQ` is eventual positivity
of `Q(·,σ)` near `s`, which makes `ψ(u,yσ) = (σ-u)Q(u,σ)` positive near `s` so that the two
integrands coincide near `s` (`Real.mul_rpow`), hence their `iteratedDeriv`s at `s` agree.

Definitions `psi`, `line`, `hquot` live in `Submission.Work.OddVolterra.Defs`; the sibling
`Submission.Work.OddVolterra.RowIdentity.odd_iteratedDeriv_momentF_eq_abel` proves the analogous
`iteratedDeriv` identity for the frozen-line radicand (`J1_div_sqrt_eq`) and the germ
factorization `psi_germ_factor` (both fully proved), and is a good model. -/
theorem yend_iteratedDeriv_eq_rpow (n : ℕ) {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {s σ : ℝ} (hsσ : s < σ)
    (hy : f (y σ) = σ * y σ + h σ)
    (hQ : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε →
      0 < (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) :
    iteratedDeriv (n + 1) (fun u : ℝ => psi h f u (y σ) ^ n * Real.sqrt (psi h f u (y σ))) s
      = iteratedDeriv (n + 1) (fun u : ℝ => (σ - u) ^ ((n : ℝ) + 1 / 2) *
          (((y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))) ^ ((n : ℝ) + 1 / 2))) s :=
  (yend_germ_rpow n hh hsσ hy hQ).iteratedDeriv_eq (n + 1)

end Work.OddVolterra.RowIdentity
