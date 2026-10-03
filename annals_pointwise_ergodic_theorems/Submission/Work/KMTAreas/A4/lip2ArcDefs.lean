/-
# Definitions for the single-arc extraction `Work.KMTAreas.A4.lip2ArcExtract`

This module fixes the vocabulary shared by `Work.KMTAreas.A4.lip2ArcExtract` and the
delegated lemmas about it: the smooth, compactly supported **tiling bump** `arcChi` with
`Σ_m arcChi (u - m) = 1`, and the **window kernel** `arcWin` at scale `N` centred at a real
frequency `s`.

## The objects

* `arcBump0 u = lipSchChi (4u/3)` — the rescaled bump, `1` for `|u| ≤ 3/8` and `0` off `(-3/4,3/4)`;
* `arcTileH u = Σ_m arcBump0 (u - m)` — its periodization (a `1`-periodic, strictly positive
  smooth function);
* `arcChi u = arcBump0 u / arcTileH u` — the *tiling bump*: smooth, compactly supported in
  `[-3/4,3/4]`, and tiling in the sense `Σ_m arcChi (u - m) = 1`;
* `arcWin ψ N s m = N⁻¹ ψ(m/N) e(m s)` — the window kernel at scale `N` centred at `s`, whose
  `ℤ`-Fourier transform is the periodized bump `Σ_n (𝓕ψ)(N(t - s + n))` (Poisson summation),
  and which is a reproducing kernel when `𝓕ψ = arcChi` (see `Work.KMTAreas.A4.arcWinPoisson`).

The point of the tiling bump (as opposed to a plain bump) is that the **sums of the window
symbols over a full grid of scale `1/N` telescope**: `Σ_{j<N} Σ_n arcChi (N(t - j/N + n)) = 1`,
which is what makes the partition argument of `lip2ArcExtract` exact.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipSchwartzExists

set_option autoImplicit false

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The rescaled bump `χ₀(u) = lipSchChi (4u/3)`: `1` for `|u| ≤ 3/8` and `0` for `|u| ≥ 3/4`. -/
noncomputable def arcBump0 (u : ℝ) : ℂ := lipSchChi (u * (4 / 3))

/-- The periodization `H(u) = Σ_m χ₀(u - m)` of `arcBump0`: a `1`-periodic, strictly positive,
smooth function of `u`. -/
noncomputable def arcTileH (u : ℝ) : ℂ := ∑' m : ℤ, arcBump0 (u - (m : ℝ))

/-- The **tiling bump** `χ̃ = χ₀ / H`: smooth, compactly supported in `[-3/4,3/4]`, even, and
satisfying the exact tiling `Σ_m χ̃(u - m) = 1`. -/
noncomputable def arcChi (u : ℝ) : ℂ := arcBump0 u / arcTileH u

/-- The window kernel at scale `N` centred at the real frequency `s`:
`arcWin ψ N s m = N⁻¹ ψ(m/N) e(m s)`.  For `𝓕ψ = arcChi` this is the kernel whose Fourier
transform is the periodized bump `t ↦ Σ_n arcChi (N (t - s + n))`. -/
noncomputable def arcWin (ψ : SchwartzR) (N : ℕ) (s : ℝ) : ℤ → ℂ :=
  fun m => ((N : ℂ)⁻¹) * (ψ ((m : ℝ) / (N : ℝ))) * (fourier m ((s : ℝ) : FreqCircle) : ℂ)

end Work.KMTAreas.A4
