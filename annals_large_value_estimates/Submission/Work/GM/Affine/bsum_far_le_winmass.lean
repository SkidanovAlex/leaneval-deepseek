import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.far_sampling_crux_fixed
import Submission.Work.GM.Affine.winmass_reduction

/-!
# GM §9: the far mass of the `m₂`-sum is bounded by the window mass

Target:
`FarMass K f M₂ M₃ ≤ C * WinMass f M₂ M₃`, uniformly in `M₂ > 0`, `M₃ ≥ 1` and in the
continuous nonnegative `f` with `SuppHyp C₀ f`.

Route (all the analysis is in the imported modules):

* `far_mass_eq` / `win_mass_eq`: substituting `τ = M₃ t` turns the two sums over `ℓ` of
  `‖Bsum f M₂ (ℓ + τ/M₃)‖²` into `M₃` times an integral of the periodisation
  `G_A t = Σ'_ℓ ‖Bsum f M₂ (ℓ + t)‖²` — over `|t| > 2/M₃` with the weight `‖ψ̂₁(M₃ t)‖²`
  for `FarMass`, and over `|t| ≤ 2/M₃` unweighted for `WinMass`.
* `Bsum_periodization`: `G_A t = ∫_u ‖Σ_ℓ Hprof f M₂ (u+ℓ) · e(ℓt)‖² du`, i.e. `G_A` is the
  average, over the unit interval, of the modulus squared of a trigonometric polynomial with
  nonnegative coefficients `H ℓ = Hprof f M₂ (u+ℓ)`.
* `far_sampling_crux`: for every nonnegative finitely supported `H : ℤ → ℝ` and `M₃ ≥ 1`, the
  `‖ψ̂₁(M₃ ·)‖²`-weighted `L²` mass of `t ↦ Σ_ℓ H ℓ e(ℓt)` away from `|t| ≤ 2/M₃` is at most a
  constant (depending only on `K`) times its unweighted mass on that window.
* `winmass_reduction`: assembling the three identities above with the crux, applied at each
  `u ∈ [0,1]`, yields the target.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

theorem bsum_far_le_winmass {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f →
      (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      FarMass K f M₂ M₃ ≤ C * WinMass f M₂ M₃ := by
  obtain ⟨C, hCpos, hcrux⟩ := far_sampling_crux_fixed hK
  exact ⟨C, hCpos, winmass_reduction hC₀ hK hCpos hcrux⟩

end Work.GM.Affine
