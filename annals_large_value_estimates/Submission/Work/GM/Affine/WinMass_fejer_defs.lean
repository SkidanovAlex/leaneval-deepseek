import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic

/-!
# Vocabulary for the direct route to `WinMass_core` (project lead's `WINMASS_ROUTE.md`)

* `fejerN M₃ = max 1 ⌊M₃/8⌋` : the Fejér order used to majorise the window count;
* `fejerK M₃ x = 1 + 2 ∑_{k=1}^{N-1} (1 - k/N) cos (2πkx)` (`N = fejerN M₃`) : the Fejér kernel,
  a non-negative `1`-periodic trig polynomial whose `k`-th cosine coefficient is `1 - |k|/N`;
  at `M₃ ≤ 8` it is `≡ 1`;
* `windowCount M₃ x = #{ℓ : ℤ | |x - ℓ| ≤ 2/M₃}` : the multiplicity of the window covering `x`.

The route (`L0`–`L7` of `WINMASS_ROUTE.md`) is
`WinMass ≤ 4π² ∫ ‖Bsum‖² · fejerK`, then the spectral expansion of `fejerK`, the near/far split
at `|x| = KT/M₃`, the domination `A = H * ρ` with `A(v) = Σ_m g_m(v/m)`, `g_m ≤ 4K f̃`, and the
tail from the decay hypothesis.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

/-- The Fejér order for the window count: `max 1 ⌊M₃/8⌋`. -/
def fejerN (M₃ : ℝ) : ℕ := max 1 ⌊M₃ / 8⌋₊

/-- The Fejér kernel `F(x) = 1 + 2 ∑_{k=1}^{N-1} (1 - k/N) cos (2π k x)`, `N = fejerN M₃`. -/
def fejerK (M₃ x : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.Icc 1 (fejerN M₃ - 1),
    (1 - (k : ℝ) / (fejerN M₃)) * Real.cos (2 * Real.pi * k * x)

/-- The window count `N(x) = #{ℓ : ℤ | |x - ℓ| ≤ 2/M₃}`. -/
def windowCount (M₃ x : ℝ) : ℕ :=
  ((Finset.Icc ⌈x - 2 / M₃⌉ ⌊x + 2 / M₃⌋).filter (fun ℓ : ℤ => |x - (ℓ : ℝ)| ≤ 2 / M₃)).card

lemma fejerN_pos (M₃ : ℝ) : 1 ≤ fejerN M₃ := le_max_left _ _

lemma one_le_fejerN (M₃ : ℝ) : (1 : ℝ) ≤ (fejerN M₃ : ℝ) := by
  exact_mod_cast fejerN_pos M₃

end

end Work.GM.Affine
