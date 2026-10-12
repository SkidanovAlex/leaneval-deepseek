import ChallengeDeps
import Submission.Q0Chosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — pointwise relations among the χ-renormalized kernels

FS `eq:defW_12` defines the renormalized kernels through the scattering
solution `ω`:

    W₁ = W(1−ω)  (numerator `g₀ = v(1−ω₀)`),   W₂ = W(1−ω²)  (numerator `g₂`),

so with the corpus kernels `wPair(ℓ,h)(x,y) := χ_ℓ(x)·h(x−y)/(χ⋆χ)_ℓ(x−y)·χ_ℓ(y)`
(KernelIds.wPair, numerator `h`) the pointwise relations hold exactly (total
functions; division by zero yields `0`, and the denominators agree on the
supports where numerators do not vanish):

    wPair(ℓ,g₀)(x,y) = wPair(ℓ,v)(x,y)·(1 − ω(x−y))                (w1_eq_w_mul)
    wPair(ℓ,g₂)(x,y) = wPair(ℓ,v)(x,y)·(1 − ω(x−y)²)               (w2_eq_w_mul)

with `ω := w₀ = Classical.choose h` the chosen scattering solution,
`g₀ := v(1−w₀)`, `g₂ := g₀(1+w₀)` (ScatKernelChosen).  These are the only
kernel relations needed to transcribe the FS potential splitting
(`lem:potsplit eq:potsplit`) in corpus language: every occurrence of
`ω(x−y)·wPair(ℓ,v)(x,y)` can be read as
`wPair(ℓ,v)(x,y) − wPair(ℓ,g₀)(x,y)`, and
`ω²·wPair(v) = wPair(v) − wPair(g₂)`.

## Route notes (for the child)

* `wPair ℓ h x y = chiScale ℓ x · chiScale ℓ y · wScaled ℓ h (x−y)` and
  `wScaled ℓ h z = h z / convScale ℓ z`; use the pointwise equalities
  `g₀ z = v z·(1 − w₀ z)` (`ScatKernelChosen.g0`), `g₂ z = g₀ z·(1+w₀ z)`,
  the total-division identity `(a·(1−ω))/C = (a/C)·(1−ω)` (ring) and
  `ring`/`field_simp`-free algebra on reals (division is `·C⁻¹`, so plain
  ring works).
* State with the standing chosen-branch hypotheses `(h : ∃ w, IsRadial w ∧
  IsScatteringSolution w v)`; write `w₀ := Classical.choose h` internally
  (`w0_spec` gives radiality/solution, only radiality used here).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **w₁ = w·(1−ω) pointwise**: `wPair(g₀)(x,y) = wPair(v)(x,y)·(1−ω(x−y))`. -/
lemma w1_eq_w_mul_one_sub {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) (x y : ℝ³) :
    wPair ℓ (g0 v h) x y = wPair ℓ v x y * (1 - Classical.choose h (x - y)) := by
  simp [wPair, wScaled, g0]
  ring


/-- **w₂ = w·(1−ω²) pointwise**: `wPair(g₂)(x,y) = wPair(v)(x,y)·(1−ω(x−y)²)`. -/
lemma w2_eq_w_mul_one_sub_sq {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) (x y : ℝ³) :
    wPair ℓ (g2 v h) x y = wPair ℓ v x y * (1 - (Classical.choose h (x - y)) ^ 2) := by
  simp [wPair, wScaled, g2]
  ring


/-- Equivalent form: `wPair(g₂) = wPair(g₀)·(1+ω)` pointwise (used to move
between the `w₂` and `w₁` kernels). -/
lemma w2_eq_w1_mul_one_add {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) (x y : ℝ³) :
    wPair ℓ (g2 v h) x y = wPair ℓ (g0 v h) x y * (1 + Classical.choose h (x - y)) := by
  simp [wPair, wScaled, g0, g2]
  ring


/-- `ω·w = w − w₁` pointwise (the form used to eliminate `ω·wPair(v)`). -/
lemma w_mul_omega_eq_sub_w1 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) (x y : ℝ³) :
    wPair ℓ v x y * Classical.choose h (x - y) = wPair ℓ v x y - wPair ℓ (g0 v h) x y := by
  simp [wPair, wScaled, g0]
  ring


/-- `ω²·w = w − w₂` pointwise. -/
lemma w_mul_omega_sq_eq_sub_w2 {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) (x y : ℝ³) :
    wPair ℓ v x y * (Classical.choose h (x - y)) ^ 2 =
      wPair ℓ v x y - wPair ℓ (g2 v h) x y := by
  simp [wPair, wScaled, g2]
  ring


end BoseGases

end Submission
