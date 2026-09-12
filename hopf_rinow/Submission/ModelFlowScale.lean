import Submission.Model
import Submission.ModelCore
import Submission.ModelAlg
import Submission.ModelScale
import Submission.ModelUniq
import Mathlib

/-!
# Scaling identity for the model geodesic flow

Task: prove the final theorem `flow_scaling` (replace the placeholder proof).

Statement (in words): if `(c₁, vel₁)` is a geodesic with initial position/velocity `(x, v)` on
`Ioo (-ε₁) ε₁`, and `(c₂, vel₂)` is a geodesic with initial data `(x, s • v)` on
`Ioo (-ε₂) ε₂` (`s ≠ 0`), then on the common interval the two agree under time rescaling:

    ∀ t, |t| < min ε₂ (ε₁ / |s|)  →  c₂ t = c₁ (s * t)   ∧   vel₂ t = s • vel₁ (s * t)

## Proof route (all ingredients are verified in the imported modules)

1. `Submission.Model.geodesic_rescale` (ModelScale.lean): the rescaled curve
   `u ↦ c₁ (s*u)` with velocity `u ↦ s • vel₁ (s*u)` is a geodesic (with initial data
   `(x, s•v)`) on `Ioo (-ε₁/|s|) (ε₁/|s|)`.
2. `Submission.Model.unique_geodesic` (ModelUniq.lean): two geodesics with the same initial
   data agree on their common interval.  Apply it to the rescaled `(c₁,vel₁)` (on
   `Ioo (-ε₁/|s|) (ε₁/|s|)`) and to `(c₂,vel₂)` (on `Ioo (-ε₂) ε₂`), using their agreement at
   `t = 0` (both start at `(x, s•v)`).  The common interval is
   `Ioo (-δ) δ` with `δ := min ε₂ (ε₁ / |s|)`; both solutions are defined there.

Small print:
* Make sure the rescaled pair satisfies the hypotheses of `unique_geodesic` on the *whole*
  interval `Ioo (-ε₁/|s|) (ε₁/|s|)` (that is exactly what `geodesic_rescale` provides), and
  `(c₂,vel₂)` on `Ioo (-ε₂) ε₂` (given).  Then restrict to the smaller interval
  `Ioo (-δ) δ` and invoke `unique_geodesic` there (it only needs the HasDerivAt statements on
  that interval).
* `|s| > 0` from `hs : s ≠ 0` (`abs_pos.mpr hs`); interval arithmetic with
  `div_lt_iff₀`, `abs_lt`, `lt_min`/`min_lt_iff`.

Do NOT change the statement of `flow_scaling`.  You may add helper lemmas.  No placeholders/axioms
may remain.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Time rescaling commutes with the flow: the geodesic from `(x, s • v)` at time `t` is the
geodesic from `(x, v)` at time `s * t`. -/
theorem flow_scaling (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    {c₁ vel₁ c₂ vel₂ : ℝ → E} {x v : E} {s : ℝ} (hs : s ≠ 0)
    (hc₁ : c₁ 0 = x) (hv₁ : vel₁ 0 = v)
    (hc₁d : ∀ t ∈ Ioo (-ε₁) ε₁, HasDerivAt c₁ (vel₁ t) t)
    (hv₁d : ∀ t ∈ Ioo (-ε₁) ε₁,
      HasDerivAt vel₁ (accel (g (c₁ t)) (fderiv ℝ g (c₁ t)) (vel₁ t)) t)
    (hc₂ : c₂ 0 = x) (hv₂ : vel₂ 0 = s • v)
    (hc₂d : ∀ t ∈ Ioo (-ε₂) ε₂, HasDerivAt c₂ (vel₂ t) t)
    (hv₂d : ∀ t ∈ Ioo (-ε₂) ε₂,
      HasDerivAt vel₂ (accel (g (c₂ t)) (fderiv ℝ g (c₂ t)) (vel₂ t)) t) :
    ∀ t ∈ Ioo (-min ε₂ (ε₁ / |s|)) (min ε₂ (ε₁ / |s|)),
      c₂ t = c₁ (s * t) ∧ vel₂ t = s • vel₁ (s * t) := by
  let δ : ℝ := min ε₂ (ε₁ / |s|)
  let c₁' : ℝ → E := fun u => c₁ (s * u)
  let vel₁' : ℝ → E := fun u => s • vel₁ (s * u)
  have hs_abs : 0 < |s| := abs_pos.mpr hs
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hε₂ (div_pos hε₁ hs_abs)
  have hδ_le_ε₁s : δ ≤ ε₁ / |s| := by
    dsimp [δ]
    exact min_le_right ε₂ (ε₁ / |s|)
  have hδ_le_ε₂ : δ ≤ ε₂ := by
    dsimp [δ]
    exact min_le_left ε₂ (ε₁ / |s|)
  have hres := geodesic_rescale (g := g) (hg := hg) (hinv := hinv) (ε := ε₁)
    (hε := hε₁) (c := c₁) (vel := vel₁) (hc := hc₁d) (hv := hv₁d) (s := s) (hs := hs)
  have hc₁'d : ∀ t ∈ Ioo (-δ) δ, HasDerivAt c₁' (vel₁' t) t := by
    intro t ht
    have hmem : t ∈ Ioo (-ε₁ / |s|) (ε₁ / |s|) := by
      constructor
      · exact lt_of_le_of_lt (by simpa [neg_div] using neg_le_neg hδ_le_ε₁s) ht.1
      · exact lt_of_lt_of_le ht.2 hδ_le_ε₁s
    simpa [c₁', vel₁'] using hres.1 t hmem
  have hv₁'d : ∀ t ∈ Ioo (-δ) δ, HasDerivAt vel₁'
      (accel (g (c₁' t)) (fderiv ℝ g (c₁' t)) (vel₁' t)) t := by
    intro t ht
    have hmem : t ∈ Ioo (-ε₁ / |s|) (ε₁ / |s|) := by
      constructor
      · exact lt_of_le_of_lt (by simpa [neg_div] using neg_le_neg hδ_le_ε₁s) ht.1
      · exact lt_of_lt_of_le ht.2 hδ_le_ε₁s
    simpa [c₁', vel₁'] using hres.2 t hmem
  have hc₂d' : ∀ t ∈ Ioo (-δ) δ, HasDerivAt c₂ (vel₂ t) t := by
    intro t ht
    have hmem : t ∈ Ioo (-ε₂) ε₂ := by
      constructor
      · exact lt_of_le_of_lt (neg_le_neg hδ_le_ε₂) ht.1
      · exact lt_of_lt_of_le ht.2 hδ_le_ε₂
    exact hc₂d t hmem
  have hv₂d' : ∀ t ∈ Ioo (-δ) δ, HasDerivAt vel₂
      (accel (g (c₂ t)) (fderiv ℝ g (c₂ t)) (vel₂ t)) t := by
    intro t ht
    have hmem : t ∈ Ioo (-ε₂) ε₂ := by
      constructor
      · exact lt_of_le_of_lt (neg_le_neg hδ_le_ε₂) ht.1
      · exact lt_of_lt_of_le ht.2 hδ_le_ε₂
    exact hv₂d t hmem
  have hc0' : c₂ 0 = c₁' 0 := by
    simp [c₁', hc₁, hc₂]
  have hv0' : vel₂ 0 = vel₁' 0 := by
    simp [vel₁', hv₁, hv₂]
  have huniq := unique_geodesic (g := g) (hg := hg) (hinv := hinv) (ε := δ) (hε := hδ)
    (c₁ := c₂) (vel₁ := vel₂) (c₂ := c₁') (vel₂ := vel₁')
    (hc₁ := hc₂d') (hv₁ := hv₂d') (hc₂ := hc₁'d) (hv₂ := hv₁'d)
    (hc0 := hc0') (hv0 := hv0')
  intro t ht
  refine ⟨?_, ?_⟩
  · simpa [δ, c₁'] using huniq.1 t ht
  · simpa [δ, vel₁'] using huniq.2 t ht

end

end Submission.Model
