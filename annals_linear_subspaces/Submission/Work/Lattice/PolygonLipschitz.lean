import Mathlib
import Submission.Work.Polygon.DiscreteConvex

/-!
# Lipschitz continuity of the largest convex minorant

The Grayson polygon of a lattice `Λ` is the largest convex minorant of its rank data
`g : {0,…,d} → ℝ`.  Along the §3 flow `Λ_t = a_t s_x ℤᵈ` the *data* moves continuously in `t`
(its shift is controlled by the two-sided flow bounds on `⋀^j a_h`:
`e^{−hj/ℓ}‖w‖ ≤ ‖⋀^j a_h w‖ ≤ (j+1)e^{hj/(d−ℓ)}‖w‖`), and it is the *polygon* (and its slope
sequence) whose continuity the time-selection argument consumes.

Here we record the elementary facts that make that passage automatic:

* `largestConvexMinorant_mono` — the operator is monotone in the data;
* `largestConvexMinorant_add_const` — it commutes with adding a constant to the data;
* `largestConvexMinorant_le_add` / `abs_largestConvexMinorant_sub_le` — it is `1`-Lipschitz for
  the sup norm on `{0,…,d}`;
* `abs_dslope_largestConvexMinorant_sub_le` — hence the *slope* sequence is `2`-Lipschitz.

Module `Submission.Work.Lattice.PolygonLipschitz`, namespace `Submission.Polygon`.
-/

noncomputable section

open Set
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.Polygon

open Submission.Polygon

/-- **Monotonicity of the largest convex minorant** in the data. -/
lemma largestConvexMinorant_mono {d : ℕ} (f g : ℕ → ℝ) (h : ∀ i : ℕ, i ≤ d → f i ≤ g i)
    {i : ℕ} (hi : i ≤ d) :
    largestConvexMinorant d f i ≤ largestConvexMinorant d g i := by
  have hmem : largestConvexMinorant d f ∈ MinorantSet d g := by
    refine ⟨largestConvexMinorant_convex d f, fun j hj => ?_⟩
    exact le_trans (largestConvexMinorant_le_g d f hj) (h j hj)
  exact convexMinorant_le_largest d g hmem hi

/-- **The largest convex minorant commutes with adding a constant to the data.** -/
lemma largestConvexMinorant_add_const {d : ℕ} (g : ℕ → ℝ) (C : ℝ) {i : ℕ} (hi : i ≤ d) :
    largestConvexMinorant d (fun j => g j + C) i = largestConvexMinorant d g i + C := by
  refine le_antisymm ?_ ?_
  · -- `j ↦ lcm (g+C) j − C` is a convex minorant of `g`
    have hmem : (fun j => largestConvexMinorant d (fun l => g l + C) j - C) ∈ MinorantSet d g := by
      refine ⟨?_, ?_⟩
      · intro j hj
        have h1 := largestConvexMinorant_convex d (fun l => g l + C) j hj
        dsimp [DiscreteConvexOn, dslope] at h1 ⊢
        linarith
      · intro j hj
        have h1 : largestConvexMinorant d (fun l => g l + C) j ≤ g j + C :=
          largestConvexMinorant_le_g d (fun l => g l + C) hj
        linarith
    have h2 := convexMinorant_le_largest d g hmem hi
    linarith
  · -- `j ↦ lcm g j + C` is a convex minorant of `g + C`
    have hmem : (fun j => largestConvexMinorant d g j + C) ∈
        MinorantSet d (fun j => g j + C) := by
      refine ⟨?_, ?_⟩
      · intro j hj
        have h1 := largestConvexMinorant_convex d g j hj
        dsimp [DiscreteConvexOn, dslope] at h1 ⊢
        linarith
      · intro j hj
        have h1 := largestConvexMinorant_le_g d g hj
        linarith
    exact convexMinorant_le_largest d (fun j => g j + C) hmem hi

/-- **The largest convex minorant is `1`-Lipschitz for the sup norm on `{0,…,d}`** (one-sided
form). -/
lemma largestConvexMinorant_le_add {d : ℕ} (f g : ℕ → ℝ) {C : ℝ}
    (h : ∀ i : ℕ, i ≤ d → f i ≤ g i + C) {i : ℕ} (hi : i ≤ d) :
    largestConvexMinorant d f i ≤ largestConvexMinorant d g i + C := by
  have h1 : largestConvexMinorant d f i ≤ largestConvexMinorant d (fun j => g j + C) i :=
    largestConvexMinorant_mono f (fun j => g j + C) h hi
  rwa [largestConvexMinorant_add_const g C hi] at h1

/-- **The largest convex minorant is `1`-Lipschitz for the sup norm on `{0,…,d}`.** -/
lemma abs_largestConvexMinorant_sub_le {d : ℕ} (f g : ℕ → ℝ) {C : ℝ}
    (h : ∀ i : ℕ, i ≤ d → |f i - g i| ≤ C) {i : ℕ} (hi : i ≤ d) :
    |largestConvexMinorant d f i - largestConvexMinorant d g i| ≤ C := by
  have h1 : largestConvexMinorant d f i ≤ largestConvexMinorant d g i + C :=
    largestConvexMinorant_le_add f g (fun j hj => by
      have := (abs_le.mp (h j hj)).2; linarith) hi
  have h2 : largestConvexMinorant d g i ≤ largestConvexMinorant d f i + C :=
    largestConvexMinorant_le_add g f (fun j hj => by
      have := (abs_le.mp (h j hj)).1; linarith) hi
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Slopes: `|Λ_i(lcm f) − Λ_i(lcm g)| ≤ 2C` under a sup-norm bound `C` on the data. -/
lemma abs_dslope_largestConvexMinorant_sub_le {d : ℕ} (f g : ℕ → ℝ) {C : ℝ}
    (h : ∀ i : ℕ, i ≤ d → |f i - g i| ≤ C) {i : ℕ} (hi : i + 1 ≤ d) :
    |dslope (largestConvexMinorant d f) i - dslope (largestConvexMinorant d g) i| ≤ 2 * C := by
  have h1 := abs_largestConvexMinorant_sub_le f g h (i := i) (by omega)
  have h2 := abs_largestConvexMinorant_sub_le f g h (i := i + 1) hi
  have e1 := (abs_le.mp h1)
  have e2 := (abs_le.mp h2)
  dsimp [dslope]
  rw [abs_sub_le_iff]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

end Submission.Polygon
