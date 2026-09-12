import Mathlib
import Submission.Work.Polygon.DiscreteConvex
import Submission.Work.Lattice.PolygonLipschitz
import Submission.Work.Lattice.Prop42Upper

/-!
# The smallest concave majorant `Ω̃` of a rank function `Ω`

The §3 asymptotics (see `Submission/Work/ROADMAP.md`, STATUS(session 160) §3) reduce the
position criterion to the concavity of the **smallest concave majorant** `Ω̃` of the maximal
position function `Ω`:

    `Ω̃(j) ≥ (ℓ/d)·j`  for all `j ≤ d`   (`Ω̃(0) = 0`, `Ω̃(d) = ℓ`, `Ω̃` concave),

which is the "concave function lies above its chord" fact.  Since `lcm(−Ω) = −` (smallest concave
majorant of `Ω`) — the largest convex minorant of `−Ω` is the negative of the smallest concave
majorant — everything is a formal consequence of the existing `largestConvexMinorant` API.

Contents (all sorry-free):

* `largestConvexMinorant_apply_left` / `_apply_right`: the largest convex minorant **agrees with
  the data at the two endpoints** (`lcm d g 0 = g 0`, `lcm d g d = g d`) — this is *not* true at
  interior points, and is why the endpoints are special; deduced from the vanishing-endpoint
  lemmas `largestConvexMinorant_zero_left/_right` by translation
  (`Polygon.largestConvexMinorant_add_const`);
* `concaveMajorant d Ω`: the smallest concave majorant, `j ↦ − lcm d (−Ω) j`;
* `concaveMajorant_majorant` (`Ω ≤ Ω̃`), `concaveMajorant_concave`
  (`Ω̃ i + Ω̃ (i+2) ≥ 2 Ω̃ (i+1)`), `concaveMajorant_zero`, `concaveMajorant_self_d`;
* `concaveMajorant_chord` (`(d)·Ω̃ j ≥ (d−j)·Ω̃ 0 + j·Ω̃ d`, from
  `Prop42Upper.chord_le_of_discreteConvex`), and the criterion
  `le_concaveMajorant_of_endpoints`: `Ω 0 = 0`, `Ω d = ℓ`, `0 < d` ⟹ `(ℓ/d)·j ≤ Ω̃ j`.

Module `Submission.Work.Lattice.ConcaveMajorant`, namespace `Submission.ConcaveMajorant`.
-/

noncomputable section

open Finset
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.ConcaveMajorant

open Submission.Polygon

/-- The largest convex minorant agrees with the data at the **right** endpoint
(translate so that the endpoint value is `0` and use `largestConvexMinorant_zero_right`). -/
theorem largestConvexMinorant_apply_right (d : ℕ) (g : ℕ → ℝ) :
    largestConvexMinorant d g d = g d := by
  have hshift : (fun i : ℕ => (g i - g d) + g d) = g := by
    funext i
    simp
  have h := largestConvexMinorant_add_const (d := d) (fun i : ℕ => g i - g d) (g d)
    (i := d) (by omega)
  rw [hshift] at h
  have h0 := largestConvexMinorant_zero_right d (fun i : ℕ => g i - g d) (by simp)
  rw [h0, zero_add] at h
  exact h

/-- The largest convex minorant agrees with the data at the **left** endpoint. -/
theorem largestConvexMinorant_apply_left (d : ℕ) (g : ℕ → ℝ) :
    largestConvexMinorant d g 0 = g 0 := by
  have hshift : (fun i : ℕ => (g i - g 0) + g 0) = g := by
    funext i
    simp
  have h := largestConvexMinorant_add_const (d := d) (fun i : ℕ => g i - g 0) (g 0)
    (i := 0) (by omega)
  rw [hshift] at h
  have h0 := largestConvexMinorant_zero_left d (fun i : ℕ => g i - g 0) (by simp)
  rw [h0, zero_add] at h
  exact h

/-- The **smallest concave majorant** of `Ω`, as the negative of the largest convex minorant of
`−Ω`. -/
def concaveMajorant (d : ℕ) (Ω : ℕ → ℝ) : ℕ → ℝ :=
  fun j => - largestConvexMinorant d (fun i => - Ω i) j

/-- `Ω̃` is a majorant of `Ω`. -/
theorem concaveMajorant_majorant {d j : ℕ} {Ω : ℕ → ℝ} (hj : j ≤ d) :
    Ω j ≤ concaveMajorant d Ω j := by
  have h := largestConvexMinorant_le_g d (fun i => -Ω i) hj
  simp only [concaveMajorant]
  linarith

/-- `Ω̃` is discrete-concave (`Ω̃ i + Ω̃ (i+2) ≤ 2 Ω̃ (i+1)`). -/
theorem concaveMajorant_concave (d : ℕ) (Ω : ℕ → ℝ) :
    ∀ i, i + 2 ≤ d →
      concaveMajorant d Ω i + concaveMajorant d Ω (i + 2) ≤ 2 * concaveMajorant d Ω (i + 1) := by
  intro i hi
  set L : ℕ → ℝ := largestConvexMinorant d (fun i => -Ω i) with hL
  have h3 := three_term_of_convex (largestConvexMinorant_convex d (fun i => -Ω i)) (i := i) hi
  have h3' : (2 : ℝ) * L (i + 1) ≤ L i + L (i + 2) := h3
  have hgoal : concaveMajorant d Ω i + concaveMajorant d Ω (i + 2) ≤
      2 * concaveMajorant d Ω (i + 1) := by
    simp only [concaveMajorant]
    linear_combination h3'
  exact hgoal

/-- `Ω̃` agrees with `Ω` at `0`. -/
theorem concaveMajorant_zero (d : ℕ) (Ω : ℕ → ℝ) :
    concaveMajorant d Ω 0 = Ω 0 := by
  simp only [concaveMajorant, largestConvexMinorant_apply_left]
  ring

/-- `Ω̃` agrees with `Ω` at `d`. -/
theorem concaveMajorant_self_d (d : ℕ) (Ω : ℕ → ℝ) :
    concaveMajorant d Ω d = Ω d := by
  simp only [concaveMajorant, largestConvexMinorant_apply_right]
  ring

/-- **The chord bound for `Ω̃`**: `Ω̃` lies above the chord joining `(0, Ω̃(0))` and `(d, Ω̃(d))`. -/
theorem concaveMajorant_chord {d j : ℕ} (Ω : ℕ → ℝ) (hj : j ≤ d) :
    ((d - j : ℕ) : ℝ) * concaveMajorant d Ω 0 + ((j : ℕ) : ℝ) * concaveMajorant d Ω d ≤
      ((d : ℕ) : ℝ) * concaveMajorant d Ω j := by
  have hraw := Submission.Prop42Upper.chord_le_of_discreteConvex (d := d)
    (largestConvexMinorant_convex d (fun i => -Ω i)) (m := 0) (j := j) (n := d)
    (by omega) hj (by omega)
  have h : ((d : ℕ) : ℝ) * largestConvexMinorant d (fun i => -Ω i) j ≤
      ((d - j : ℕ) : ℝ) * (-Ω 0) + ((j : ℕ) : ℝ) * (-Ω d) := by
    have h2 := hraw
    simp only [Nat.sub_zero] at h2
    rw [largestConvexMinorant_apply_left, largestConvexMinorant_apply_right] at h2
    simpa only [Nat.sub_zero, add_zero] using h2
  simp only [concaveMajorant]
  rw [largestConvexMinorant_apply_left, largestConvexMinorant_apply_right]
  simp only [neg_neg]
  linarith [h]

/-- **The position criterion.**  If `Ω 0 = 0`, `Ω d = ℓ` and `0 < d`, then the smallest concave
majorant dominates the chord `j ↦ (ℓ/d)·j`. -/
theorem le_concaveMajorant_of_endpoints {d : ℕ} (hd : 0 < d) {Ω : ℕ → ℝ} {ℓ : ℝ}
    (h0 : Ω 0 = 0) (hdℓ : Ω d = ℓ) {j : ℕ} (hj : j ≤ d) :
    (ℓ / (d : ℝ)) * (j : ℝ) ≤ concaveMajorant d Ω j := by
  have hchord := concaveMajorant_chord (d := d) Ω hj
  rw [concaveMajorant_zero, concaveMajorant_self_d, h0, hdℓ] at hchord
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : ((d - j : ℕ) : ℝ) * 0 + ((j : ℕ) : ℝ) * ℓ = (j : ℝ) * ℓ := by ring
  rw [h1] at hchord
  have h2 : (ℓ / (d : ℝ)) * (j : ℝ) * (d : ℝ) ≤ concaveMajorant d Ω j * (d : ℝ) := by
    calc (ℓ / (d : ℝ)) * (j : ℝ) * (d : ℝ) = (j : ℝ) * ℓ := by
          field_simp
      _ ≤ ((d : ℕ) : ℝ) * concaveMajorant d Ω j := hchord
      _ = concaveMajorant d Ω j * (d : ℝ) := by ring
  exact le_of_mul_le_mul_right h2 hdR

end Submission.ConcaveMajorant

end
