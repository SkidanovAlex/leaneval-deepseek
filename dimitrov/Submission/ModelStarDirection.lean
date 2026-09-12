import Mathlib
import Submission.ModelStarBoundary2
import Submission.ModelStarBoundary4

/-!
# ModelStarDirection -- the arc-direction ("E3") dictionary for the model map

STATUS: research isolate (NOT imported by `Submission.lean`); every declaration
axiom-clean `[propext, Classical.choice, Quot.sound]`; 0 sorries.

The model boundary map is

    F(z) = modelF z₀ r z = z · ∏_k (1 - z₀ k / z) ^ (2 r k),     z₀ k = eAngle (φ k),

and `ModelStarBoundary2.modelF_boundary_ray` computes its argument on the unit
circle: for `0 < t < 2π` with `t` not a junction angle,

    F(eAngle t) = (∏_k ‖1 - eAngle (φ k - t)‖ ^ (2 r k)) · eAngle (Θ φ r t),

    Θ φ r t := Σ_k r k · (φ k + π · dirSign φ t k),
    dirSign φ t k := if φ k < t then 1 else -1

(`ModelStarBoundary4.boundaryMap_on_junctionFree_interval` derives from this that
each junction-free interval maps into a single ray, with direction the constant
value of `Θ` on it).  This module records the *arithmetic* of `Θ` that turns the
ray description into the dictionary between the model data `(φ, r)` and the
spike directions:

* `theta_gap`: crossing a single junction angle `φ m` changes `Θ` by `2π·r m`.
  Hence **the angular gaps between consecutive spike directions of a model star
  are exactly `2π r k`** -- so the weights of a model star are FORCED to be the
  angular gaps of the desired spike directions divided by `2π`.
* `theta_on_arc`: on the arc that follows the `j`-th junction (in the sense
  `φ k < t ↔ (k : ℕ) ≤ j`), the direction is the explicit affine function of the
  cumulative weights

      Θ = (Σ_k r k φ k) + π · (2 · (Σ_{k ≤ j} r k) - Σ_k r k).

Both are elementary finite-sum identities (only one summand changes), but they
are the model-star half of input E3 of the Eremenko/KL route and the dictionary
needed to *construct* candidate model stars for the "dominating model star"
reduction `Submission/ModelStarDominating.unit_case_of_dominating_modelStar`
(see `Submission/Work/STATUS_dimitrov.md` section 126).
-/

noncomputable section

open scoped Real Topology BigOperators
open Filter Set

namespace Submission.ModelStarDirection

open Submission.ModelStarBoundary2 (dirSign eAngle)
open Submission.ModelStarBoundary4

/-- `dirSign` is `1` once the junction angle is passed. -/
lemma dirSign_eq_one {s : ℕ} {φ : Fin s → ℝ} {t : ℝ} {k : Fin s} (h : φ k < t) :
    dirSign φ t k = 1 := by
  simp [Submission.ModelStarBoundary2.dirSign, h]

/-- `dirSign` is `-1` before the junction angle is passed. -/
lemma dirSign_eq_neg_one {s : ℕ} {φ : Fin s → ℝ} {t : ℝ} {k : Fin s} (h : ¬ φ k < t) :
    dirSign φ t k = -1 := by
  simp [Submission.ModelStarBoundary2.dirSign, h]

/-- **Crossing one junction changes the direction by `2π·r m`.**  If `t < φ m < t'`
and every OTHER junction angle lies on the same side of `t` as of `t'`, then

    Θ(t') - Θ(t) = 2 π r m ,

i.e. the two adjacent arcs of the model star have spike directions differing by
exactly `2π` times the weight of the junction between them. -/
theorem theta_gap {s : ℕ} (φ r : Fin s → ℝ) (m : Fin s) {t t' : ℝ}
    (ht : t < φ m) (ht' : φ m < t')
    (hother : ∀ k : Fin s, k ≠ m → (φ k < t ↔ φ k < t')) :
    (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t' k)) -
        (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k))
      = 2 * Real.pi * r m := by
  classical
  have hterm : ∀ k : Fin s, r k * (φ k + Real.pi * dirSign φ t' k) -
      r k * (φ k + Real.pi * dirSign φ t k) =
      (if k = m then 2 * Real.pi * r k else 0) := by
    intro k
    by_cases hk : k = m
    · subst hk
      rw [if_pos rfl, dirSign_eq_neg_one (not_lt.mpr ht.le), dirSign_eq_one ht']
      ring
    · have hiff := hother k hk
      rcases hiff with ⟨h1, h2⟩
      rw [if_neg hk]
      by_cases hcase : φ k < t
      · rw [dirSign_eq_one hcase, dirSign_eq_one (h1 hcase)]
        ring
      · have hnt' : ¬ φ k < t' := fun h => hcase (h2 h)
        rw [dirSign_eq_neg_one hcase, dirSign_eq_neg_one hnt']
        ring
  calc (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t' k)) -
        (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k))
      = ∑ k : Fin s, (r k * (φ k + Real.pi * dirSign φ t' k) -
          r k * (φ k + Real.pi * dirSign φ t k)) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ k : Fin s, (if k = m then 2 * Real.pi * r k else 0) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
    _ = 2 * Real.pi * r m := by
        rw [Finset.sum_ite_eq' Finset.univ m (fun k => 2 * Real.pi * r k)]
        simp

/-- **The direction on an arc, in terms of the cumulative weights.**  If `t` lies
after exactly the junctions with index `≤ j` (the formal statement: for every
`k`, `φ k < t` iff `(k : ℕ) ≤ (j : ℕ)`), then the direction of the ray containing
`F (eAngle t)` is

    Θ = (Σ_k r k φ k) + π · (2 · (Σ_{k ≤ j} r k) - Σ_k r k) ,

the sum `Σ_{k ≤ j}` running over `Finset.univ.filter (·.val ≤ j.val)`.  Since
`Σ r k = 1` for the standard model data, this reads
`Θ = Σ_k r k φ k + π - 2π Σ_{k ≤ j} r k`: the direction of the arc following the
`j`-th junction.  In particular the directions of consecutive arcs differ by
`2π r` (see `theta_gap`). -/
theorem theta_on_arc {s : ℕ} (φ r : Fin s → ℝ) {j : Fin s} {t : ℝ}
    (harc : ∀ k : Fin s, (φ k < t ↔ k.val ≤ j.val)) :
    (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k)) =
      (∑ k : Fin s, r k * φ k) +
        Real.pi * (2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val), r k) -
          (∑ k : Fin s, r k)) := by
  classical
  have hterm : ∀ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k) =
      r k * φ k - Real.pi * r k + 2 * Real.pi * (if k.val ≤ j.val then r k else 0) := by
    intro k
    by_cases hk : φ k < t
    · have hle : k.val ≤ j.val := (harc k).mp hk
      rw [dirSign_eq_one hk, if_pos hle]
      ring
    · have hle : ¬ k.val ≤ j.val := fun h => hk ((harc k).mpr h)
      rw [dirSign_eq_neg_one hk, if_neg hle]
      ring
  have hsum_if : (∑ k : Fin s, (if k.val ≤ j.val then r k else 0)) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val), r k) := by
    rw [Finset.sum_filter]
  calc (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k))
      = ∑ k : Fin s, (r k * φ k - Real.pi * r k +
          2 * Real.pi * (if k.val ≤ j.val then r k else 0)) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
    _ = (∑ k : Fin s, r k * φ k) - Real.pi * (∑ k : Fin s, r k) +
          2 * Real.pi * (∑ k : Fin s, (if k.val ≤ j.val then r k else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (∑ k : Fin s, r k * φ k) +
        Real.pi * (2 * (∑ k ∈ Finset.univ.filter (fun k : Fin s => k.val ≤ j.val), r k) -
          (∑ k : Fin s, r k)) := by
        rw [hsum_if]
        ring

/-- `eAngle` is multiplicative in the angle. -/
lemma eAngle_add (a b : ℝ) : eAngle (a + b) = eAngle a * eAngle b := by
  simp only [Submission.ModelStarBoundary2.eAngle, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **The spike directions of adjacent arcs differ by the rotation `eAngle (2π r m)`.**
Formulated on the direction angles `Θ`: this is the geometric form of `theta_gap`,
the dictionary between the model data and the spike directions. -/
theorem eAngle_direction_gap {s : ℕ} (φ r : Fin s → ℝ) (m : Fin s) {t t' : ℝ}
    (ht : t < φ m) (ht' : φ m < t')
    (hother : ∀ k : Fin s, k ≠ m → (φ k < t ↔ φ k < t')) :
    eAngle (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t' k)) =
      eAngle (2 * Real.pi * r m) *
        eAngle (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k)) := by
  have hgap := theta_gap φ r m ht ht' hother
  have hsplit : (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t' k)) =
      (∑ k : Fin s, r k * (φ k + Real.pi * dirSign φ t k)) + 2 * Real.pi * r m := by
    linarith [hgap]
  rw [hsplit, eAngle_add, mul_comm]

end Submission.ModelStarDirection

end
