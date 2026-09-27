import Mathlib
import Submission.Work.Drive.linPlaneTripleMeet
import Submission.Work.Drive.existsUnique_fibre_linPlaneChart
import Submission.Work.Drive.exists_norm_lt_one_linPlaneChart_eq

/-!
# The end contribution of the chain route: three linear planes have triple count one

Hugelmeyer's Lemma 4 (transitivity of `≺`) is the parity identity
`n_P + n_Q + n_R ≡ 1`, which the chain route obtains as

> `Σ_k top_k ≡ Σ_k (top_k + bottom_k + seam_k) + Σ_k bottom_k ≡ 0 + 1`,

the middle term `Σ_k bottom_k` being the *end contribution*: the three sweeps' bottom faces may be
chosen to be three *linear* projective planes of one level in general position
(`ENDS_AND_SEAMS_NOTES.md` §2), and then

> `bottom_k = #(Z_0 ⋔ Z_1 ⋔ Z_2) = #(Z_0 ∩ Z_1 ∩ Z_2) = 1`.

This file proves the count in the form the engine consumes it: for the three *folded square
presentations* `B k = diskPlane (linPlaneChart (φ k) c hc)` of three linear planes of one level whose
planes have a one-dimensional triple intersection and whose common point is not on the boundary circle
of any of the three charts (`hgen`), the set of parameter triples at which the three presentations take
the same value has exactly one element:

> `#{x ∈ (unitBox 1)³ | B 0 (x 0) = B 1 (x 1) = B 2 (x 2)} = 1`.

The three ingredients are:

* `Work.Drive.tripleMeet_linPlaneCharts` — the common value is forced to be `linCommonPt` (the unique
  point of the level on all three planes), so the triple set is a product of three fibres;
* `Work.Drive.exists_norm_lt_one_linPlaneChart_eq` — off the boundary circle each chart attains
  `linCommonPt` in the *open* disk (`hgen` is exactly the boundary-avoidance), and
* `Work.Drive.existsUnique_fibre_linPlaneChart` — the folded presentation has a **singleton** fibre
  over an interior point of the disk (the only failure would be the antipodal boundary pair).

The count is *exactly* one, not merely odd, which is what the chain bookkeeping needs (`Σ_k bottom_k =
3 ≡ 1`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The end contribution: three linear plane charts of one level in general position have exactly
one triple parameter.** -/
theorem ncard_linPlaneTriples_eq_one (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc h) :
    {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc) (x 0)
          = diskPlane (linPlaneChart (φ 1) c hc) (x 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc) (x 0)
          = diskPlane (linPlaneChart (φ 2) c hc) (x 2)}.ncard = 1 := by
  rw [tripleMeet_linPlaneCharts φ c hc h]
  -- each fibre over the common point is a singleton
  have hfib : ∀ k : Fin 3, ∃! y : EuclideanSpace ℝ (Fin 2),
      y ∈ Submission.Drive.unitBox 1 ∧
        diskPlane (linPlaneChart (φ k) c hc) y = linCommonPt φ c hc h := by
    intro k
    obtain ⟨z, hzlt, hzeq⟩ := exists_norm_lt_one_linPlaneChart_eq φ c hc h k (hgen k)
    have hf := existsUnique_fibre_linPlaneChart (φ k) c hc hzlt
    rw [hzeq] at hf
    exact hf
  refine (Set.ncard_eq_one).mpr ⟨fun k => (hfib k).choose, ?_⟩
  ext x
  constructor
  · rintro ⟨hbox, hall⟩
    exact funext fun k => (hfib k).choose_spec.2 (x k) ⟨hbox k, hall k⟩
  · rintro rfl
    exact ⟨fun k => (hfib k).choose_spec.1.1, fun k => (hfib k).choose_spec.1.2⟩

end

end Work.Drive
