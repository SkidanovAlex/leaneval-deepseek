import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.coord_spec

/-!
# Specification of the local barycentric coordinates `rcoord`

`Work.Geo.DualStretch.rcoord σ x` is the barycentric-coordinate function of a point `x` of the
simplex `PL.simp σ`, with respect to the (finite) vertex set `σ`: off `PL.simp σ` and off `σ` it
vanishes, and on `σ` it is the chosen convex-combination weight function of `x`.

The four clauses proved here are the analogue, for the local object, of `coord_spec`:
non-negativity on `σ`, unit total mass, `x` is the centre of mass, and vanishing off `σ`.
-/

namespace Work.Geo.DualStretch

variable {n : ℕ}

theorem rcoord_spec {n : ℕ} {σ : Finset (PL.E n)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E n)) {x : PL.E n} (hx : x ∈ PL.simp σ) :
    (∀ v ∈ σ, 0 ≤ Work.Geo.DualStretch.rcoord σ x v) ∧
      (∑ v ∈ σ, Work.Geo.DualStretch.rcoord σ x v = 1) ∧
      (∑ v ∈ σ, Work.Geo.DualStretch.rcoord σ x v • v = x) ∧
      (∀ v ∉ σ, Work.Geo.DualStretch.rcoord σ x v = 0) := by
  classical
  -- the hypothesis of affine independence is not needed for these clauses
  have _hσ := hσ
  -- `rcoord σ x` is the chosen convex-combination weight function of `x` on `σ`
  have hex : ∃ μ : PL.E n → ℝ, (∀ w ∈ σ, 0 ≤ μ w) ∧
      (∑ w ∈ σ, μ w = 1) ∧ (∑ w ∈ σ, μ w • w = x) :=
    exists_coordOn_of_mem_simp hx
  obtain ⟨hex0, hex1, hex2⟩ := hex.choose_spec
  have hcoord : ∀ v : PL.E n,
      rcoord σ x v = if v ∈ σ then hex.choose v else 0 := by
    intro v
    by_cases hv : v ∈ σ
    · simp only [rcoord, dite_eq_left hx, dite_eq_left hv, dite_eq_left hex, ite_eq_left hv]
    · by_cases hxs : x ∈ PL.simp σ
      · simp only [rcoord, dite_eq_left hxs, dite_eq_right hv, ite_eq_right hv]
      · simp only [rcoord, dite_eq_right hxs, ite_eq_right hv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hcoord v, ite_eq_left hv]
    exact hex0 v hv
  · have h : ∑ v ∈ σ, rcoord σ x v = ∑ v ∈ σ, hex.choose v :=
      Finset.sum_congr rfl fun v hv => by rw [hcoord v, ite_eq_left hv]
    rw [h]; exact hex1
  · have h : ∑ v ∈ σ, rcoord σ x v • v = ∑ v ∈ σ, hex.choose v • v :=
      Finset.sum_congr rfl fun v hv => by rw [hcoord v, ite_eq_left hv]
    rw [h]; exact hex2
  · intro v hv
    rw [hcoord v, ite_eq_right hv]

end Work.Geo.DualStretch
