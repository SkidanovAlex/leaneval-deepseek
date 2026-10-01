import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports

namespace Work.LinnikAreas.Zeta1Aux

/-- **A good radius for `ζ₁` on the segment `(11/2, 6]`.**

For every real `v` there is `R ∈ (11/2, 6]` such that neither the circle `‖w - c‖ = R`
nor the circle `‖w - c‖ = R/2` (`c = 2 + i v`) contains a zero of the entire function
`riemannZeta₁ = (s-1)·ζ`.

Route: the zeros of `riemannZeta₁` in the closed ball `‖ρ‖ ≤ 7 + ‖c‖` are finite
(`Commons.NumberTheory.Zeta.zetaZeroBall`); let `Bad` be the finite set of their distances
to `c` and `E := Bad ∪ 2·Bad`; `Commons.NumberTheory.Linnik.exists_notMem_Ioc_of_finite`
applied to the interval `(11/2, 6]` produces `R ∉ E`.  If `‖w - c‖ = R` and `ζ₁ w = 0`
then `‖w‖ ≤ ‖c‖ + 6 < ‖c‖ + 7`, so `‖w - c‖ ∈ Bad`, contradiction; likewise for `R/2`
(note `R ∈ Bad2` iff `R/2 ∈ Bad`). -/
lemma zeta1_exists_goodR_segment (v : ℝ) :
    ∃ R : ℝ, 11 / 2 < R ∧ R ≤ 6 ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (v : ℂ))‖ = R → riemannZeta₁ w ≠ 0) ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (v : ℂ))‖ = R / 2 → riemannZeta₁ w ≠ 0) := by
  let c : ℂ := (2 : ℂ) + Complex.I * (v : ℂ)
  -- the zeros of `ζ₁` inside the closed ball `‖ρ‖ ≤ 7 + ‖c‖` form a finite set
  rcases Commons.NumberTheory.Zeta.zetaZeroBall (7 + ‖c‖) (by positivity) with ⟨Z, hZ⟩
  -- the "bad" radii: distances of those zeros to `c`, and their doubles
  let Bad : Set ℝ := (fun u : ℂ => ‖u - c‖) '' (Z : Set ℂ)
  have hBad_fin : Bad.Finite := Z.finite_toSet.image (fun u : ℂ => ‖u - c‖)
  let Bad2 : Set ℝ := (fun r : ℝ => 2 * r) '' Bad
  have hBad2_fin : Bad2.Finite := hBad_fin.image (fun r : ℝ => 2 * r)
  let E : Set ℝ := Bad ∪ Bad2
  have hE_fin : E.Finite := hBad_fin.union hBad2_fin
  -- a finite set of reals cannot cover `(11/2, 6]`
  rcases Commons.NumberTheory.Linnik.exists_notMem_Ioc_of_finite (S := E) hE_fin
      (a := 11 / 2) (b := 6) (by norm_num) with ⟨R, hRa, hR6, hRnotE⟩
  have hRnotBad : R ∉ Bad := fun hb => hRnotE (Or.inl hb)
  have hRnotBad2 : R ∉ Bad2 := fun hb => hRnotE (Or.inr hb)
  refine ⟨R, hRa, hR6, ?_, ?_⟩
  · intro w hw hwz
    -- `‖w‖ ≤ R + ‖c‖ ≤ 6 + ‖c‖ < 7 + ‖c‖`, so `w` is one of the finitely many zeros
    have hwZ : w ∈ Z := by
      rw [hZ]
      refine ⟨?_, hwz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
        calc ‖w‖ = ‖(w - c) + c‖ := by congr 1; ring
          _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
      rw [hw] at h1
      linarith
    have hmem : ‖w - c‖ ∈ Bad := Set.mem_image_of_mem _ hwZ
    exact hRnotBad (by rw [← hw]; exact hmem)
  · intro w hw hwz
    have hwZ : w ∈ Z := by
      rw [hZ]
      refine ⟨?_, hwz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
        calc ‖w‖ = ‖(w - c) + c‖ := by congr 1; ring
          _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
      rw [hw] at h1
      linarith
    have hmem : ‖w - c‖ ∈ Bad := Set.mem_image_of_mem _ hwZ
    have hhalf : R / 2 ∈ Bad := by rw [show R / 2 = ‖w - c‖ from by linarith]; exact hmem
    exact hRnotBad2 ⟨R / 2, hhalf, by ring⟩

end Work.LinnikAreas.Zeta1Aux
