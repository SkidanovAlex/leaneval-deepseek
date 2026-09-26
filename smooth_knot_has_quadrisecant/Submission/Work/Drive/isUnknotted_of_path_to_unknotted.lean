import Mathlib
import Submission.Work.Drive.isUnknotted_of_knotPath
import Submission.Work.Drive.isUnknotted_of_close
import Submission.Work.Drive.isUnknotted_of_close_rev

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-!
# `IsUnknotted` propagates backwards along a `C¹` path of analytic knots

If `R : ℝ → ℝ → Space` is a jointly `C¹` family whose slices `R · s`, `s ∈ [0,1]`,
are analytic knots, starting at `r0` and ending at `r1`, and the terminal knot `r1`
is unknotted, then the initial knot `r0` is unknotted.

The proof is the same connectedness argument as in
`Work.Drive.isUnknotted_of_knotPath`, but with `standardCircle` replaced by the
arbitrary unknotted terminal knot `r1`:

* `Us` — the set of slice parameters whose slice is unknotted — is open by
  `isUnknotted_of_close_rev` (nearby slices of an unknotted slice are unknotted)
  and closed by `isUnknotted_of_close` (a slice close to an unknotted slice is
  unknotted), using `familyWindowAtC1` for the `C¹`-continuity of the slices;
* `Us` is nonempty because the terminal slice is `r1`, unknotted by hypothesis;
* `[0,1]` is preconnected, so `Us = univ`, and the initial slice `r0` is unknotted.
-/

theorem isUnknotted_of_path_to_unknotted {r0 r1 : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr0 : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r0)
    (hr1 : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r1)
    (hU : LeanEval.KnotTheory.Quadrisecant.IsUnknotted r1)
    {R : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => R p.1 p.2))
    (h0 : ∀ t : ℝ, R t 0 = r0 t) (h1 : ∀ t : ℝ, R t 1 = r1 t)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (fun t : ℝ => R t s)) :
    LeanEval.KnotTheory.Quadrisecant.IsUnknotted r0 := by
  -- the set of slice parameters whose slice is unknotted
  let Us : Set (Set.Icc (0 : ℝ) 1) := {x | IsUnknotted (fun t : ℝ => R t x.1)}
  have hUs : Us = {x : Set.Icc (0 : ℝ) 1 | IsUnknotted (fun t : ℝ => R t x.1)} := rfl
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace (isPreconnected_Icc (a := (0 : ℝ)) (b := 1))
  -- `Us` is open: nearby slices of an unknotted slice are unknotted
  have hopen : IsOpen Us := by
    rw [hUs, Metric.isOpen_iff]
    rintro ⟨x, hx⟩ hxU
    obtain ⟨ε, hεpos, hε⟩ := isUnknotted_of_close_rev (hslice x hx) hxU
    obtain ⟨δ, hδpos, hδ⟩ := familyWindowAtC1 hR hslice hx (γ := ε / 2) (by linarith)
    refine ⟨δ, hδpos, ?_⟩
    rintro ⟨y, hy⟩ hyb
    have hyx : |y - x| < δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hyb
      exact hyb
    have hwin := hδ y hy (le_of_lt hyx)
    exact hε (fun t : ℝ => R t y) (hslice y hy)
      (fun t => ⟨by linarith [(hwin t).1], by linarith [(hwin t).2]⟩)
  -- `Us` is closed: a slice close to an unknotted slice is unknotted
  have hclosed : IsClosed Us := by
    rw [hUs, ← isOpen_compl_iff, Metric.isOpen_iff]
    rintro ⟨x, hx⟩ hxU
    obtain ⟨ε, hεpos, hε⟩ := isUnknotted_of_close (hslice x hx)
    obtain ⟨δ, hδpos, hδ⟩ := familyWindowAtC1 hR hslice hx (γ := ε / 2) (by linarith)
    refine ⟨δ, hδpos, ?_⟩
    rintro ⟨y, hy⟩ hyb
    have hyx : |y - x| < δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hyb
      exact hyb
    intro hyU
    have hclose : ∀ t : ℝ, ‖R t y - R t x‖ < ε ∧
        ‖velocity (fun u : ℝ => R u y) t - velocity (fun u : ℝ => R u x) t‖ < ε := by
      intro t
      have hwin := hδ y hy (le_of_lt hyx) t
      exact ⟨by linarith [hwin.1], by linarith [hwin.2]⟩
    exact hxU (hε (fun t : ℝ => R t y) (hslice y hy) hclose hyU)
  have hclopen : IsClopen Us := ⟨hclosed, hopen⟩
  -- `Us` is nonempty: the terminal slice is the unknotted knot `r1`
  have hne : Us.Nonempty := by
    refine ⟨⟨1, by norm_num⟩, ?_⟩
    rw [hUs]
    show IsUnknotted (fun t : ℝ => R t 1)
    rw [show (fun t : ℝ => R t 1) = r1 from funext h1]
    exact hU
  have hUniv : Us = Set.univ := hclopen.eq_univ hne
  -- hence the initial slice is unknotted too
  have hun : IsUnknotted (fun t : ℝ => R t 0) := by
    have hmem : (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) ∈ Us := by
      rw [hUniv]; exact Set.mem_univ _
    rw [hUs] at hmem
    exact hmem
  rwa [show (fun t : ℝ => R t 0) = r0 from funext h0] at hun

end Work.Drive
