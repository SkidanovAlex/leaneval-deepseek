import Mathlib
import Submission.Work.PL.Subdiv.Embed
import Submission.Work.PL.Subdiv.Embed.exists_translate_faces
import Submission.Work.PL.Subdiv.Embed.exists_union_faces

/-!
# Disjoint union of two finite PL complexes after a far translation

Blueprint A2 item 6 of `Submission/Work/NOTES_LEAD_poincare_blueprint.md`: two finite geometric
simplicial complexes `K`, `L` in `ℝᴺ` (`N > 0`) can be made *disjoint* by translating one of them
far away, and then glued into a single complex `C` whose faces are the faces of `K` together with
the translated faces of `L`.  This is what lets far-away frozen components be adjoined to a
complex.

The ingredients are

* `Work.PL.Subdiv.Embed.exists_translate_faces` -- translating a complex by `v` gives a complex
  whose faces are the translated faces and whose space is the translated space;
* `Work.PL.Subdiv.Embed.exists_union_faces` -- two complexes with disjoint spaces glue into their
  union;
* the two facts proved here: the space of a complex with finitely many faces is *bounded*
  (`exists_norm_le_of_finite_faces`), and `ℝᴺ` with `N > 0` contains a vector of norm `> 2 * R`
  (`norm_single_gt_two_mul`).

Take `R` bounding the norms of the points of both spaces and translate by a vector `v` of norm
`> 2 * R` along a coordinate axis (possible exactly because `N > 0`).  Then the two spaces are
disjoint: from `x = y + v` with `x ∈ K.space`, `y ∈ L.space` we would get
`‖v‖ = ‖x - y‖ ≤ ‖x‖ + ‖y‖ ≤ 2 * R < ‖v‖`.  Now glue the translate of `L` to `K`.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Embed

noncomputable section

/-- The underlying space of a complex with finitely many faces is bounded: there is `R` with
`‖x‖ ≤ R` for every `x` in the space. -/
private theorem exists_norm_le_of_finite_faces {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) :
    ∃ R : ℝ, ∀ x ∈ K.space, ‖x‖ ≤ R := by
  have hb : Bornology.IsBounded K.space := by
    rw [Geometry.SimplicialComplex.space]
    refine (Bornology.isBounded_biUnion hK).2 fun s _ => ?_
    exact isBounded_convexHull.mpr (Set.Finite.isBounded (s.finite_toSet))
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : PL.E N)
  exact ⟨R, fun x hx => by simpa [Metric.mem_closedBall, dist_eq_norm] using hR hx⟩

/-- In `ℝᴺ` with `N > 0` there is a vector of norm bigger than `2 * R`: `2 * R + 1` times a unit
basis vector. -/
private lemma norm_single_gt_two_mul (N : ℕ) (hN : 0 < N) (R : ℝ) :
    2 * R < ‖EuclideanSpace.single (⟨0, hN⟩ : Fin N) (2 * R + 1)‖ := by
  rw [show EuclideanSpace.single (⟨0, hN⟩ : Fin N) (2 * R + 1)
      = PiLp.single (2 : ENNReal) (⟨0, hN⟩ : Fin N) (2 * R + 1) from rfl]
  rw [PiLp.norm_single, Real.norm_eq_abs]
  have := le_abs_self (2 * R + 1)
  linarith

theorem exists_disjoint_union_translate {N : ℕ} (hN : 0 < N) (K L : PL.Cx N)
    (hK : K.faces.Finite) (hL : L.faces.Finite) :
    ∃ (v : PL.E N) (C : PL.Cx N),
      (∀ t, t ∈ C.faces ↔ t ∈ K.faces ∨ ∃ s ∈ L.faces, t = s.image (fun x => x + v)) ∧
      C.space = K.space ∪ ((fun x => x + v) '' L.space) ∧
      Disjoint K.space ((fun x => x + v) '' L.space) := by
  obtain ⟨R₁, hR₁⟩ := exists_norm_le_of_finite_faces K hK
  obtain ⟨R₂, hR₂⟩ := exists_norm_le_of_finite_faces L hL
  -- translate along a coordinate axis, far enough to separate the two bounded spaces
  set v : PL.E N := EuclideanSpace.single ⟨0, hN⟩ (2 * max R₁ R₂ + 1) with hv
  have hvgt : 2 * max R₁ R₂ < ‖v‖ := by
    rw [hv]; exact norm_single_gt_two_mul N hN (max R₁ R₂)
  obtain ⟨M, hMfaces, hMspace⟩ := exists_translate_faces L v
  have hdisj : Disjoint K.space M.space := by
    rw [hMspace, Set.disjoint_left]
    rintro x hxK ⟨y, hyL, rfl⟩
    -- if `y + v ∈ K.space` with `y ∈ L.space`, then `v` would be too short
    have hle : ‖v‖ ≤ 2 * max R₁ R₂ := by
      have h1 : ‖(y + v) - y‖ ≤ ‖y + v‖ + ‖y‖ := norm_sub_le _ _
      have h2 : (y + v) - y = v := by abel
      rw [h2] at h1
      have h3 : ‖y + v‖ ≤ R₁ := hR₁ _ hxK
      have h4 : ‖y‖ ≤ R₂ := hR₂ _ hyL
      have h5 : R₁ + R₂ ≤ 2 * max R₁ R₂ := by
        have ha := le_max_left R₁ R₂
        have hb := le_max_right R₁ R₂
        linarith
      linarith
    linarith
  obtain ⟨C, hCfaces, hCspace⟩ := exists_union_faces K M hdisj
  refine ⟨v, C, ?_, ?_, ?_⟩
  · intro t
    rw [hCfaces, hMfaces t]
  · rw [hCspace, hMspace]
  · rw [← hMspace]; exact hdisj

end

end Work.PL.Subdiv.Embed
