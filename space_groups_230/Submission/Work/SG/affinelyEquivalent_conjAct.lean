import Mathlib
import Submission.Work.SG.affFactsDefs

/-!
# `AffinelyEquivalent` / `AffOPEquivalent` as conjugation of the affine image

`AffFacts.conjAct φ S` is conjugation by the affine map `φ` of a set `S` of affine maps,
and `AffFacts.affImage G` is the image of a subgroup `G` of Euclidean isometries inside
`Aff(ℝ^d)`.  This file records the two trivial dictionary facts that connect those two
operations with the definitions `AffinelyEquivalent` and `AffOPEquivalent` from the
challenge file:

* `conjAct φ (affImage G)` is *definitionally* the set of conjugates `φ * g * φ⁻¹` of the
  elements of `G` (lemma `conjAct_affImage_eq`);
* consequently `AffinelyEquivalent G H` says exactly that some `φ` sends `affImage G` to
  `affImage H` by conjugation, and `AffOPEquivalent G H` says the same with the extra
  condition `0 < det φ.linear`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- Conjugating the affine image of `G` by `φ` gives exactly the set of conjugates
`φ * g * φ⁻¹` of the affine images of the elements of `G`. -/
lemma conjAct_affImage_eq (d : ℕ) (φ : AffineGroup d) (G : Subgroup (EuclideanIsom d)) :
    AffFacts.conjAct φ (AffFacts.affImage G) =
      {h : AffineGroup d | ∃ g ∈ G, h = φ * g.toAffineEquiv * φ⁻¹} := by
  ext h
  simp only [AffFacts.conjAct, AffFacts.affImage]
  constructor
  · rintro ⟨g, ⟨g₀, hg₀, rfl⟩, rfl⟩
    exact ⟨g₀, hg₀, rfl⟩
  · rintro ⟨g₀, hg₀, rfl⟩
    exact ⟨g₀.toAffineEquiv, ⟨g₀, hg₀, rfl⟩, rfl⟩

theorem affinelyEquivalent_conjAct (d : ℕ) :
    (∀ (φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d)
      (G : Subgroup (LeanEval.Geometry.SpaceGroupsProblem.EuclideanIsom d)),
      Work.SG.AffFacts.conjAct φ (Work.SG.AffFacts.affImage G) =
        {h : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d |
          ∃ g ∈ G, h = φ * g.toAffineEquiv * φ⁻¹}) ∧
    (∀ G H : Subgroup (LeanEval.Geometry.SpaceGroupsProblem.EuclideanIsom d),
      LeanEval.Geometry.SpaceGroupsProblem.AffinelyEquivalent G H ↔
        ∃ φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d,
          Work.SG.AffFacts.conjAct φ (Work.SG.AffFacts.affImage G) =
            Work.SG.AffFacts.affImage H) ∧
    (∀ G H : Subgroup (LeanEval.Geometry.SpaceGroupsProblem.EuclideanIsom d),
      LeanEval.Geometry.SpaceGroupsProblem.AffOPEquivalent G H ↔
        ∃ φ : LeanEval.Geometry.SpaceGroupsProblem.AffineGroup d,
          0 < (φ.linear.det : ℝ) ∧
            Work.SG.AffFacts.conjAct φ (Work.SG.AffFacts.affImage G) =
              Work.SG.AffFacts.affImage H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ G
    exact conjAct_affImage_eq d φ G
  · intro G H
    unfold AffinelyEquivalent
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ, by rw [conjAct_affImage_eq]; exact hφ⟩
    · rintro ⟨φ, hφ⟩
      exact ⟨φ, by rw [conjAct_affImage_eq] at hφ; exact hφ⟩
  · intro G H
    unfold AffOPEquivalent
    constructor
    · rintro ⟨φ, hd, hφ⟩
      exact ⟨φ, hd, by rw [conjAct_affImage_eq]; exact hφ⟩
    · rintro ⟨φ, hd, hφ⟩
      exact ⟨φ, hd, by rw [conjAct_affImage_eq] at hφ; exact hφ⟩

end Work.SG
