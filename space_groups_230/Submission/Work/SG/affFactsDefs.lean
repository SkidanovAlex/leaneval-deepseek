import ChallengeDeps

/-! Helpers for the route node `affEquiv_facts` (`Submission/Work/SG/affEquiv_facts.lean`).

`AffinelyEquivalent` / `AffOPEquivalent` compare sets of affine maps obtained by conjugating
the image of a subgroup of Euclidean isometries inside `Aff(ℝ^d)`.  This file isolates the two
elementary operations involved, so that the lemmas about them can be proved separately:

* `conjAct φ S` — conjugation by the affine map `φ` of a set `S` of affine maps;
* `affImage G` — the image of a subgroup `G` of Euclidean isometries in `Aff(ℝ^d)`.

With these, `AffinelyEquivalent G H` says exactly that `conjAct φ (affImage G) = affImage H`
for some `φ`, so all the formal content of `affEquiv_facts` is about the conjugation action. -/

namespace Work.SG
namespace AffFacts

open LeanEval.Geometry.SpaceGroupsProblem

/-- Conjugation of a set of affine equivalences by the affine equivalence `φ`. -/
def conjAct {d : ℕ} (φ : AffineGroup d) (S : Set (AffineGroup d)) : Set (AffineGroup d) :=
  {h | ∃ g ∈ S, h = φ * g * φ⁻¹}

/-- The image of a subgroup of Euclidean isometries inside the affine group. -/
def affImage {d : ℕ} (G : Subgroup (EuclideanIsom d)) : Set (AffineGroup d) :=
  {h | ∃ g ∈ G, h = g.toAffineEquiv}

end AffFacts
end Work.SG
