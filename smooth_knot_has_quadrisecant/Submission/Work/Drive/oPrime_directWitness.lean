import Mathlib
import Submission.Work.Drive.liftedOPrime
import Submission.Work.Drive.Prelude

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **Representative independence of the middle-secant clause of `O'`.**  The
class-level predicate `ClassNontrivialMiddleSecant r (mobiusCover p)` — "the
class of `p` carries two distinct strict middles whose middle secant is
non-trivial" — is exactly the data property at the ordered pair `p` itself.
(The fibre of `mobiusCover` over `p` is `{p, swapOrdered p}` and both
`IsMiddleOnChord` and `QuadrisecantMiddleSecantTrivial` are invariant under the
endpoint swap.)  This is the middle-secant analogue of
`ClassNontrivialTrisecant_mobiusCover`. -/
lemma ClassNontrivialMiddleSecant_mobiusCover {r : ℝ → Space} (p : OrderedPairs) :
    ClassNontrivialMiddleSecant r (mobiusCover p) ↔
      ∃ z w : AddCircle period, z ≠ w ∧
        IsMiddleOnChord r p.1.1 p.1.2 z ∧ IsMiddleOnChord r p.1.1 p.1.2 w ∧
        ¬ QuadrisecantMiddleSecantTrivial r z w := by
  constructor
  · rintro ⟨q, hq, z, w, hzw, hz, hw, hnt⟩
    have hqmem : q ∈ ({p, swapOrdered p} : Set OrderedPairs) := by
      rw [← mobiusCover_fiber p]; exact hq
    simp at hqmem
    rcases hqmem with rfl | hqeq
    · exact ⟨z, w, hzw, hz, hw, hnt⟩
    · rw [hqeq] at hz hw
      exact ⟨z, w, hzw,
        (IsMiddleOnChord_swap r p z).mp (by simpa [swapOrdered] using hz),
        (IsMiddleOnChord_swap r p w).mp (by simpa [swapOrdered] using hw), hnt⟩
  · rintro ⟨z, w, hzw, hz, hw, hnt⟩
    exact ⟨p, rfl, z, w, hzw, hz, hw, hnt⟩

/-- The `O'`-witness of a point of `liftedOPrime r`, normalised to the *direct* pair of parameters
`(p.1, p.1 + p.2)` of the strip point `p`. -/
lemma oPrime_directWitness {r : ℝ → Space} {p : ℝ × ℝ} (hp : p ∈ Work.Drive.liftedOPrime r) :
    (∃ m : AddCircle period,
        IsMiddleOnChord r (p.1 : AddCircle period) (((p.1 + p.2 : ℝ)) : AddCircle period) m ∧
        ¬ TrisecantTrivial r (p.1 : AddCircle period) (((p.1 + p.2 : ℝ)) : AddCircle period) m) ∨
    (∃ z w : AddCircle period, z ≠ w ∧
        IsMiddleOnChord r (p.1 : AddCircle period) (((p.1 + p.2 : ℝ)) : AddCircle period) z ∧
        IsMiddleOnChord r (p.1 : AddCircle period) (((p.1 + p.2 : ℝ)) : AddCircle period) w ∧
        ¬ TrivialSecant r z w) := by
  rcases hp with ⟨h0, h1, hmem⟩
  rw [stripSecantClass_eq_mobiusCover] at hmem
  rcases (mem_OPrime_iff r (mobiusCover (stripPair p h0 h1))).mp hmem with htr | hquad
  · left
    obtain ⟨m, hm, hnt⟩ := (ClassNontrivialTrisecant_mobiusCover (stripPair p h0 h1)).mp htr
    exact ⟨m, hm, hnt⟩
  · right
    obtain ⟨z, w, hzw, hz, hw, hnt⟩ :=
      (ClassNontrivialMiddleSecant_mobiusCover (stripPair p h0 h1)).mp hquad
    exact ⟨z, w, hzw, hz, hw, hnt⟩

end Work.Drive
