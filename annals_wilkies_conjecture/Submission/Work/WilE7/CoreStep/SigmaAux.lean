/-
  Area E7 / `CoreLT_succ` case B: the coordinate helpers used to state the Σ-assembly.

  The Σ-family of the case-B step is indexed by the *pieces* (`Stratum 0 (n + (m+1))`) and by
  their **pair sets** (`absPairSet T : SemiPf (0 + pPair n m)`, `pPair n m = 2*(n + (m+1))`).
  The "forbidden locus" attached to a subset of the pair space is its projection to the common
  base coordinates — the first `n` coordinates, which coincide for the two vertices because
  `absPairSet` requires `projFirst n (m+1) u = projFirst n (m+1) v`.

  `pairBase` is that projection, written so that it typechecks without any `Nat` rewriting at the
  use site.  Everything else in the Σ-assembly is stated with the library's `projFirst`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs

set_option autoImplicit false
noncomputable section
namespace Work.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair)

theorem le_pPair (n m : ℕ) : n ≤ pPair n m := by
  show n ≤ (n + (m + 1)) + (n + (m + 1))
  omega

/-- The common base point of a point of the pair space `ℝ^{pPair n m}` (the first `n`
coordinates).  For a point of `absPairSet T` this is the base point of both vertices. -/
def pairBase (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) : Fin n → ℝ :=
  fun i => absPt w (Fin.castLE (le_pPair n m) i)

/-- The same projection, for a point of the *reindexed* pair space `ℝ^{pPair n m}`. -/
def pairBaseFst (n m : ℕ) (w : Fin (pPair n m) → ℝ) : Fin n → ℝ :=
  fun i => w (Fin.castLE (le_pPair n m) i)

theorem pairBase_absPt (n m : ℕ) (w : Fin (0 + pPair n m) → ℝ) :
    pairBase n m w = pairBaseFst n m (absPt w) := rfl

/-- The forbidden locus attached to an absolute stratum `T`: the projection to `ℝ^n` of the
*frontier* `closure ∖ set`.  `hE6` turns its `SemiPf` realisation into a member of Σ (this is what
supplies `hclosed`). -/
def frontierSet (n m : ℕ) (T : Stratum 0 (n + (m + 1))) : Set (Fin n → ℝ) :=
  projFirst n (m + 1) '' (closure (absSet T) \ absSet T)

/-- The forbidden locus attached to a `Good` stratum `W` of a pair set: the projection of the
pair stratum to the common base coordinates (the first `n` of the pair space). -/
def pairSubBase (n m : ℕ) (W : Stratum 0 (pPair n m)) : Set (Fin n → ℝ) :=
  pairBase n m '' W.X.set

/-- Same, read through `absPt` (the form in which `absPairSet`'s members are stated). -/
def pairSubBaseFst (n m : ℕ) (W : Stratum 0 (pPair n m)) : Set (Fin n → ℝ) :=
  pairBaseFst n m '' (absPt '' W.X.set)

/-- The forbidden locus attached to the *frontier* of a stratum of the pair space: the base
projection of `closure set ∖ set`.  This is the second clause of the level-dichotomy avoidance
(`persist_of_Zavoid_same`'s `havoid`). -/
def pairFrontierBaseFst (n m : ℕ) (V : Stratum 0 (pPair n m)) : Set (Fin n → ℝ) :=
  pairBaseFst n m '' (closure (absPt '' V.X.set) \ (absPt '' V.X.set))

theorem pairSubBase_eq (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    pairSubBase n m W = pairSubBaseFst n m W := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨absPt w, ⟨w, hw, rfl⟩, (pairBase_absPt n m w).symm⟩
  · rintro ⟨w', ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, pairBase_absPt n m w⟩

end Work.CoreStep
