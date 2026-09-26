import Mathlib
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# The plane statement behind the removal lemma

Vocabulary for `Work.BoxShrink.Pinch.PlanePathExists`, the planar statement to which the removal
lemma `Work.BoxShrink.Pinch.RemovalInput` reduces through the covering space `ℝ² → F` of a
parametrised torus (see `Submission/Work/BoxShrink/Pinch/removalInput_of_torusCover.lean`).

* `Work.TorusCover.periodShift k` is the period vector `2π k ∈ ℝ²` (the underlying map of the
  covering `ℝ² → T²`);
* `Work.BoxShrink.Pinch.orbit J` is the union of the lattice translates of `J`;
* `Work.BoxShrink.Pinch.LatticeDisjoint J` says that no two distinct points of `J` differ by a
  nonzero period vector — the "embeddedness" of `J` in the torus;
* `Work.BoxShrink.Pinch.PlanePathExists` is the statement: for `J` the trace of a periodic simple
  curve with pairwise disjoint lattice translates, every period shift `2πv` is realised by a path
  avoiding the orbit of `J`.
-/

namespace Work.BoxShrink.Pinch

/-- The orbit of a set `J ⊆ ℝ²` under the period lattice `2πℤ²`. -/
def orbit (J : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | ∃ j ∈ J, ∃ k : ℤ × ℤ, p = j + Work.TorusCover.periodShift k}

theorem mem_orbit_iff {J : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ orbit J ↔ ∃ j ∈ J, ∃ k : ℤ × ℤ, p = j + Work.TorusCover.periodShift k := Iff.rfl

/-- A set `J ⊆ ℝ²` has *disjoint translates* if no point of `J` is the translate of another by a
nonzero period vector.  For the trace of a periodic simple curve this is the statement that the
curve is embedded in the torus `ℝ²/2πℤ²`. -/
def LatticeDisjoint (J : Set (ℝ × ℝ)) : Prop :=
  ∀ (x y : ℝ × ℝ), x ∈ J → y ∈ J → x ≠ y → ∀ k : ℤ × ℤ, y ≠ x + Work.TorusCover.periodShift k

/-- **The plane statement.**  For `J` the trace of a periodic curve whose lattice translates are
pairwise disjoint (the lift of an embedded simple closed curve of the torus), every period shift
`2πv` is realised by a path avoiding the orbit of `J`: there is a continuous `Λ : ℝ → ℝ²` with
`Λ (t + 2π) = Λ t + 2πv` whose image avoids `orbit J`. -/
def PlanePathExists : Prop :=
  ∀ J : Set (ℝ × ℝ),
    (∃ γ : ℝ → ℝ × ℝ, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = J) →
    LatticeDisjoint J →
    ∀ v : ℤ × ℤ,
      ∃ Λ : ℝ → ℝ × ℝ, Continuous Λ ∧
        (∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t + Work.TorusCover.periodShift v) ∧
        ∀ t : ℝ, Λ t ∉ orbit J

end Work.BoxShrink.Pinch
