import Submission.Work.Smooth.Jordan.Separation

/-!
# Finite families of pairwise disjoint curves on a surface: nesting and innermost

This file sets up the API for a finite family of pairwise disjoint simple closed curves on a
surface `A ⊆ ℝ³` (in the application, the round sphere or the boundary of Pardon's box), each of
which bounds an embedded disc in `A` and whose discs are nested.

The datum is `FamilyDiscs A ι c`: the curves `c i`, their spanning discs `disc i`, and a rank
`rank : ι → ℕ` decreasing when a curve meets the interior of the disc of another (this is the
*standard position* of finitely many disjoint Jordan curves on `S²`, and it is what makes the
innermost argument work).

From it are derived, in this file and its siblings:

* `FamilyDiscs.exists_innermost` — some curve of the family bounds a disc whose interior meets no
  curve of the family: **Pardon's "take a curve innermost in `S`"**;
* the *containment relation* `FamilyDiscs.InsideOpen` and the proof that it is a strict partial
  order (`FamilyDiscs.insideOpen_irrefl`, `FamilyDiscs.insideOpen_trans`);
* the usable form of the innermost output, `FamilyDiscs.exists_innermost_curve`.

The containment relation is stated on the index type: `InsideOpen h i j` means that the curve `c i`
meets the *interior* of the disc spanned by `c j`, i.e. that `c i` lies inside `c j` in the
nesting.
-/

open Set
open Classical
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-- **A finite family of pairwise disjoint simple closed curves on a surface `A ⊆ ℝ³`, each bounding
an embedded disc in `A`, with nested discs.**

The nesting is witnessed by `rank` (a curve meeting the interior of the disc of another has smaller
rank) and by `inside_subset` (if a curve meets the interior of the disc of another then its own disc
is contained in that disc); these are the two classical properties of finitely many disjoint Jordan
curves on a `2`-sphere in *standard position*. -/
structure FamilyDiscs (A : Set R3) (ι : Type) [Fintype ι] (c : ι → ℝ → R3) where
  /-- each curve is a simple closed curve in `A` -/
  simple : ∀ i : ι, IsSimpleClosedCurveOn A (c i)
  /-- distinct curves are disjoint -/
  disjoint : Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))
  /-- the disc spanned by each curve -/
  disc : ι → C(Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- the boundary of the disc is the curve -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ, disc i (circlePoint θ) = c i θ
  /-- the disc lies in the surface -/
  disc_mem : ∀ i : ι, ∀ z : Disc, disc i z ∈ A
  /-- the nesting rank -/
  rank : ι → ℕ
  /-- a curve meeting the interior of the disc of another has smaller rank -/
  nested : ∀ i j : ι, i ≠ j →
    (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j)) → rank j < rank i
  /-- a curve meeting the interior of the disc of another lies inside that disc -/
  inside_subset : ∀ i j : ι,
    (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j)) →
      Set.range (disc j) ⊆ Set.range (disc i)

namespace FamilyDiscs

variable {A : Set R3} {ι : Type} [Fintype ι] {c : ι → ℝ → R3}

/-- The **containment relation**: the curve `c i` lies strictly inside the curve `c j`, i.e. it
meets the interior of the disc spanned by `c j`. -/
def InsideOpen (h : FamilyDiscs A ι c) (i j : ι) : Prop :=
  ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.disc j z ∈ Set.range (c i)

/-- The curve of index `j` is contained in the closed disc of index `i`. -/
def Inside (h : FamilyDiscs A ι c) (i j : ι) : Prop := Set.range (c j) ⊆ Set.range (h.disc i)

theorem insideOpen_iff (h : FamilyDiscs A ι c) (i j : ι) :
    h.InsideOpen i j ↔ ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ h.disc j z ∈ Set.range (c i) := Iff.rfl

theorem inside_iff (h : FamilyDiscs A ι c) (i j : ι) :
    h.Inside i j ↔ Set.range (c j) ⊆ Set.range (h.disc i) := Iff.rfl

/-- The interior of a spanning disc meets the trace of the curve it spans in no point: a point of
the curve inside the disc would be the image of a boundary point under the embedding, and the
boundary points of `𝔻` have norm `1`. -/
theorem not_insideOpen_self (h : FamilyDiscs A ι c) (i : ι) : ¬ h.InsideOpen i i := by
  rintro ⟨z, hz, hzmem⟩
  obtain ⟨θ, hθ⟩ := hzmem
  have hz' : z = circlePoint θ := h.disc_inj i (by rw [hθ.symm, h.disc_boundary i θ])
  subst hz'
  have hone : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
    rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  rw [hone] at hz
  exact absurd hz (lt_irrefl 1)

/-- **Pardon's innermost curve**: in a finite non-empty family of pairwise disjoint simple closed
curves with nested spanning discs, some curve bounds a disc whose interior meets no curve of the
family. -/
theorem exists_innermost (h : FamilyDiscs A ι c) [Nonempty ι] :
    ∃ i : ι, ∀ j : ι, ¬ h.InsideOpen j i := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι) h.rank hne
  refine ⟨i, fun j hj => ?_⟩
  by_cases hji : j = i
  · rw [hji] at hj
    exact h.not_insideOpen_self i hj
  · exact absurd (hmin j (Finset.mem_univ j)) (not_le.mpr (h.nested i j (Ne.symm hji) hj))

/-- The usable form of the innermost datum: a curve `c i` whose spanning disc has interior disjoint
from every curve of the family. -/
theorem exists_innermost_curve (h : FamilyDiscs A ι c) [Nonempty ι] :
    ∃ i : ι, ∀ j : ι,
      Disjoint (Set.range (c j)) (h.disc i '' {z : Disc | ‖(z : ℂ)‖ < 1}) := by
  obtain ⟨i, hi⟩ := h.exists_innermost
  refine ⟨i, fun j => Set.disjoint_left.mpr fun x hxj hxi => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hxi
  exact hi j ⟨z, hz, hxj⟩

end FamilyDiscs

end

end Work.Smooth.Jordan
