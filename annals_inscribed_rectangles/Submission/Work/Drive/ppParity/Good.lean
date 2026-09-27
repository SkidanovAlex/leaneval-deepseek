import Mathlib
import Submission.Work.Drive.ppParity.Richness
import Submission.Work.Drive.goodParamsOpen

/-!
# The good parameter set of the pair Sard, and its two forms

The pair analogue of `Work.Drive.goodParamsOpen`'s good set (the *block* form, which is the one the
merged genericity theorem produces), together with its equivalence with the *coordinate* form that the
self-centred `PPRegAt` uses: on the nine-box the block index sets `{bIdx k i : k, i : Fin 3}` and the
coordinate set `Fin 9` coincide (the blocks of the pair's box are `(s,u)`, `y`, `z`).
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted


/-- **The good parameter set of a cut-off pair system** (block form): every zero in `K ∩ unitBox 8` is
regular, and every boundary zero in `K` lies on exactly one *coordinate* of the nine-box (spelled in
the block decomposition `bIdx`), with the derivative restricted to that coordinate hyperplane onto.

This is *definitionally* the set whose openness is `Work.Drive.goodParamsOpen`. -/
def ppGoodSet (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
    EuclideanSpace ℝ (Fin 8)) (K : Set (EuclideanSpace ℝ (Fin 9)))
    (τ : EuclideanSpace ℝ (Fin 8)) : Prop :=
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (τ, y) = 0 →
    Function.Surjective (fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (τ, y')) y)) ∧
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 → Ψ (τ, y) = 0 →
    y ∈ Submission.Drive.unitBoxBdry 8 →
    ∃ (k : Fin 3) (i : Fin 3),
      (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
      (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v (Work.Drive.bIdx k i) = 0} =>
        fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (τ, y')) y v.1))

/-- **The good parameter set is open** — `goodParamsOpen` for the pair system. -/
theorem ppGoodSet_open
    (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8))
    (hΨ : ContDiff ℝ Ctop Ψ) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) :
    IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K τ} :=
  goodParamsOpen 8 Ψ hΨ K hK


/-- The block index map `bIdx` is surjective on `Fin 9`. -/
lemma exists_bIdx_eq (j : Fin 9) : ∃ (k i : Fin 3), Work.Drive.bIdx k i = j :=
  ⟨⟨j.val / 3, by omega⟩, ⟨j.val % 3, by omega⟩, by
    ext
    rw [Work.Drive.bIdx_val, Nat.mod_add_div]⟩

/-- **The charted regularity conclusion of the localized pair Sard at a fixed chart pair.**  This is
the coordinate form of `ppGoodSet`, with the pair map in place of the cut-off system; it is the form in
which `PPRegAt` is read off (via `Work.Drive.PPRegAt_chart_indep`). -/
def PPChartGood {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p p' : M)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (w : ℝ → ℝ) (τ : EuclideanSpace ℝ (Fin 8))
    (K : Set (EuclideanSpace ℝ (Fin 9))) : Prop :=
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
      ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
      Function.Surjective (fderiv ℝ (ppDiff p p' (ppShift Ξ w (unpackFst τ) E)
        (ppShift Ξ w (unpackSnd τ) E') V W) y)) ∧
  (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
      ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
      y ∈ Submission.Drive.unitBoxBdry 8 →
      ∃ i : Fin 9, (y i = 0 ∨ y i = 1) ∧ (∀ j : Fin 9, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (ppDiff p p' (ppShift Ξ w (unpackFst τ) E)
            (ppShift Ξ w (unpackSnd τ) E') V W) y v.1))

end

end Work.Drive
