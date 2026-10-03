import Mathlib
import Submission.Work.Dim.Setup

/-!
# Disjointness of the cylinder pieces of a conformal IFS

Let `τ : Fin N → ℂ → ℂ` be branches that map `ball p r` into `ball p (r/2)`, are injective on
`ball p r`, and have pairwise disjoint images of `ball p r`.  The "piece" of a word `w` is
`piece τ p r w = ifsComp τ w '' closedBall p (r/2)`.  We show that two pieces whose words are
incomparable (neither is a prefix of the other) are disjoint.

The proof is by induction on the first word.  If the two words start with different letters the
claim follows from the disjointness of the level-one images; if they start with the same letter the
claim follows from the induction hypothesis together with injectivity of that branch (which is
legitimate because every piece is contained in `ball p (r/2) ⊆ ball p r`).
-/

namespace Work.Dim.Pieces

open Set Metric

variable {N : ℕ}

/-! ### Elementary structure of the pieces -/

/-- Composition along a concatenation. -/
theorem ifsComp_append' {τ : Fin N → ℂ → ℂ} (w v : List (Fin N)) :
    MandelDim.ifsComp τ (w ++ v) = MandelDim.ifsComp τ w ∘ MandelDim.ifsComp τ v := by
  induction w with
  | nil => simp [MandelDim.ifsComp]
  | cons i w ih => simp [MandelDim.ifsComp, ih, Function.comp_assoc]

/-- The piece of a concatenation. -/
theorem piece_append' (τ : Fin N → ℂ → ℂ) (p : ℂ) (r : ℝ) (w v : List (Fin N)) :
    Work.Dim.piece τ p r (w ++ v) = MandelDim.ifsComp τ w '' Work.Dim.piece τ p r v := by
  simp [Work.Dim.piece, ifsComp_append', Set.image_image]

/-- The piece of a nonempty word unfolds over its first letter. -/
theorem piece_cons (τ : Fin N → ℂ → ℂ) (p : ℂ) (r : ℝ) (i : Fin N) (a : List (Fin N)) :
    Work.Dim.piece τ p r (i :: a) = τ i '' Work.Dim.piece τ p r a := by
  have h := piece_append' τ p r [i] a
  simpa [MandelDim.ifsComp] using h

/-- Each branch maps the inner closed ball into itself. -/
theorem branch_mapsTo_closedBall {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ i, MapsTo (τ i) (closedBall p (r / 2)) (closedBall p (r / 2)) := by
  intro i z hz
  rw [mem_closedBall] at hz ⊢
  have hzr : z ∈ ball p r := by rw [mem_ball]; linarith
  have h := hmaps i hzr
  rw [mem_ball] at h
  linarith

/-- Every composition maps the inner closed ball into itself. -/
theorem ifsComp_branch_mapsTo_closedBall' {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N),
      MapsTo (MandelDim.ifsComp τ w) (closedBall p (r / 2)) (closedBall p (r / 2)) := by
  intro w
  induction w with
  | nil => intro z hz; simpa [MandelDim.ifsComp] using hz
  | cons i a ih =>
      intro z hz
      show τ i (MandelDim.ifsComp τ a z) ∈ closedBall p (r / 2)
      exact branch_mapsTo_closedBall hr hmaps i (ih hz)

/-- A piece is contained in the inner closed ball. -/
theorem piece_subset_closedBall {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) :
    ∀ w : List (Fin N), Work.Dim.piece τ p r w ⊆ closedBall p (r / 2) := by
  intro w
  induction w with
  | nil => intro z hz; simpa [Work.Dim.piece, MandelDim.ifsComp] using hz
  | cons i a ih =>
      rw [piece_cons]
      exact Subset.trans (Set.image_mono ih) (branch_mapsTo_closedBall hr hmaps i).image_subset

/-- A piece is contained in the outer ball, where the branches are injective. -/
theorem piece_subset_ball {τ : Fin N → ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2))) (w : List (Fin N)) :
    Work.Dim.piece τ p r w ⊆ ball p r := by
  intro z hz
  have h := piece_subset_closedBall hr hmaps w hz
  rw [mem_closedBall] at h
  rw [mem_ball]
  linarith

/-- An injective map sends disjoint subsets of its domain of injectivity to disjoint sets. -/
theorem image_disjoint_image_of_injOn {f : ℂ → ℂ} {s t u : Set ℂ} (hinj : InjOn f s)
    (ht : t ⊆ s) (hu : u ⊆ s) (h : Disjoint t u) : Disjoint (f '' t) (f '' u) := by
  rw [Set.disjoint_left] at h ⊢
  rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
  have hyz : y = z := hinj (ht hy) (hu hz) hzy.symm
  exact h hy (hyz.symm ▸ hz)

/-! ### The main disjointness statement -/

theorem disjoint {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (r : ℝ) (hr : 0 < r)
    (hmaps : ∀ i, Set.MapsTo (τ i) (Metric.ball p r) (Metric.ball p (r / 2)))
    (hτ : ∀ i, Set.InjOn (τ i) (Metric.ball p r))
    (hdisj : Pairwise fun i j => Disjoint (τ i '' Metric.ball p r) (τ j '' Metric.ball p r)) :
    ∀ w w' : List (Fin N), ¬ w <+: w' → ¬ w' <+: w →
      Disjoint (Work.Dim.piece τ p r w) (Work.Dim.piece τ p r w') := by
  intro w
  induction w with
  | nil => intro w' h1 _; exact absurd List.nil_prefix h1
  | cons i a ih =>
      intro w' h1 h2
      cases w' with
      | nil => exact absurd List.nil_prefix h2
      | cons j b =>
          by_cases hij : i = j
          · cases hij
            rw [piece_cons, piece_cons]
            refine image_disjoint_image_of_injOn (hτ i) (piece_subset_ball hr hmaps a)
              (piece_subset_ball hr hmaps b) ?_
            rw [List.cons_prefix_cons] at h1 h2
            exact ih b (fun h => h1 ⟨rfl, h⟩) (fun h => h2 ⟨rfl, h⟩)
          · rw [piece_cons, piece_cons]
            exact Disjoint.mono (Set.image_mono (piece_subset_ball hr hmaps a))
              (Set.image_mono (piece_subset_ball hr hmaps b)) (hdisj hij)

end Work.Dim.Pieces
