import Mathlib
import Submission.Work.Drive.PushDisc.whitneyChart

/-!
# `Work.Drive.PushDisc.IsWhitneyDisc`: the smooth Whitney disc of a bigon

This is the conclusion of `Work.Drive.Whitney.whitneyDiscSmooth` (the general-position step of the
lead's design audit, 2026-09-25 10:10) packaged as a predicate, so that the *framing* step
(`Work.Drive.PushDisc.whitneyChart_of_disc`) can take the disc as a single hypothesis.

The disc is a `C^∞` map `D : ℝ × ℝ → ℝ^{2n}` on the strip `[-1,1] × [0,1]`:

* the two sides `t = 0`, `t = 1` are the two arcs of the bigon (`x ↦ f (γᵢ ((x+1)/2))`), the two
  ends `x = ±1` are constant (so the boundary of the strip is the closed loop `f ∘ γ₁ ∪ f ∘ γ₂`);
* the interior of the strip maps into the complement of `f '' M` (this is the "cap"/free region of
  the Whitney move — the direction the finger is pushed through);
* `D` is injective on the interior strip;
* `D` meets the image `f '' M` *transversally* along the two sides (`∂ₜD ∉ range (mfderiv f …)`), the
  collaring condition that makes the normal frame of the disc well behaved near the boundary and is
  what the framing step consumes.  The transversality is imposed on the **open** parameter interval
  `Ioo (-1) 1`: at `x = ±1` the side is a single point (`D (x,·)` is constant), so the directional
  derivative there is `0`, which always lies in the range of a linear map.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The smooth Whitney disc of the bigon** (the conclusion of
`Work.Drive.Whitney.whitneyDiscSmooth`). -/
def IsWhitneyDisc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (γ₁ γ₂ : ℝ → M)
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D ∧
  (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 0) = f (γ₁ ((x + 1) / 2))) ∧
  (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 1) = f (γ₂ ((x + 1) / 2))) ∧
  (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D ((-1 : ℝ), t) = f (γ₁ 0)) ∧
  (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D (1, t) = f (γ₁ 1)) ∧
  Set.InjOn D (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∧
  D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩ (f '' (Set.univ : Set M)) = ∅ ∧
  (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
    fderiv ℝ D (x, 0) (0, 1) ∉ (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₁ ((x + 1) / 2))).range) ∧
  (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
    fderiv ℝ D (x, 1) (0, 1) ∉ (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₂ ((x + 1) / 2))).range)

/-- **The disc predicate holds for the conclusion of `whitneyDiscSmooth`** (the packaging used by
the framing step). -/
theorem isWhitneyDisc_of_conj {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {γ₁ γ₂ : ℝ → M}
    {D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 0) = f (γ₁ ((x + 1) / 2))) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → D (x, 1) = f (γ₂ ((x + 1) / 2))) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D ((-1 : ℝ), t) = f (γ₁ 0)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → D (1, t) = f (γ₁ 1)) ∧
      Set.InjOn D (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∧
      D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩ (f '' (Set.univ : Set M)) = ∅ ∧
      (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        fderiv ℝ D (x, 0) (0, 1) ∉ (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₁ ((x + 1) / 2))).range) ∧
      (∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
        fderiv ℝ D (x, 1) (0, 1) ∉ (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₂ ((x + 1) / 2))).range)) :
    IsWhitneyDisc f γ₁ γ₂ D :=
  h

end Work.Drive.PushDisc
