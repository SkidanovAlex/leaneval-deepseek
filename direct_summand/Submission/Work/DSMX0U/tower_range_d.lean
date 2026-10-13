import Mathlib
import Submission.Work.DSMX0U.Cell
import Submission.Work.DSMX0U.Cells

/-!
# DSMX0U — the range of the differential of the tower

The differential of a cell `Cell A C c₀ q` is

`Cell.dHom A = coprod 0 ((Kprev).subtype ∘ cov) : gen × rel ⟶ Gprev`

so its range is the image of the relations `rel` in `Gprev`, which is `Kprev` because
`cov : rel ↠ Kprev` is surjective (`Cell.hcov`) and `Kprev.subtype` has range `Kprev`.

The step `stepCell` takes the cell `s : Cell A C c₀ q` to the cell in degrees `[q - 2, q - 1]`
whose `Kprev` is `s.K` and whose `cov` is `sd.cov`.  Hence the range of the differential of the
cell produced by a step is exactly the excess kernel `Cell.K` of the cell it was produced from,
which for the tower says `range (tower (k+1)).dHom = (tower k).K`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- **The range of the differential of a cell produced by a step** is the excess kernel `Cell.K`
of the cell the step was taken from.  This is the form of the statement which is *definitional*:
`stepCell` re-uses the given cell as its predecessor, so its `Kprev` (the target of the range) is
literally `s.K`, and its `cov` is `sd.cov`, which is surjective by `sd.hcov`. -/
theorem stepCell_range_dHom {q : ℤ} (s : Cell A C c₀ q) (sd : StepData A s) :
    LinearMap.range ((stepCell A s sd).dHom A) = s.K A := by
  -- `stepCell` is a structure literal, so `dHom` unfolds definitionally to the coproduct of the
  -- zero map on the generators with the structure map of the relations.
  rw [show (stepCell A s sd).dHom A =
      LinearMap.coprod (0 : ↥sd.gen →ₗ[A] ↥(s.G A)) ((s.K A).subtype ∘ₗ sd.cov) from rfl]
  -- the range of the coproduct is the supremum of the two ranges, and the first is `⊥`
  rw [LinearMap.range_coprod, LinearMap.range_comp, LinearMap.range_eq_top.mpr sd.hcov]
  simp

theorem tower_range_d {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1)) (k : ℕ) :
    LinearMap.range ((Work.DSMX0U.tower hstep M s₀ (k + 1)).dHom A) =
      (Work.DSMX0U.tower hstep M s₀ k).K A := by
  -- level `k + 1` of the tower is *definitionally* the step taken from level `k`
  -- (`Work.DSMX0U.tower_succ`), so the lemma above applies directly; `rw` cannot be used here
  -- because the target of the range is the `Gprev` field of the cell, on which the type of the
  -- goal depends.
  exact stepCell_range_dHom (tower hstep M s₀ k)
    (hstep (levelDeg M k) (tower hstep M s₀ k))

end Work.DSMX0U
