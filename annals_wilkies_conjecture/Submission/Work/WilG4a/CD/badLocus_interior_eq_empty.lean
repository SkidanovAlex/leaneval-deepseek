/-
  WilG4a / CD — the bad locus of a definable family member has empty interior.

  For a family member `f : ℝᵖ → ℝ → ℝ` whose graph is `Ω`-definable with format `F0` and
  degree `D` (i.e. `graphFam f ∈ S.Ω F0 D (p+1+1)`), the set

    `badLocus f j = (smoothLocus f j)ᶜ`,   `smoothLocus f j = interior {x | ContDiffAt ℝ j (famFun f) x}`

  has empty interior.  The two ingredients are:

  * the `C^j` locus of `famFun f` is *open* (`C^j` is a local property, Mathlib's
    `ContDiffAt.eventually`), hence `smoothLocus f j` is the `C^j` locus itself and
    `badLocus f j` is exactly the non-`C^j` locus;
  * the non-`C^j` locus of a definable function has empty interior: `smooth_k_cover` exhibits
    it inside a finite union of `Ω`-sets of empty interior, and `thin_union` (sharp cell
    decomposition) kills finite unions of thin `Ω`-sets.
-/
import Mathlib
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG1.Cell.thin_closure

namespace Work.WilG4a.CD

open Work.WilG4a
open scoped Topology

/-! ## The `C^j` locus is open -/

/-- The set of points at which a family member is `C^j` is open: `C^j` is a local property. -/
theorem isOpen_contDiffAt_famFun {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    IsOpen {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (famFun f) x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ContDiffAt ℝ j (famFun f) x := by simpa using hx
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ j (famFun f) y := hx'.eventually (by simp)
  exact hev

/-- Consequently `smoothLocus f j` — the *interior* of the `C^j` locus — is the `C^j`
locus itself. -/
theorem smoothLocus_eq_contDiffAt {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    smoothLocus f j = {x : Fin (p + 1) → ℝ | ContDiffAt ℝ j (famFun f) x} :=
  (isOpen_contDiffAt_famFun f j).interior_eq

/-- `badLocus f j` is exactly the locus where `famFun f` fails to be `C^j`. -/
theorem badLocus_eq_compl_contDiffAt {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (j : ℕ) :
    badLocus f j = {x : Fin (p + 1) → ℝ | ¬ ContDiffAt ℝ j (famFun f) x} := by
  rw [badLocus, smoothLocus_eq_contDiffAt f j]
  ext x
  simp

/-! ## The non-`C^j` locus is thin -/

/-- The locus where a definable family member is not `C^j` has empty interior.

This is `WilG1.G1_generic_smooth` in the coordinates of `famFun`: `smooth_k_cover` covers the
non-`C^j` locus by finitely many `Ω`-sets of empty interior, and `thin_union` shows that a
finite union of thin `Ω`-sets is thin. -/
theorem interior_compl_contDiffAt_famFun (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (p F0 : ℕ) :
    ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
      interior {x : Fin (p + 1) → ℝ | ¬ ContDiffAt ℝ j (famFun f) x} = ∅ := by
  intro D j f hf
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) hcd (famFun f)
      (by simpa [graphOf_famFun] using hf) (k := j)
  have hthin : interior (⋃ i : Fin m, A i) = ∅ :=
    Work.WilG1.Cell.thin_union hcd m a b D A hA hint
  refine Set.eq_empty_of_subset_empty ?_
  calc interior {x : Fin (p + 1) → ℝ | ¬ ContDiffAt ℝ j (famFun f) x}
      ⊆ interior (⋃ i : Fin m, A i) := interior_mono hsub
    _ = ∅ := hthin

/-! ## Main statement -/

theorem badLocus_interior_eq_empty (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (p F0 : ℕ) :
    ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
      interior (Work.WilG4a.badLocus f j) = ∅ := by
  intro D j f hf
  rw [badLocus_eq_compl_contDiffAt f j]
  exact interior_compl_contDiffAt_famFun S hcd p F0 D j hf

end Work.WilG4a.CD
