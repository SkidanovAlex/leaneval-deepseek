import Mathlib
import Submission.Work.Analysis.InverseTheory.AhalfZAPI
import Submission.Work.KMTAreas.A4.norm_AhalfTranspose_le
import Submission.Work.KMTAreas.A4.supportIn_AhalfTranspose
import Submission.Work.KMTContract.Areas

/-!
# The dual function `Ã_N^*(h,g)` is bounded and has small `ℓ¹` mass

The first dual function of the halved average (paper §6, equation `(bkhg)`)

`Ã_N^*(h,g)(x) = (1/N) ∑_{N/2 < n ≤ N} h (x - n) g (x + P(n) - n)`

is bounded pointwise by `‖h‖_∞ ‖g‖_∞`, and — because `N` consecutive shifts of a function
supported in `[-N₀, N₀]` spread it over at most `[-(N₀+N), N₀+N]` — its `ℓ¹` seminorm is at most
`(2 (N₀+N) + 1) ‖h‖_∞ ‖g‖_∞`.

Both statements are the exact analogues, for the dual function, of `norm_AhalfZ_le` and
`ellOne_le_of_supportIn` of `Work.Analysis.InverseTheory.AhalfZAPI` for the forward average
`Ã_N(f,g)`.  They are used in §5 (`A4`) to put the transposed averages into `ℓ¹` uniformly in
the parameters.
-/

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- **Bound for the first dual function.**  If `‖h‖ ≤ Mh` and `‖g‖ ≤ Mg` pointwise then
`‖Ã_N^*(h,g)‖ ≤ Mh * Mg` pointwise; and since `Ã_N^*(h,g)` is supported in `[-(N₀+N), N₀+N]`
when `h, g` are supported in `[-N₀, N₀]` (so at most `2 (N₀+N) + 1` points contribute), its
`ℓ¹` seminorm is at most `(2 (N₀+N) + 1) (Mh * Mg)`. -/
theorem AhalfTransposeBound (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) (N₀ : ℕ)
    (hh : Work.Analysis.InverseTheory.SupportIn h N₀)
    (hg : Work.Analysis.InverseTheory.SupportIn g N₀)
    {Mh Mg : ℝ} (hMh : 0 ≤ Mh) (hMg : 0 ≤ Mg)
    (hhb : ∀ x : ℤ, ‖h x‖ ≤ Mh) (hgb : ∀ x : ℤ, ‖g x‖ ≤ Mg) :
    (∀ x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ ≤ Mh * Mg) ∧
      Work.Analysis.InverseTheory.ellOne (Work.Analysis.InverseTheory.AhalfTranspose N P h g)
        ≤ (2 * ((N₀ : ℝ) + (N : ℝ)) + 1) * (Mh * Mg) := by
  have hpt : ∀ x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ ≤ Mh * Mg :=
    fun x => norm_AhalfTranspose_le N P h g hMh hMg hhb hgb x
  refine ⟨hpt, ?_⟩
  have hsupp : Work.Analysis.InverseTheory.SupportIn
      (Work.Analysis.InverseTheory.AhalfTranspose N P h g) (N₀ + N) :=
    supportIn_AhalfTranspose (N := N) (M := N₀) (P := P) (g := g) hh
  have hb := Work.Analysis.InverseTheory.ellOne_le_of_supportIn
    (Work.Analysis.InverseTheory.AhalfTranspose N P h g) (N₀ + N) hsupp (C := Mh * Mg) hpt
  simpa only [Nat.cast_add] using hb

end Work.KMTAreas.A4
