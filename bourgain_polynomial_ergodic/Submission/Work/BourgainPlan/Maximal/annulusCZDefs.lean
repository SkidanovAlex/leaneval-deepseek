import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.lwtCZDefs

/-!
# The Calderón--Zygmund vocabulary of the (ii-e) assembly

`WINDOW_WEAK_TYPE_STATUS_S10.md` §10 step 2/3: the weak-`(1,1)` bound for the annulus square
function `annulusSqfun` is proved by the classical Calderón--Zygmund decomposition of
`σ = ‖f‖ₑ` at the level `c`, with the maximal dyadic cells `czMax σ c` (from `dyCZ.lean` /
`lwtCZDefs.lean`).

This file fixes the objects.  The decomposition is defined **bad part first**, which is what makes
the formalisation short:

* `czBadPiece f p = (f - ⨏_{dyCell p} f) · 1_{dyCell p}` is the mean-zero piece of the cell `p`;
* `czBad f σ c = Σ'_{p ∈ czMax σ c} czBadPiece f p` — a sum with **at most one nonzero term at any
  point** (the maximal cells are pairwise disjoint), so it is a.e.-measurable by
  `AEMeasurable.tsum` and vanishes off the CZ set `lwtOm σ c`;
* `czGood f σ c = f - czBad f σ c` — on every maximal cell it equals the complex cell average
  `czCellAvgC f p` (by `czMax_eq_of_mem`), and off the CZ set it equals `f`; it is a.e.-measurable
  *for free*, being a difference of two a.e.-measurable functions, which is exactly why the good
  part is defined this way rather than as a `choose`-of-cell;
* `czStar σ c` is the enlargement of the CZ set by the intervals `[c_p - 2^{n_p+1}, c_p +
  2^{n_p+1}]` around the pivots `c_p = k·2^n` (the left endpoints of the cells, which is the pivot
  used by the kernel estimate `annulusKernel_translation`).  It is chosen so that its complement
  lies in the region `{|x - c_p| > 2^{n_p+1}}` of `AnnulusBadPartBound b`, for **every** maximal
  cell `p` simultaneously.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

/-- The complex average of `f` over the dyadic cell `p = (n,k)`:
`czCellAvgC f p = (2^n)⁻¹ • ∫_{dyCell p} f`.  The scalar is real (the length of the cell is
`2^n`), so that `2^n • czCellAvgC f p = ∫_{dyCell p} f` by `smul_smul`, matching the shape of the
cell-average estimate `czMax_avg_le`. -/
noncomputable def czCellAvgC (f : ℝ → ℂ) (p : ℤ × ℤ) : ℂ :=
  ((2 : ℝ) ^ p.1)⁻¹ • ∫ y in dyCell p.1 p.2, f y

/-- The mean-zero piece of the cell `p`: `czBadPiece f p = (f - ⨏_{dyCell p} f) · 1_{dyCell p}`. -/
noncomputable def czBadPiece (f : ℝ → ℂ) (p : ℤ × ℤ) : ℝ → ℂ :=
  fun x => if x ∈ dyCell p.1 p.2 then f x - czCellAvgC f p else 0

/-- The Calderón--Zygmund bad part at level `c`: the sum of the mean-zero pieces over the maximal
cells `czMax σ c`. -/
noncomputable def czBad (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : ℝ → ℂ :=
  fun x => ∑' p : ℤ × ℤ, if p ∈ czMax σ c then czBadPiece f p x else 0

/-- The Calderón--Zygmund good part at level `c`: `czGood f σ c = f - czBad f σ c`. -/
noncomputable def czGood (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : ℝ → ℂ :=
  fun x => f x - czBad f σ c x

/-- The enlargement of the Calderón--Zygmund set used by the bad-part kernel estimate: the union,
over the maximal cells `p`, of the intervals of radius `2^{n_p+1}` centred at the pivots
`c_p = k·2^n` (the left endpoints).  Its complement is contained in the region
`{|x - c_p| > 2^{n_p+1}}` of `AnnulusBadPartBound`, for every maximal cell `p`. -/
noncomputable def czStar (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Set ℝ :=
  ⋃ p ∈ czMax σ c, Set.Icc (((p.2 : ℝ) * (2 : ℝ) ^ p.1) - (2 : ℝ) ^ (p.1 + 1))
    (((p.2 : ℝ) * (2 : ℝ) ^ p.1) + (2 : ℝ) ^ (p.1 + 1))

/-- The `ℓ²` triangle inequality for the square function: `S(f - g) = S((f - g))`, i.e. the bad
part of the CZ decomposition satisfies `S(β) ≤ Σ'_p S(β_p)`.  Stated here as the elementary fact
that the square function of a sum of two functions is at most the sum. -/
noncomputable def czNormFn (f : ℝ → ℂ) : ℝ → ℝ≥0∞ := fun x => ‖f x‖ₑ

end Work.BourgainPlan.Maximal
