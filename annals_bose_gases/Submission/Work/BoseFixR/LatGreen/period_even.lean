import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatGreen.CellDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

open scoped BigOperators Real BigOperators RealInnerProductSpace
open MeasureTheory Set

/-- Negation of the lattice labels, as an involution of `ℤ³`. -/
private def negLabE : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) := Equiv.neg (Fin 3 → ℤ)

private lemma negLabE_apply (n : Fin 3 → ℤ) : negLabE n = -n := rfl

/-- Negation of the lattice vectors.  (Local private copy of `integrableOn_period.lat_neg`, kept
here so that this glue lemma depends on `CellDefs` alone.) -/
private lemma lat_neg_local (ℓ : ℝ) (n : Fin 3 → ℤ) :
    Work.BoseFixR.lat ℓ (-n) = -Work.BoseFixR.lat ℓ n := by
  simpa only [Work.BoseFixR.latHom_apply] using map_neg (Work.BoseFixR.latHom ℓ) n

/-- **`period_even`** (glue obligation 1 of `farLatRow.lean`'s note): the `ℓ`-periodisation of an
even charge is even.

`period W ℓ (-x) = period W ℓ x` whenever `∀ x, W (-x) = W x`.

Route: unfold `period`; `-x - lat ℓ n = -(x + lat ℓ n)`, so `hW` rewrites each summand to
`W (x + lat ℓ n)`, and `Equiv.tsum_eq (Equiv.neg _)` reindexes `n ↦ -n` (with
`lat ℓ (-n) = -lat ℓ n`) to `Σ'_n W (x - lat ℓ n)`.  Only `hW`, `tsum_congr` and `Equiv.tsum_eq`
(unconditional) are used — no summability side condition, and it holds uniformly in `ℓ`, including
`ℓ = 0`.  Needed by `LatGreen.CollapseCell`'s `hP` at `P = period (W1fun v h ℓ) ℓ` (with
`isEven_W1fun` supplying the evenness of `W₁`). -/
theorem period_even {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : ∀ x, W (-x) = W x) (ℓ : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.LatGreen.period W ℓ (-x) = Work.BoseFixR.LatGreen.period W ℓ x := by
  rw [period, period]
  -- each summand of the reflected periodisation is an even charge evaluated at `x + lat ℓ n`
  have hstep : ∀ n : Fin 3 → ℤ,
      W (-x - Work.BoseFixR.lat ℓ n) = W (x + Work.BoseFixR.lat ℓ n) := fun n => by
    rw [show -x - Work.BoseFixR.lat ℓ n = -(x + Work.BoseFixR.lat ℓ n) by abel, hW]
  rw [tsum_congr hstep]
  -- reindex the lattice labels by the involution `n ↦ -n`
  rw [← negLabE.tsum_eq (fun n : Fin 3 → ℤ => W (x + Work.BoseFixR.lat ℓ n))]
  exact tsum_congr fun n => by
    simp only [negLabE_apply n, lat_neg_local ℓ n, sub_eq_add_neg]

end Work.BoseFixR.LatGreen
