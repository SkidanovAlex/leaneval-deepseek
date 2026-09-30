import Mathlib
import Submission.Work.MbarHomology.Mbar.Flags
import Submission.Work.MbarHomology.ConvexCells.sd_realization_of_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of the barycentre map on the flags of `Q̄`

The `k`-simplices of the barycentric subdivision of `Q̄` are the flags of `Q̄`, i.e. the strictly
increasing `(k+1)`-tuples of faces `Simplex QbarCW.Cell k`.  The subdivision is *simplicial* only
because the barycentre map

`bary s = (k+1)⁻¹ • ∑ i, posR (s i)`

is injective: two different flags must have different barycentres, otherwise the attached open
simplices would overlap.

The proof is the one used for the general uniqueness of flag points
(`Work.MbarHomology.ConvexCells.flagPt_unique_basic`, the version resting only on the decidable
basic checks `QbarPD_okBasic`): the uniform-weight flag point `flagPtOf s` has realization exactly
`bary s`, and two flag points with the same realization have the same flag list.  Reading off the
indices of that list recovers `s`.
-/

set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology.Mbar

open Work.Subdivision Work.ConvexCells
open Work.MbarHomology.ConvexCells
open scoped BigOperators

noncomputable section

/-- The index of the `j`-th face of a flag of `Q̄`. -/
private def cellIdx {k : ℕ} (s : Simplex QbarCW.Cell k) (j : Fin (k + 1)) : Fin QbarPD.K :=
  (s j).idx

/-- The flag point of a flag with the uniform weights. -/
private def flagPtOf {k : ℕ} (s : Simplex QbarCW.Cell k) : QbarPD.FlagPt where
  flag := List.ofFn (fun j : Fin (k + 1) => cellIdx s j)
  isFlag := by
    rw [PolytopeData.IsFlag, List.pairwise_ofFn]
    intro i j hij
    show qTight (s j).idx ⊂ qTight (s i).idx
    refine Finset.ssubset_iff_subset_ne.mpr ⟨le_of_lt (s.strictMono hij), fun heq => ?_⟩
    apply not_le_of_gt (s.strictMono hij)
    show qTight (s i).idx ⊆ qTight (s j).idx
    rw [← heq]
  wt := fun _ => ((k + 1 : ℝ))⁻¹
  wt_pos := fun _ => by positivity
  wt_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, List.length_ofFn, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (by positivity)

private theorem bary_eq_sum {k : ℕ} (s : Simplex QbarCW.Cell k) :
    bary s = ∑ i : Fin (k + 1), ((k + 1 : ℝ))⁻¹ • QbarPD.posR (cellIdx s i) := rfl

private theorem ofFn_get_sum {n : ℕ} {α : Type*} (f : Fin n → α) (g : α → E 4) :
    (∑ i : Fin (List.ofFn f).length, g ((List.ofFn f).get i)) = ∑ j : Fin n, g (f j) := by
  rw [← Equiv.sum_comp (Fin.castOrderIso (List.length_ofFn (f := f)) :
      Fin (List.ofFn f).length ≃ Fin n) (fun j : Fin n => g (f j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [List.get_ofFn]
  congr 2

/-- The affine realization of the flag point of a flag is its barycentre. -/
private theorem flagPtOf_toE' {k : ℕ} (s : Simplex QbarCW.Cell k) :
    (flagPtOf s).toE' = bary s := by
  rw [bary_eq_sum]
  rw [show (flagPtOf s).toE'
      = ∑ i : Fin (List.ofFn (fun j : Fin (k+1) => cellIdx s j)).length,
          ((k+1:ℝ))⁻¹ • QbarPD.posR ((List.ofFn (fun j : Fin (k+1) => cellIdx s j)).get i)
      from rfl]
  rw [ofFn_get_sum (f := fun j : Fin (k+1) => cellIdx s j)
      (g := fun c => ((k+1:ℝ))⁻¹ • QbarPD.posR c)]

/-- **The barycentre map is injective on the flags of `Q̄`.**  The uniform-weight flag point of a
flag has realization its barycentre, and flag points with equal realization have equal flag lists;
reading off the entries of that list recovers the flag. -/
theorem bary_inj {k : ℕ} {s t : Work.Subdivision.Simplex Work.MbarHomology.QbarCW.Cell k}
    (h : Work.MbarHomology.bary s = Work.MbarHomology.bary t) : s = t := by
  have h2 : (flagPtOf s).toE' = (flagPtOf t).toE' := by rw [flagPtOf_toE', flagPtOf_toE', h]
  have h3 : flagPtOf s = flagPtOf t :=
    flagPt_unique_basic QbarPD QbarPD_okBasic (flagPtOf s) (flagPtOf t) h2
  have h4 : (fun j : Fin (k+1) => cellIdx s j) = (fun j : Fin (k+1) => cellIdx t j) := by
    have h5 := congrArg (fun F : QbarPD.FlagPt => F.flag) h3
    rw [show (flagPtOf s).flag = List.ofFn (fun j : Fin (k+1) => cellIdx s j) from rfl,
        show (flagPtOf t).flag = List.ofFn (fun j : Fin (k+1) => cellIdx t j) from rfl] at h5
    exact List.ofFn_inj.mp h5
  ext j
  exact QbarCell.ext (congrFun h4 j)

end

end Work.MbarHomology.Mbar
