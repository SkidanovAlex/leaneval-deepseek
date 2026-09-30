/-
# The pieces of the fold charts

For each of the 98 fold classes `i` of `M̄` (codimension `c = foldCodim i`) and each of the `2^c`
sign indices `r`, the blueprint's FOLD area attaches to `M̄`

* a *closed piece* `Clift i r` (the points of the copy `foldCr i r` of `Q̄` whose only tight sides
  are the walls of the representative — the closure of the Voronoi region of the face),
* an *open piece* `Dlift i r` (the same with strict inequalities), and
* the *chart map* `θ i r = coordPerm τ ∘ mobiusKlein (N_F D_r)`, obtained from the normalisation
  `N_F ∈ foldN`, the developing matrix `D_r ∈ foldRepD` and the coordinate permutation `τ` that
  moves the wall coordinates to the front.

This file defines those objects; `FoldChart.lean` assembles the fold charts from them.
-/
import Mathlib
import Submission.Work.FoldInst.Basic
import Submission.Work.FoldInst.Action
import Submission.Work.FoldInst.Cert
import Submission.Work.FoldInst.CertFold
import Submission.Work.FoldInst.Continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Matrix
open scoped Matrix

namespace Work.FoldInst

/-- The coordinate permutation of the model attached to a fold class: it moves the triple
coordinates to the front row by row (and fixes the height). -/
def coordPerm (i : Fin 98) (y : E4) : E4 :=
  !₂[(y : Fin 4 → ℝ) (Function.invFun (foldTau i) 0),
      (y : Fin 4 → ℝ) (Function.invFun (foldTau i) 1),
      (y : Fin 4 → ℝ) (Function.invFun (foldTau i) 2),
      (y : Fin 4 → ℝ) (Function.invFun (foldTau i) 3)]

theorem coordPerm_apply (i : Fin 98) (y : E4) (j : Fin 4) :
    coordPerm i y j = (y : Fin 4 → ℝ) (Function.invFun (foldTau i) j) := by
  fin_cases j <;> rfl

theorem coordPerm_invFun_wall (i : Fin 98) (t : Fin 3) (ht : (t : ℕ) < foldCodim i) :
    Function.invFun (foldTau i) (f3to4 t) = f3to4 (foldWallPos i t) := by
  rw [← foldTau_wall i t ht]
  exact Function.leftInverse_invFun (foldTau_bijective i).1 _

/-- The `±1` sign matrix `R_ε` of a sign vector, as a real matrix. -/
def reflEr (e : Fin 3 → ℤ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (reflE e).map (Int.castRingHom ℝ)

/-- The developing matrix `D_r` over `ℝ`. -/
def foldDrR (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Matrix (Fin 5) (Fin 5) ℝ :=
  (foldDr i r).map (Int.castRingHom ℝ)

/-- The Klein diagonal of a representative, over `ℝ`. -/
def foldKrR (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Matrix (Fin 5) (Fin 5) ℝ :=
  (diagK (foldKr i r)).map (Int.castRingHom ℝ)

/-- **The chart map of the fold class `i` and the sign index `r`** on the Klein model. -/
def foldTheta (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4) : E4 :=
  coordPerm i (HypModel.mobiusKlein (foldNr i * foldDrR i r) y)

/-- The closed piece of the fold chart, inside the copy `foldCr i r` of `Q̄`. -/
def Clift (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Set Xbar :=
  {x | x.1 = foldCr i r ∧ ∀ S : Fin 24, (∀ t : Fin (foldCodim i), foldWalls i r t ≠ S) →
    0 ≤ sideSlack S x.2.1}

/-- The source piece of the fold chart, inside the copy `foldCr i r` of `Q̄`. -/
def Dlift (i : Fin 98) (r : Fin (foldCodim i) → Bool) : Set Xbar :=
  {x | x.1 = foldCr i r ∧ ∀ S : Fin 24, (∀ t : Fin (foldCodim i), foldWalls i r t ≠ S) →
    0 < sideSlack S x.2.1}

theorem Dlift_subset_Clift (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    Dlift i r ⊆ Clift i r :=
  fun x hx => ⟨hx.1, fun S hS => le_of_lt (hx.2 S hS)⟩

theorem isClosed_Clift (i : Fin 98) (r : Fin (foldCodim i) → Bool) : IsClosed (Clift i r) := by
  have h : Clift i r = {x : Xbar | x.1 = foldCr i r} ∩
      ⋂ (S : Fin 24), ⋂ (_ : ∀ t : Fin (foldCodim i), foldWalls i r t ≠ S),
        {x : Xbar | 0 ≤ sideSlack S x.2.1} := by
    ext x
    simp only [Clift, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  refine IsClosed.inter ?_ ?_
  · exact (isClosed_discrete (s := {foldCr i r})).preimage continuous_fst
  · refine isClosed_iInter fun S => isClosed_iInter fun hS => ?_
    exact isClosed_le continuous_const ((continuous_sideSlack S).comp
      ((continuous_subtype_val : Continuous (Subtype.val : Qbar → E4)).comp continuous_snd))

theorem isOpen_Dlift (i : Fin 98) (r : Fin (foldCodim i) → Bool) : IsOpen (Dlift i r) := by
  have h : Dlift i r = {x : Xbar | x.1 = foldCr i r} ∩
      ⋂ (S : Fin 24), ⋂ (_ : ∀ t : Fin (foldCodim i), foldWalls i r t ≠ S),
        {x : Xbar | 0 < sideSlack S x.2.1} := by
    ext x
    simp only [Dlift, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  refine IsOpen.inter ?_ ?_
  · exact (isOpen_discrete (s := {foldCr i r})).preimage continuous_fst
  · refine isOpen_iInter_of_finite fun S => isOpen_iInter_of_finite fun hS => ?_
    exact isOpen_lt continuous_const ((continuous_sideSlack S).comp
      ((continuous_subtype_val : Continuous (Subtype.val : Qbar → E4)).comp continuous_snd))

end Work.FoldInst
