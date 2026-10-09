import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.dimensionSubgroup_free
import Submission.Work.SSGRoute.prop5.magnus_filtration_correspondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus map detects the lower central series (`magnus_detects_gamma`)

`magnus X N` is the Magnus map `FreeGroup X →* (FreeAssoc X ⧸ fil X N)ˣ`, `x ↦ 1 + X_x`.

The classical Magnus/Witt theorem says that, for `y` in the `(j-1)`-th term of the lower central
series, the image `magnus X (j+1) y` is trivial exactly when `y` lies in the `j`-th term:

`y ∈ γ_j  ∧  magnus X (j+1) y = 1  →  y ∈ γ_{j+1}`.

The proof combines two independent inputs.

* `magnus_filtration_correspondence` identifies the word-length filtration `fil` of the free
  associative algebra (as seen through the Magnus map) with the `Δ`-adic filtration of the integral
  group ring `ℤ[FreeGroup X]` (`Δ` the augmentation ideal): if `magnus X N y = 1` then
  `single y 1 - 1 ∈ Δ^N`.
* `dimensionSubgroup_free` is Magnus's dimension-subgroup theorem for free groups over `ℤ`: the
  `N`-th dimension subgroup `FreeGroup X ∩ (1 + Δ^N)` equals `γ_N`.
-/

namespace Work.SSGRoute.prop5

noncomputable section

/-- **The Magnus map detects `γ_j`.**  If `y ∈ γ_j` and the Magnus image of `y` modulo `fil (j+1)`
is trivial, then `y ∈ γ_{j+1}`. -/
theorem magnus_detects_gamma (X : Type) (j : ℕ) (hj : 1 ≤ j) (y : FreeGroup X)
    (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (h : ((magnus X (j + 1) y : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
        FreeAssoc X ⧸ fil X (j + 1)) - 1 = 0) :
    y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  -- The Magnus image of `y` is trivial, so `y - 1` lies in the `(j+1)`-st power of the
  -- augmentation ideal of `ℤ[FreeGroup X]`.
  have hΔ : MonoidAlgebra.single y (1 : ℤ) - 1 ∈
      (Ideal.span (Set.range (fun g' : FreeGroup X =>
        MonoidAlgebra.single g' (1 : ℤ) - 1))) ^ (j + 1) :=
    magnus_filtration_correspondence X (j + 1) y h
  -- Magnus's dimension-subgroup theorem for free groups then places `y` in `γ_{j+1}`.
  simpa using dimensionSubgroup_free X (j + 1) y hΔ

end

end Work.SSGRoute.prop5
