import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.mem_skelSet_iff
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial

/-- A point lies in the open `k`-cell `intCell k σ` of a realized `Δ`-complex if and only if it
is the image of an *interior* point of the standard `k`-simplex under the characteristic map.
-/
theorem mem_intCell_iff {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k : ℕ) (σ : Fin (K.card k)) (x : X) :
    x ∈ R.toDeltaSimplexMap.intCell k σ ↔
      ∃ y : StdSimplex ℝ (Fin (k + 1)),
        (∀ i, 0 < y.weights i) ∧ R.toDeltaSimplexMap.cls k σ y = x := by
  constructor
  · intro hx
    rw [DeltaSimplexMap.mem_intCell_iff] at hx
    obtain ⟨y₀, hy₀⟩ := hx.1
    obtain ⟨p, hp⟩ := (R.bij x).exists
    -- The open simplex of `x` has dimension at most `k`, since `x` is the image of a
    -- `k`-simplex.
    have hle : p.dim ≤ k := R.dim_le_aux p k σ y₀ (hy₀.trans hp.symm)
    -- ... and at least `k`, since `x` is in no lower skeleton.
    have hge : k ≤ p.dim := by
      by_contra h
      have hlt : p.dim < k := Nat.lt_of_not_le h
      exact hx.2 p.dim hlt (hp ▸ R.toDeltaSimplexMap.real_mem_skelSet p)
    have hdim : p.dim = k := le_antisymm hle hge
    -- Hence `y₀` is an interior point of the standard `k`-simplex.
    exact ⟨y₀, R.interior_of_cls_eq_real p hdim σ y₀ (hy₀.trans hp.symm), hy₀⟩
  · rintro ⟨y, hy, hcls⟩
    rw [DeltaSimplexMap.mem_intCell_iff]
    refine ⟨hcls ▸ Set.mem_range_self y, ?_⟩
    intro j hj hxskel
    obtain ⟨p, hp, hpd⟩ := (mem_skelSet_iff R j x).mp hxskel
    have hreal : R.toDeltaSimplexMap.real (⟨k, σ, y, hy⟩ : OpenSimplex K) = x := hcls
    have heq : p = ⟨k, σ, y, hy⟩ := (R.bij x).unique hp hreal
    have : p.dim = k := by rw [heq]
    omega

end Work.DeltaHomology
