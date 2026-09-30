import Mathlib
import Submission.Work.Subdivision.Subdiv
import Submission.Work.Subdivision.subdivCell_support
import Submission.Work.Subdivision.D_coneLM
import Submission.Work.Subdivision.D_coneLM_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The subdivision chain map commutes with the differential

For a `PolyCW` `P` satisfying the two hypotheses

* `hdd : P.HasDdZero`  (the cellular incidence numbers satisfy `∂ ∘ ∂ = 0`), and
* `haug : P.HasAugZero` (the incidence coefficients of the two endpoints of every
  `1`-cell sum to zero),

the subdivision chain `PolyCW.subdivCell` is compatible with the differential:

`∂ (subdivCell e) = ∑_{f ⋖ e} inc(e, f) • subdivCell f`

for every cell `e` of dimension `n + 1`.

Rather than prove this pointwise by induction, we prove the *linearised* statement
(`PolyCW.subdivLM_chain` below)

`D k ∘ subdivLM (k+1) = subdivLM k ∘ cellD k`,

i.e. that `subdivLM` is a chain map; the requested statement is the evaluation of
this identity on the basis vector `single e 1`.

The induction is on `k`:

* **base case `k = 0`**: the cone identity in degree zero (`D_coneLM_zero`) gives
  `∂ (cone_e x) = -x + (∑_v x_v) • [e]`; the augmentation hypothesis `haug` kills
  the extra term `(∑_v x_v) • [e]`.
* **step**: the general cone identity `D_coneLM` gives
  `∂ (cone_e x) = cone_e (∂ x) + (-1)^{k+2} • x`, and `∂ x = 0` because `x` is the
  image under `subdivLM` of `∂ e`, and `subdivLM` is a chain map in degree `k` by
  the induction hypothesis, while `∂ ∘ ∂ = 0` by `hdd`.

The support invariant `subdivCell_support` enters (via
`facetsSum_mem_belowSub`) to place the argument of the cone in `belowSub`, which
is the hypothesis of the cone identities.
-/

namespace Work.Subdivision

universe u

namespace PolyCW

variable {P : PolyCW}

/-- The "subdivided boundary" `∑_{f ⋖ e} inc(e, f) • subdivCell f` of a cell `e`
of dimension `n + 1`, written with the named facet index `facetIndex`.  It lies in
`belowSub` because every simplex of `subdivCell f` has vertices `≤ f < e`. -/
theorem facetsSum_mem_belowSub (P : PolyCW) (n : ℕ) (e : P.Cell) (he : P.dim e = n+1) :
    (∑ x ∈ (P.facets e).attach,
        P.inc e x.1 • P.subdivCell n (PolyCW.facetIndex n e he x)) ∈ P.belowSub e n := by
  refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
  refine P.mem_belowSub_of_support fun σ hσ i => ?_
  have hfx : (PolyCW.facetIndex n e he x).1 < e := ((P.mem_facets e x.1).1 x.2).1
  exact lt_of_le_of_lt (subdivCell_support P n (PolyCW.facetIndex n e he x) σ hσ i) hfx

/-- The subdivided boundary of `e` is `subdivLM` applied to the cellular boundary
`∂ e` (`cellDval`), the two sums differing only in the (irrelevant) dimension
proof attached to the facet. -/
theorem facetsSum_eq_subdivLM_cellDval (P : PolyCW) (n : ℕ)
    (e : {e : P.Cell // P.dim e = n+1}) :
    (∑ x ∈ (P.facets e.1).attach,
        P.inc e.1 x.1 • P.subdivCell n (PolyCW.facetIndex n e.1 e.2 x))
      = P.subdivLM n (P.cellDval n e) := by
  rw [PolyCW.cellDval, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, PolyCW.subdivLM_single]
  congr 1

/-- Equation (0): for a `1`-cell `e`, the coefficient sum of the subdivided
boundary of `e` vanishes.  This is where the augmentation hypothesis is used. -/
theorem coeffSum_facetsSum (P : PolyCW) (haug : P.HasAugZero) (e : P.Cell)
    (he : P.dim e = 1) :
    PolyCW.coeffSum (∑ x ∈ (P.facets e).attach,
        P.inc e x.1 • P.subdivCell 0 (PolyCW.facetIndex 0 e (by omega) x)) = 0 := by
  have h1 : PolyCW.coeffSum (∑ x ∈ (P.facets e).attach,
        P.inc e x.1 • P.subdivCell 0 (PolyCW.facetIndex 0 e (by omega) x))
      = ∑ x ∈ (P.facets e).attach, P.inc e x.1 := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, PolyCW.subdivCell_zero, PolyCW.coeffSum_single]
    simp
  rw [h1, Finset.sum_attach]
  exact haug e he

/-- The base case of the induction: `∂ (subdivCell e) = ∂ e` (subdivided) for a
`1`-cell `e`. -/
theorem subdivLM_chain_base (P : PolyCW) (haug : P.HasAugZero)
    (e : {e : P.Cell // P.dim e = 1}) :
    D (α := P.Cell) 0 (P.subdivCell 1 e)
      = P.subdivLM 0 (P.cellD 0 (Finsupp.single e 1)) := by
  set S := ∑ x ∈ (P.facets e.1).attach,
      P.inc e.1 x.1 • P.subdivCell 0 (PolyCW.facetIndex 0 e.1 e.2 x) with hSdef
  have hSmem : S ∈ P.belowSub e.1 0 := facetsSum_mem_belowSub P 0 e.1 e.2
  have hcoeff : PolyCW.coeffSum S = 0 := by
    rw [hSdef]; exact coeffSum_facetsSum P haug e.1 e.2
  rw [P.subdivCell_succ_eq 0 e, map_smul, D_coneLM_zero P e.1 S hSmem, hcoeff,
    zero_smul, add_zero]
  rw [show (-1:ℤ)^(0+1) • -S = S by simp]
  rw [P.cellD_single, hSdef]
  exact facetsSum_eq_subdivLM_cellDval P 0 e

/-- The inductive step: given the chain-map identity in degree `k`, prove it on the
basis vector `single e 1` for a `(k+2)`-cell `e`. -/
theorem subdivLM_chain_step (P : PolyCW) (hdd : P.HasDdZero) (k : ℕ)
    (ih : ∀ z : P.cellMod (k+1),
        D (α := P.Cell) k (P.subdivLM (k+1) z) = P.subdivLM k (P.cellD k z))
    (e : {e : P.Cell // P.dim e = k+2}) :
    D (α := P.Cell) (k+1) (P.subdivLM (k+2) (Finsupp.single e 1))
      = P.subdivLM (k+1) (P.cellD (k+1) (Finsupp.single e 1)) := by
  rw [PolyCW.subdivLM_single]
  set S := ∑ x ∈ (P.facets e.1).attach,
      P.inc e.1 x.1 • P.subdivCell (k+1) (PolyCW.facetIndex (k+1) e.1 e.2 x) with hSdef
  have hSmem : S ∈ P.belowSub e.1 (k+1) := facetsSum_mem_belowSub P (k+1) e.1 e.2
  have hS : S = P.subdivLM (k+1) (P.cellD (k+1) (Finsupp.single e 1)) := by
    rw [P.cellD_single]; exact facetsSum_eq_subdivLM_cellDval P (k+1) e
  have hDkS : D (α := P.Cell) k S = 0 := by
    rw [hS, ih (P.cellD (k+1) (Finsupp.single e 1)),
      show P.cellD k (P.cellD (k+1) (Finsupp.single e 1)) = 0 from
        LinearMap.congr_fun (hdd k) (Finsupp.single e 1)]
    simp
  rw [PolyCW.subdivCell_succ_eq (k+1) e, map_smul, D_coneLM P e.1 k S hSmem, hDkS,
    map_zero, zero_add, ← hS]
  rw [show (-1:ℤ)^(k+2) • ((-1:ℤ)^(k+2) • S) = S by
        rw [smul_smul]
        rcases neg_one_pow_eq_or ℤ (k+2) with h | h <;> rw [h] <;> simp]

/-- A linear identity is determined by its values on the basis vectors
`Finsupp.single e 1`. -/
theorem linear_of_single (P : PolyCW) (k : ℕ)
    (h : ∀ e : {e : P.Cell // P.dim e = k+1},
      D (α := P.Cell) k (P.subdivLM (k+1) (Finsupp.single e 1))
        = P.subdivLM k (P.cellD k (Finsupp.single e 1))) :
    ∀ z : P.cellMod (k+1),
      D (α := P.Cell) k (P.subdivLM (k+1) z) = P.subdivLM k (P.cellD k z) := by
  intro z
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add]
      rw [hf, hg, ← map_add]
  | single e b =>
      rw [show Finsupp.single e b = b • Finsupp.single e 1 by rw [Finsupp.smul_single]; simp]
      simp only [map_smul]
      rw [h e]

/-- **`subdivLM` is a chain map**: `D k ∘ subdivLM (k+1) = subdivLM k ∘ cellD k`. -/
theorem subdivLM_chain (P : PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) :
    ∀ k : ℕ, ∀ z : P.cellMod (k+1),
      D (α := P.Cell) k (P.subdivLM (k+1) z) = P.subdivLM k (P.cellD k z) := by
  intro k
  induction k with
  | zero =>
      apply linear_of_single P 0
      intro e
      rw [PolyCW.subdivLM_single]
      exact subdivLM_chain_base P haug e
  | succ k ih =>
      exact linear_of_single P (k+1) (fun e => subdivLM_chain_step P hdd k ih e)

end PolyCW

open PolyCW

/-- **The subdivision of a cell is compatible with the differential**: for a cell
`e` of dimension `n + 1`, `∂ (subdivCell e) = ∑_{f ⋖ e} inc(e, f) • subdivCell f`. -/
theorem D_subdivCell (P : PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (n : ℕ) (e : {e : P.Cell // P.dim e = n + 1}) :
    D (α := P.Cell) n (PolyCW.subdivCell P (n + 1) e)
      = ∑ x ∈ (P.facets e.1).attach, P.inc e.1 x.1 • PolyCW.subdivCell P n ⟨x.1, by
          have h := (P.mem_facets e.1 x.1).1 x.2
          have he := e.2
          omega⟩ := by
  have h := P.subdivLM_chain hdd haug n (Finsupp.single e 1)
  rw [PolyCW.subdivLM_single, PolyCW.cellD_single] at h
  rw [h]
  rw [PolyCW.cellDval, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, PolyCW.subdivLM_single]

end Work.Subdivision
