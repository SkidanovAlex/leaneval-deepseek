import Mathlib
import Submission.Work.Subdivision.Subdiv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cone identity in degree zero

For a `PolyCW` `P`, a cell `e`, and a `0`-chain `x` supported on vertices all of
which are `< e` (i.e. `x ∈ PolyCW.belowSub P e 0`), coning `x` with apex `e`
(append `e` to every vertex, so every vertex becomes the edge from that vertex to
`e`) and taking the boundary gives

`∂(cone_e x) = -x + (∑_v x_v) • [e]`,

i.e. every edge `[v, e]` contributes `[e] - [v]`.  This is the degree-zero base
case of the general cone recursion `D_coneLM` for the subdivision chain map.

The computation uses only that the two faces of the cone on a vertex are the
apex `e` (delete the vertex) and the vertex `σ` again (delete the apex).
-/

namespace Work.Subdivision

theorem D_coneLM_zero (P : PolyCW) (e : P.Cell) (x : chainMod P.Cell 0)
    (hx : x ∈ PolyCW.belowSub P e 0) :
    D (α := P.Cell) 0 (PolyCW.coneLM P e 0 x)
      = -x + PolyCW.coeffSum x • Finsupp.single (Simplex.vertex e) 1 := by
  -- `belowSub` is spanned by the single vertices `σ` with all vertices `< e`,
  -- and both sides are `ℤ`-linear in `x`.
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨σ, hσ, rfl⟩ := hx
      -- The `0`-th face of the cone on `σ` is the apex `e` ...
      have h0 : Simplex.face (0 : Fin (0 + 2)) (Simplex.snoc σ e hσ) = Simplex.vertex e := by
        ext i
        fin_cases i
        exact Simplex.snocFun_last σ.toFun e
      -- ... and its `1`-st (last) face is `σ` itself.
      have h1 : Simplex.face (1 : Fin (0 + 2)) (Simplex.snoc σ e hσ) = σ := by
        ext i
        fin_cases i
        exact Simplex.snocFun_castSucc σ.toFun e 0
      rw [PolyCW.coneLM_single P e 0 σ hσ, D_single, Fin.sum_univ_two, h0, h1]
      simp
      abel
  | zero =>
      simp only [map_zero, neg_zero, zero_smul, add_zero]
  | add x y hx hy ihx ihy =>
      rw [map_add, map_add, ihx, ihy, map_add]
      simp only [add_smul]
      abel
  | smul a x hx ih =>
      rw [map_smul, map_smul, ih, map_smul]
      simp only [smul_add, smul_neg, smul_smul]
      abel

end Work.Subdivision
