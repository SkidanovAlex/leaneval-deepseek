import Mathlib
import Submission.Work.Stems.Hurewicz
import Submission.Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped Topology

/-!
# A based cube that is *freely* null-homotopic is trivial in the homotopy group

This is Lemma 2.2(a) of Hutchings' notes (an elementary route to the Hurewicz result): if a based
`k`-cube, viewed as a map of the sphere `S^k` through the descent `Work.Stems.cubeLift`, is
homotopic to the constant map *without* the base-point condition, then its class in `π_k(X,x₀)` is
trivial.  The classical proof modifies the free homotopy using the trajectory of the base point
(in degree `1` it uses that a based loop that is freely null-homotopic has trivial class, its free
class being a conjugacy class).

The descent to the sphere is essential: free homotopy of *cube* maps is vacuous, `I^k` being
contractible.  The result is used in proofs of the Hurewicz map's injectivity: the boundary sphere
map of a cube extends over a ball, hence is freely null, and therefore contributes nothing.

## Proof

The free homotopy is a map `H : I × S^k → X` with `H (0, ·) = cubeLift p` and `H (1, ·) = x₀`.
Pulling it back along the quotient map `Work.Stems.collapseMap : I^k → S^k` gives a homotopy
`Hc : I^k × I → X` from `p` (by `Work.Stems.cubeLift_comp`) to the constant `x₀` which is constant
on the boundary slice `∂I^k × {t}` for every `t` (by `Work.Stems.collapseMap_boundary`).  That is
exactly the hypothesis of `Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased`, whose proof
descends `Hc` further to the cone `D^{k+1}` (the boundary condition is what makes the descent
exist: `collapseMap` identifies all boundary points, so `∂I^k × {t}` is contained in a fibre) and
then straightens the base point out along the trajectory, producing a homotopy relative to `∂I^k`
from `p` to the constant loop.  The class in `π_k` is then trivial by `Quotient.sound`.
-/

theorem genLoop_eq_one_of_free_homotopic_const (k : ℕ) {X : Type} [TopologicalSpace X]
    (x₀ : X) (p : GenLoop (Fin (k + 1)) X x₀)
    (h : (Work.Stems.cubeLift (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) p).Homotopic
          (ContinuousMap.const (Work.Stems.sphere (k + 1)) x₀)) :
    (show HomotopyGroup (Fin (k + 1)) X x₀ from Quotient.mk _ p) = 1 := by
  have hn : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  obtain ⟨H⟩ := h
  -- The free homotopy, pulled back to the cube.
  let Hc : C(Work.Stems.CubeI (k + 1) × unitInterval, X) :=
    ⟨fun z => H ((z.2 : unitInterval), (Work.Stems.collapseMap (k + 1) hn) z.1), by fun_prop⟩
  have hc_val : ∀ (y : Work.Stems.CubeI (k + 1)) (t : unitInterval),
      Hc (y, t) = H (t, (Work.Stems.collapseMap (k + 1) hn) y) := fun _ _ => rfl
  -- It starts at `p` ...
  have h0 : ∀ y : Work.Stems.CubeI (k + 1), Hc (y, 0) = p.1 y := by
    intro y
    have hz : H (0, (Work.Stems.collapseMap (k + 1) hn) y)
        = (Work.Stems.cubeLift (k + 1) hn p) ((Work.Stems.collapseMap (k + 1) hn) y) :=
      H.map_zero_left _
    rw [hc_val, hz]
    exact congrFun (congrArg (fun f : C(Work.Stems.CubeI (k + 1), X) => ⇑f)
      (Work.Stems.cubeLift_comp (k + 1) hn p)) y
  -- ... ends at the constant map ...
  have h1 : ∀ y : Work.Stems.CubeI (k + 1), Hc (y, 1) = x₀ := by
    intro y
    have hz : H (1, (Work.Stems.collapseMap (k + 1) hn) y) = x₀ := H.map_one_left _
    rw [hc_val, hz]
  -- ... and is constant on the boundary slice at every time.
  have hb : ∀ (y y' : Work.Stems.CubeI (k + 1)) (t : unitInterval),
      y ∈ Cube.boundary (Fin (k + 1)) → y' ∈ Cube.boundary (Fin (k + 1)) →
      Hc (y, t) = Hc (y', t) := by
    intro y y' t hy hy'
    rw [hc_val, hc_val, Work.Stems.collapseMap_boundary (k + 1) hn hy,
      Work.Stems.collapseMap_boundary (k + 1) hn hy']
  -- Hence `p` is null-homotopic as a based cube.
  have hfree : GenLoop.Homotopic p GenLoop.const :=
    Work.Stems.Hur2b.genLoop_homotopic_const_of_unbased (k + 1) p Hc h0 h1 hb
  rw [HomotopyGroup.one_def]
  exact Quotient.sound hfree

end Work.RatHurewicz
