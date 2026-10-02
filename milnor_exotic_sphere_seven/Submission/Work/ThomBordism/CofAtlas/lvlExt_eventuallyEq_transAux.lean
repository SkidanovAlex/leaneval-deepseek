import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

/-- For `q` in the chart sources of `x` and `y`, with `D.lvlExt x q` in the *interior* of the
half-space (`0 < (D.lvlExt x q) 0` — automatic when `x` is not a boundary point of `M`), the
transition of the extended `Lvl` charts agrees with `D.S.transAux x y` near `D.lvlExt x q`.

Route: `Work.PTGeometric.Lvl.Setup.transAux_eq_chartAt_trans` holds on the neighbourhood
`{u | u ∈ range (𝓡∂ 9) ∧ (𝓡∂ 9).symm u ∈ D.S.chartTarget x ∧ D.S.chartInvFun x ((𝓡∂ 9).symm u) ∈ D.S.chartSource y}`
of `D.lvlExt x q` (all three conditions are open and hold at `D.lvlExt x q`, which equals
`(𝓡∂ 9) (D.S.chartAt x q)`), and on that neighbourhood both
`fun u => D.lvlExt y ((D.lvlExt x).symm u)` and `D.S.transAux x y` equal
`(𝓡∂ 9) (D.S.chartAt y (D.S.chartInvFun x ((𝓡∂ 9).symm u)))`. -/
theorem lvlExt_eventuallyEq_transAux
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x y : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x) (hy : q ∈ D.S.chartSource y)
    (hpos : 0 < (D.lvlExt x q) 0) :
    Filter.EventuallyEq (nhds (D.lvlExt x q))
      (fun u : EuclideanSpace ℝ (Fin 9) => D.lvlExt y ((D.lvlExt x).symm u))
      (D.S.transAux x y) := by
  -- `D.lvlExt x` is the `𝓡∂ 9`-extended chart, and `D.lvlExt x q = (𝓡∂ 9) (D.S.chartAt x q)`.
  have hu₀ : D.lvlExt x q = (𝓡∂ 9) ((D.S.chartAt x) q) := rfl
  have hxT : (D.S.chartAt x) q ∈ D.S.chartTarget x := (D.S.chartAt x).map_source hx
  have hsymm : (𝓡∂ 9).symm (D.lvlExt x q) = (D.S.chartAt x) q := by
    rw [hu₀]
    exact ModelWithCorners.left_inv (𝓡∂ 9) ((D.S.chartAt x) q)
  -- The three conditions of the row where `transAux` is the chart transition are open near
  -- `D.lvlExt x q`.
  have hN1 : Set.range (𝓡∂ 9) ∈ 𝓝 (D.lvlExt x q) := by
    have hint : D.lvlExt x q ∈ interior (Set.range (𝓡∂ 9)) := by
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      exact hpos
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset
  have hN2 : {u : EuclideanSpace ℝ (Fin 9) | (𝓡∂ 9).symm u ∈ D.S.chartTarget x}
      ∈ 𝓝 (D.lvlExt x q) := by
    have hmem : (𝓡∂ 9).symm (D.lvlExt x q) ∈ D.S.chartTarget x := by
      rw [hsymm]; exact hxT
    exact ((D.S.chartTarget_open x).preimage (𝓡∂ 9).continuous_symm).mem_nhds hmem
  have hleft : (D.S.chartAt x).symm ((D.S.chartAt x) q) = q := (D.S.chartAt x).left_inv hx
  have hN3 : {u : EuclideanSpace ℝ (Fin 9) | D.S.chartInvFun x ((𝓡∂ 9).symm u)
      ∈ D.S.chartSource y} ∈ 𝓝 (D.lvlExt x q) := by
    have htgt : (𝓡∂ 9).symm (D.lvlExt x q) ∈ (D.S.chartAt x).target := by
      rw [hsymm]; exact hxT
    have hcts : ContinuousAt (fun u : EuclideanSpace ℝ (Fin 9) =>
        (D.S.chartAt x).symm ((𝓡∂ 9).symm u)) (D.lvlExt x q) :=
      ((D.S.chartAt x).continuousAt_symm htgt).comp (𝓡∂ 9).continuous_symm.continuousAt
    have hmem : (D.S.chartAt x).symm ((𝓡∂ 9).symm (D.lvlExt x q)) ∈ D.S.chartSource y := by
      rw [hsymm, hleft]; exact hy
    exact hcts.preimage_mem_nhds ((D.S.chartSource_open y).mem_nhds hmem)
  -- On that neighbourhood both sides are `(𝓡∂ 9) (D.S.chartAt y (D.S.chartInvFun x ((𝓡∂ 9).symm u)))`.
  have key : ∀ᶠ u in nhds (D.lvlExt x q),
      D.lvlExt y ((D.lvlExt x).symm u) = D.S.transAux x y u := by
    filter_upwards [hN1, hN2, hN3] with u hu1 hu2 hu3
    rw [D.S.transAux_eq_chartAt_trans x y hu1 hu2 hu3]
    rfl
  exact key

end Work.ThomBordism.CofAtlas
