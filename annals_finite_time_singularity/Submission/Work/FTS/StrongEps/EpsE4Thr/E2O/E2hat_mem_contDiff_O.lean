/-
Copyright: work module for the Elgindi finite-time singularity project.

# The defect `Ê₂` preserves the open class: `ℋⁿ`-membership and `Cⁿ`-regularity

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)² = 2·φ·f + 3·φ·D_θf` with the
`z`-only multiplier `φ(z) = z/(1+z)²`, which is `C^∞` on `(-1,∞)` and whose `Zop`-iterates
(`Zop = z∂_z`) are uniformly bounded on `(0,∞)`.

Both claims of the target are therefore instances of the multiplier calculus for
`SmoothOpen` data:

* `ℋⁿ`-membership: `StrongPersist.L3Aux.HkIntegrand_zmul_le` gives
  `HkMem α n g → HkMem α n (φ·g)` for a `z`-only multiplier of class `C^∞` on `(-1,∞)`
  (applied to `g = f` and `g = D_θ f`, using the two hypotheses `hmem`, `hmemd`), and
  `EllipticEst.HkMem_add_open` + `LocData.HkMem_const_mul` assemble
  `Ê₂ f = 2·(φ·f) + 3·(φ·D_θf)`;
* `Cⁿ`-regularity: `E2hatOAux.smoothOpen_mul` / `smoothOpen_const_mul` / `smoothOpen_zOnly`
  give `SmoothOpen (Ê₂ f)`, i.e. `C^∞` on the open quadrant, which restricts to the required
  `Cⁿ` (`smoothOpen_iff_forall`).

The hypotheses are exactly the honest ones the route carries (`SmoothOpen f`,
`HkMem α n f`, `HkMem α n (D_θ f)`) — no boundary trace and no `ℋ^{n+1}` datum is used.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2hatOAux.PtBound
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

theorem E2hat_mem_contDiff_O (α : ℝ) (hα : 0 < α) {n : ℕ} (hn : n ≤ 4) {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α n f)
    (hmemd : Work.Spaces.HkMem α n (Work.Spaces.Dth f)) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.E2hat f) ∧
      ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.E2hat f))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  -- the angular derivative is again `C^∞` on the open quadrant
  have hDthO : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth f) := hO.Dth
  -- the `z`-only multiplier `φ(z) = z/(1+z)²`: smooth on `(-1,∞)`, `Zop`-iterates bounded
  obtain ⟨K, hK0, hKb⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le n
  have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
    Work.FTS.CoercivityFix.E2Bound.contDiffOn_zDiv
  -- `ℋⁿ`-membership of the two products `φ·f` and `φ·D_θf`
  have hmul_f : Work.Spaces.HkMem α n (fun z θ => (z / (1 + z) ^ 2) * f z θ) :=
    ((hC α (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hφsm f hO).2 hmem).1
  have hmul_d : Work.Spaces.HkMem α n
      (fun z θ => (z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    ((hC α (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb hφsm
      (Work.Spaces.Dth f) hDthO).2 hmemd).1
  -- smoothness of the two summands
  have hφSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) :=
    E2hatOAux.smoothOpen_zOnly E2hatOAux.phiZ_contDiffOn
  have hA_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
    E2hatOAux.smoothOpen_const_mul 2 (E2hatOAux.smoothOpen_mul hφSO hO)
  have hB_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ)) :=
    E2hatOAux.smoothOpen_const_mul 3 (E2hatOAux.smoothOpen_mul hφSO hDthO)
  -- the explicit `z`-multiplier form of the defect
  have hE2 : Work.FTS.CoercivityFix.E2hat f
      = fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) :=
    Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f
  constructor
  · rw [hE2]
    exact Work.FTS.EllipticEst.HkMem_add_open hA_sm hB_sm
      (Work.FTS.LocData.HkMem_const_mul α n 2 hmul_f)
      (Work.FTS.LocData.HkMem_const_mul α n 3 hmul_d)
  · have hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.CoercivityFix.E2hat f) := by
      rw [hE2]
      exact Work.FTS.EllipticEst.smoothOpen_add hA_sm hB_sm
    have h := (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (Work.FTS.CoercivityFix.E2hat f)).mp hsm n
    simpa only [Work.FTS.EllipticEst.Q0] using h

end Work.FTS.StrongEps.EpsE4Thr.E2O
