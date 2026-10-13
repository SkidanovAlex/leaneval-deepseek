/-
# `Work.FTS_RegExport.RXT.jc3` — joint continuity of the order-≤3 jets (RX-St1 leaf S3)

For a family `g` with `DynOK' (pExp α) C₀ Φs E g`, the mixed slots
`D_z^j D_θ^i (slice g τ)` of total order `≤ 3` are jointly continuous on the slab
`z > 0`, `θ ∈ (0,π/2)`, `τ ∈ [0,T]`.

The proof assembles three pieces:

* `RXT.slice_space_lip` — the slots of order `≤ 3` are Lipschitz in `(z,θ)`, uniformly in
  `τ ∈ [0,T]` (from the local `C⁴`-bound `RXT.loc_sup4` and the mean value theorem);
* `RXT.lim_mixed_lip` — the slots of order `≤ 2` are Lipschitz in `τ` (from the class-C
  approximants of `LimApprox` and the interior `L^∞`–`ℋ⁴` trade-off);
* `RXT.tau_lip_sqrt_of_primitive_self` (in `RXT.jc3_landau`) — the abstract Landau step: if `V`
  is Lipschitz in the time variable and `∂_x V = W` with `W` Lipschitz in `x`, then `W` is
  `1/2`-Hölder in time.

The order-3 slots are not Lipschitz in `τ`, but they are the spatial derivatives of the
order-2 slots, and that is where the Landau step enters: along the curve `x ↦ z e^x`
(on which the spatial derivative is `D_z`) resp. `x ↦ arctan (tan θ · e^{2x})` (on which it is
`D_θ`), the order-3 slot becomes the `x`-derivative of the order-2 slot, so a time increment
is paid for by a space increment.

The three pieces are combined in `RXT.jc3_of_pieces` (through the time-continuity lemma
`RXT.tau_cont_mixed` of `RXT.jc3_tau`), and `jc3` is that combination with the pieces
supplied.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.jc3_asm
import Submission.Work.FTS_RegExport.RXT.loc_sup4
import Submission.Work.FTS_RegExport.RXT.slice_space_lip
import Submission.Work.FTS_RegExport.RXT.lim_mixed_lip
import Submission.Work.FTS_RegExport.RXT.jc3_landau

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem jc3 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) :
    ∀ j i : ℕ, j + i ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g p.2.2) p.1 p.2.1)
        (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) T) :=
  jc3_of_pieces hOK T hT
    (fun {a b c d} ha hab hc hcd hd => slice_space_lip hα hα13 hOK T hT ha hab hc hcd hd)
    (lim_mixed_lip (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13)
      hOK.2 T hT)
    (fun {V W} {x₀ δc L K} hδc hL hK hV hcont hW hderiv =>
      tau_lip_sqrt_of_primitive_self hδc hL hK hV hcont hW hderiv)

end Work.FTS_RegExport.RXT
