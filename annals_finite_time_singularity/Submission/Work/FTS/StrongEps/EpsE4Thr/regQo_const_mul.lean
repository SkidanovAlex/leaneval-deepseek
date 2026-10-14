import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.Reduction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The class the `hEll` packages control -/

/-- **The membership half of the two elliptic packages.**  `EllPkgCls α Ce F Ψ` records exactly the
*structural* content of `EllPkgGo α Ce F Ψ ∧ EllPkgK α _ Ce F Ψ`:
`Ψ` is `C^∞` on the open quadrant, solves the elliptic law with source `F` (Dirichlet data and
`z`-decay), and the three modulation outputs `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ) / sin 2θ`,
`Vop (PhiTil α F Ψ)` are of class `HQo α 6` — i.e. `C^∞` on the open quadrant *and* of honest
weighted `ℋ⁶`-size, which is exactly the slot shape of `EllPkgGo`/`EllPkgK`.

The *numeric* clauses of the packages (`Xn _ ≤ Ce * Xn _`, `HkNorm _ ≤ Ce * HkNorm _`) are
deliberately absent: they are not closed under taking differences (the constant doubles), while
every consumer of the reduction re-derives its bound from the packages at the *difference* profile. -/
def EllPkgCls (α Ce : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ ∧
    Work.FTS.VocabO.HQo α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ)) ∧
    Work.FTS.VocabO.HQo α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ / Work.Construction.s2 θ) ∧
    Work.FTS.VocabO.HQo α 6 (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ))

/-- **The three slots** through which the packages — and the scheme's right-hand side — see the
stream function.  `SlotR α F Ψ` is the `R`-slot, `SlotU α F Ψ` the `U`-slot *with the `1 / sin 2θ`
already divided in* (the shape in which `EllPkgK` bounds it), and `SlotV α F Ψ` the `V`-slot. -/
def SlotR (α : ℝ) (F Ψ : Fn) : Fn :=
  Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ)

/-- The `U`-slot of the packages. -/
def SlotU (α : ℝ) (F Ψ : Fn) : Fn := fun z θ =>
  Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ / Work.Construction.s2 θ

/-- The `V`-slot of the packages. -/
def SlotV (α : ℝ) (F Ψ : Fn) : Fn :=
  Work.Construction.Vop (Work.Construction.PhiTil α F Ψ)

/-- **The packages give the class.**  For every `u` of the elliptic source class `ClassC`, `hEll`
supplies `EllPkgGo α Ce u (E u)` (the elliptic law `IsBslSol α u (E u)` and the open-quadrant
smoothness) and `EllPkgK α 6 Ce u (E u)` (which carries the three `HQo α 6` slots). -/
theorem EllPkgCls_of_pkg {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u : Fn} (hu : Work.FTS.ClassC.ClassC α u) : EllPkgCls α Ce u (E u) :=
  ⟨(hEll u hu).1.smooth, (hEll u hu).1.sol, (hEll u hu).2.R.1, (hEll u hu).2.U.1,
    (hEll u hu).2.V.1⟩

/-- **`ClassC` is a subspace: it is closed under subtraction.**  (`classC_add` +
`classC_smul` with `c = -1`.)  This is what lets the reduction put the *difference* profile
`u - v` in the class, i.e. apply `hEll` to it. -/
theorem classC_sub {α : ℝ} {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u)
    (hv : Work.FTS.ClassC.ClassC α v) :
    Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ) := by
  have h : (fun z θ => u z θ - v z θ) = u + (-1 : ℝ) • v := by
    funext z θ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul (-1) hv)

/-! ## The reduction -/



/-! ## What the reduction buys: the Lipschitz input of the Picard estimate -/




end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr
end
end
