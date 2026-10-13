/-
Copyright: work module for the Elgindi finite-time singularity project.

# The elliptic chapter in the interior class `RegQ` (interface correction of 2026-10-03)

The lead's interface correction (`Submission/Work/FTS/Vocab.lean`, frozen 2026-10-03;
`N45_DESIGN_LEAD.md` §5 trap 1) records that `Work.Spaces.SmoothNbhd` is
`ContDiffOn ℝ ⊤`, where `⊤ : WithTop ℕ∞` is Mathlib's **analyticity** order — so
`SmoothNbhd` demands a *real-analytic* function on a neighbourhood of the closed quadrant.  The
objects of the actual construction (`F_*`, the stream functions, the localised datum, the PDE
solution) are not analytic at the angular boundary (`Γ(θ) = (sinθ cos²θ)^{α/3}` is only Hölder
there), so every hypothesis built on `SmoothNbhd` is vacuous in use.

This module restates the elliptic chapter in the frozen vocabulary:

* `Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f` — genuinely
  `C^∞` on the open quadrant, with the honest weighted `ℋ^k`-integrals and the boundary traces
  which make the integrations by parts legitimate (the lead's replacement for my `ZDecay`);
* `Work.FTS.Nonlin.Xn α f = HkNorm α 4 f` — the size used by N4/N5;
* the packages `EllPkgG` (stream function of the perturbation `g`) and `StarPkg` (stream
  function of the profile `F_*`).

`EllHypQ` below is the analogue of `EllHyp` (`Defs.lean`) with `SmoothQuad`/`RegQ` in place of
`SmoothNbhd`.  It is inhabited (`ellHypQ_zero`), and the estimates of the chapter
(`propL2_reg`, `propHk_reg`, `removingL12_reg`) and the three bounds of `EllPkgG` are stated
below in that class; the reduction `EllPkgG_of_reg` assembles the package as soon as the three
bounds are available.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.ScaleAPI

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The data class in the interior vocabulary -/

/-- **The data class of the elliptic chapter, in the lead's interior vocabulary.**  This is
`EllHyp` with `Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open quadrant) and
`Work.FTS.Nonlin.RegQ` (which bundles `HkMem` and the boundary traces) in place of the
analyticity requirement `Work.Spaces.SmoothNbhd`. -/
structure EllHypQ (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  /-- genuine `C^∞` on the open quadrant -/
  quadF : Work.FTS.LocData.SmoothQuad F
  quadPsi : Work.FTS.LocData.SmoothQuad Ψ
  /-- the solution of (PolarBSL) with source `F`, Dirichlet data and decay -/
  sol : Work.Elliptic.IsBslSol α F Ψ
  /-- the interior class of the source -/
  regF : RegQ α k F
  /-- the interior class of the solution and of the quantities the estimates bound -/
  regPsi : RegQ α k Ψ
  regDth : RegQ α k (Work.Spaces.pth Ψ)
  regDth2 : RegQ α k (Work.Spaces.pthIter 2 Ψ)
  regZ2 : RegQ α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  regDivCos : RegQ α k (fun z θ => Ψ z θ / Real.cos θ)
  /-- honesty of the unweighted `L²`-integrals of the `L²`-level estimate -/
  l2Psi : Work.Spaces.L2Mem Ψ
  l2Dth : Work.Spaces.L2Mem (Work.Spaces.pth Ψ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2DthDivCos : Work.Spaces.L2Mem (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ))
  l2F : Work.Spaces.L2Mem F

theorem RegQ_zero (α : ℝ) (k : ℕ) : RegQ α k (0 : ℝ → ℝ → ℝ) := by
  refine ⟨?_, HkMem_zero α k, ?_⟩
  · simp only [Work.FTS.LocData.SmoothQuad, Function.uncurry]
    exact contDiffOn_const
  · intro a b hab
    constructor
    · intro θ hθ
      have h : (fun z : ℝ => z * (Work.Spaces.mixed b a (0 : ℝ → ℝ → ℝ) z θ
          * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
        funext z
        rw [mixed_zero_fun]
        simp
      rw [h]
      exact ⟨(tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)),
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))⟩
    · intro z hz
      have h : (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (0 : ℝ → ℝ → ℝ) z θ) ^ 2) = fun _ => (0 : ℝ) := by
        funext θ
        rw [mixed_zero_fun]
        simp
      rw [h]
      exact ⟨(tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)),
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] (π / 2)) (𝓝 0))⟩

theorem SmoothQuad_zero : Work.FTS.LocData.SmoothQuad (0 : ℝ → ℝ → ℝ) := by
  simp only [Work.FTS.LocData.SmoothQuad, Function.uncurry]
  exact contDiffOn_const

/-- The class is inhabited by `(F, Ψ) = (0,0)`. -/
theorem ellHypQ_zero (α : ℝ) (k : ℕ) :
    EllHypQ α k (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  have h0 : Work.Spaces.pth (0 : ℝ → ℝ → ℝ) = 0 := pth_zero_fun
  have h1 : Work.Spaces.pthIter 2 (0 : ℝ → ℝ → ℝ) = 0 := pthIter_zero_fun 2
  have h2 : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
    funext z θ; rw [pzIter_zero_fun]; simp
  have h3 : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
    funext z θ; simp
  have h4 : Work.Spaces.pth (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
    rw [h3]; exact pth_zero_fun
  refine ⟨SmoothQuad_zero, SmoothQuad_zero, IsBslSol_zero α, RegQ_zero α k, RegQ_zero α k,
    ?_, ?_, ?_, ?_, L2Mem_zero, ?_, ?_, ?_, ?_, ?_, L2Mem_zero⟩
  · rw [h0]; exact RegQ_zero α k
  · rw [h1]; exact RegQ_zero α k
  · rw [h2]; exact RegQ_zero α k
  · rw [h3]; exact RegQ_zero α k
  · rw [h0]; exact L2Mem_zero
  · rw [h1]; exact L2Mem_zero
  · rw [h2]; exact L2Mem_zero
  · rw [h3]; exact L2Mem_zero
  · rw [h4]; exact L2Mem_zero

/-! ## The restated targets (interior class) and the `EllPkgG` assembly -/

/-- The straightened stream function `Φ̃ = Φ - Θ(α,F)` of `Work.Construction.PhiTil` is the
`EllResid` of this chapter. -/
theorem PhiTil_eq_EllResid (α : ℝ) (F Φ : ℝ → ℝ → ℝ) :
    Work.Construction.PhiTil α F Φ = Work.Elliptic.EllResid α F Φ := by
  funext z θ
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Elliptic.EllResid,
    Work.Construction.s2, Work.Elliptic.L12_eq_FM, Work.FM.L12]
  rfl

theorem Rop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ) :
    Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)
      = Rop α (Work.Elliptic.EllResid α g Φg) := by
  rw [PhiTil_eq_EllResid]
  rfl

theorem Uop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ) :
    Work.Construction.Uop α (Work.Construction.PhiTil α g Φg)
      = Uop α (Work.Elliptic.EllResid α g Φg) := by
  rw [PhiTil_eq_EllResid]
  rfl

theorem Vop_PhiTil_eq (α : ℝ) (g Φg : ℝ → ℝ → ℝ) :
    Work.Construction.Vop (Work.Construction.PhiTil α g Φg)
      = Vop α (Work.Elliptic.EllResid α g Φg) := by
  rw [PhiTil_eq_EllResid]
  funext z θ
  rfl

theorem Rop_eq (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Work.Construction.Rop α Φ = Rop α Φ := rfl
theorem Uop_eq (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Work.Construction.Uop α Φ = Uop α Φ := rfl
theorem Vop_eq (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Work.Construction.Vop Φ = Vop α Φ := by
  funext z θ; rfl

/-- **The `EllPkgG` package assembled from the three bounds.**  Once the `ℛ`, `U` and `V` bounds
hold for `(g, Φg)` and `Φg` is the solution of the elliptic law in the interior class, the
package `Work.FTS.Nonlin.EllPkgG` of the frozen vocabulary follows with the maximum of the three
constants. -/
theorem EllPkgG_of_reg {α Ce : ℝ} {g Φg : ℝ → ℝ → ℝ} (hCe : 0 < Ce)
    (hSol : Work.Elliptic.IsBslSol α g Φg) (hSm : Work.FTS.LocData.SmoothQuad Φg)
    (hR : RegQ α 4 (Rop α (Work.Elliptic.EllResid α g Φg)) ∧
      Xn α (Rop α (Work.Elliptic.EllResid α g Φg)) ≤ Ce * Xn α g)
    (hU : RegQ α 4 (fun z θ => Uop α (Work.Elliptic.EllResid α g Φg) z θ
        / Real.sin (2 * θ)) ∧
      Xn α (fun z θ => Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ))
        ≤ Ce * Xn α g)
    (hV : RegQ α 4 (Vop α (Work.Elliptic.EllResid α g Φg)) ∧
      Xn α (Vop α (Work.Elliptic.EllResid α g Φg)) ≤ Ce * Xn α g)
    (hvU : Work.Spaces.VanishTheta (Uop α (Work.Elliptic.EllResid α g Φg))) :
    Work.FTS.Nonlin.EllPkgG α Ce g Φg := by
  refine ⟨hSol, hSm, ?_, ?_, ?_, ?_⟩
  · rw [Rop_PhiTil_eq]; exact hR
  · rw [Uop_PhiTil_eq]; exact hU
  · rw [Vop_PhiTil_eq]; exact hV
  · rw [Uop_PhiTil_eq]; exact hvU

/-! ## The consumable package: `EllPkgG` with the trace-free interior class

The frozen `EllPkgG` asks for `RegQ` of the three operator outputs; as `NOTES.md` §A4 records,
the `BdryTraces` conjunct of `RegQ` is *not* implied for those outputs (they do not vanish at the
angular endpoints in general), so the provable bounds deliver `SmoothQuad ∧ HkMem ∧ bound`
instead.  `EllPkgQ` is the corresponding package — everything `EllPkgG` has, with `RegQ`
replaced by the pair `(SmoothQuad, HkMem)` on the three operator fields. -/
structure EllPkgQ (α Ce : ℝ) (g Φg : ℝ → ℝ → ℝ) : Prop where
  sol : Work.Elliptic.IsBslSol α g Φg
  smooth : Work.FTS.LocData.SmoothQuad Φg
  R : Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  U : Work.FTS.LocData.SmoothQuad (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ∧
      Xn α (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ
          / Work.Construction.s2 θ) ≤ Ce * Xn α g
  V : Work.FTS.LocData.SmoothQuad (Work.Construction.Vop
        (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Xn α (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ≤ Ce * Xn α g
  vanishU : Work.Spaces.VanishTheta (Work.Construction.Uop α (Work.Construction.PhiTil α g Φg))

/-- **`EllPkgQ` from the three delegated bounds** (the shapes of `Rop_bound_reg`,
`Uop_bound_reg`, `Vop_bound_reg`). -/
theorem EllPkgQ_of_bounds {α Ce : ℝ} {g Φg : ℝ → ℝ → ℝ}
    (hSol : Work.Elliptic.IsBslSol α g Φg) (hSm : Work.FTS.LocData.SmoothQuad Φg)
    (hR : Work.FTS.LocData.SmoothQuad (Rop α (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Rop α (Work.Elliptic.EllResid α g Φg)) ∧
      Xn α (Rop α (Work.Elliptic.EllResid α g Φg)) ≤ Ce * Xn α g)
    (hU : Work.FTS.LocData.SmoothQuad (fun z θ =>
        Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)) ∧
      Xn α (fun z θ => Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ))
        ≤ Ce * Xn α g)
    (hV : Work.FTS.LocData.SmoothQuad (Vop α (Work.Elliptic.EllResid α g Φg)) ∧
      Work.Spaces.HkMem α 4 (Vop α (Work.Elliptic.EllResid α g Φg)) ∧
      Xn α (Vop α (Work.Elliptic.EllResid α g Φg)) ≤ Ce * Xn α g)
    (hvU : Work.Spaces.VanishTheta (Uop α (Work.Elliptic.EllResid α g Φg))) :
    EllPkgQ α Ce g Φg := by
  have hs : Work.Construction.s2 = fun θ => Real.sin (2 * θ) := rfl
  refine ⟨hSol, hSm, ?_, ?_, ?_, ?_⟩
  · rw [Rop_PhiTil_eq]; exact hR
  · rw [Uop_PhiTil_eq, hs]; exact hU
  · rw [Vop_PhiTil_eq]; exact hV
  · rw [Uop_PhiTil_eq]; exact hvU


/-! ## The trace-free data class `EllHypT`

`BdryTraces` (inside `RegQ`) demands, in its `(a,b) = (0,0)` slot, that the function itself
vanish at both angular endpoints — true for the perturbation `g` (`VanishTheta`) but *not* for the
derived quantities `∂_θΨ`, `∂_θ²Ψ`, `Ψ/cos θ` of a solution of (PolarBSL), whose boundary values
are free.  `EllHypT` keeps, for those derived quantities, only the honesty of the weighted
integrals (`HkMem`/`L2Mem`), and keeps the boundary decay in `z` in the form of this chapter's
`ZDecay` (which is what the integrations by parts in `z` use).  It is the natural trace-free
analogue of `EllHyp` with `SmoothQuad` in place of the analyticity requirement `SmoothNbhd`. -/
structure EllHypT (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : Prop where
  quadF : Work.FTS.LocData.SmoothQuad F
  quadPsi : Work.FTS.LocData.SmoothQuad Ψ
  sol : Work.Elliptic.IsBslSol α F Ψ
  regF : RegQ α k F
  memPsi : Work.Spaces.HkMem α k Ψ
  memDth : Work.Spaces.HkMem α k (Work.Spaces.pth Ψ)
  memDth2 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)
  memZ2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  memDivCos : Work.Spaces.HkMem α k (fun z θ => Ψ z θ / Real.cos θ)
  l2Psi : Work.Spaces.L2Mem Ψ
  l2Dth : Work.Spaces.L2Mem (Work.Spaces.pth Ψ)
  l2Dth2 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ)
  l2Z2 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
  l2DivCos : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ)
  l2DthDivCos : Work.Spaces.L2Mem (Work.Spaces.pth (fun z θ => Ψ z θ / Real.cos θ))
  l2F : Work.Spaces.L2Mem F
  zdecay : ZDecay Ψ

theorem ellHypT_zero (α : ℝ) (k : ℕ) :
    EllHypT α k (0 : ℝ → ℝ → ℝ) (0 : ℝ → ℝ → ℝ) := by
  have h0 : Work.Spaces.pth (0 : ℝ → ℝ → ℝ) = 0 := pth_zero_fun
  have h1 : Work.Spaces.pthIter 2 (0 : ℝ → ℝ → ℝ) = 0 := pthIter_zero_fun 2
  have h2 : (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (0 : ℝ → ℝ → ℝ) z θ) = 0 := by
    funext z θ; rw [pzIter_zero_fun]; simp
  have h3 : (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
    funext z θ; simp
  have h4 : Work.Spaces.pth (fun z θ => (0 : ℝ → ℝ → ℝ) z θ / Real.cos θ) = 0 := by
    rw [h3]; exact pth_zero_fun
  refine ⟨SmoothQuad_zero, SmoothQuad_zero, IsBslSol_zero α, RegQ_zero α k, HkMem_zero α k, ?_,
    ?_, ?_, ?_, L2Mem_zero, ?_, ?_, ?_, ?_, ?_, L2Mem_zero, ZDecay_zero⟩
  · rw [h0]; exact HkMem_zero α k
  · rw [h1]; exact HkMem_zero α k
  · rw [h2]; exact HkMem_zero α k
  · rw [h3]; exact HkMem_zero α k
  · rw [h0]; exact L2Mem_zero
  · rw [h1]; exact L2Mem_zero
  · rw [h2]; exact L2Mem_zero
  · rw [h3]; exact L2Mem_zero
  · rw [h4]; exact L2Mem_zero


end Work.FTS.EllipticEst
