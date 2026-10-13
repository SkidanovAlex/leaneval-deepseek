/-
# `Npair6BWork/nsumData` — the `C⁶`/`ℋ⁶` data of the level-six `N`-row sum

The level-six `N`-row of the pairing (`H6Rows/Npair6_sup`) pairs the sum of the twenty pieces
`nsP0 … nsP19` of `H6Rows/Npair6SupAux.NDefs` against the datum `f = slice g τ`.  Before any
estimate can be made, that sum `nsum α f (E f) Φs` must be

* `C⁶` on the open quadrant `Q0` (so that the pairing's slots exist), and
* honest in `ℋ⁶` (so that it can be paired).

Both are read off from the already proved per-piece analysis of the sibling area
`H6Row6/NS6/Pieces.lean`: the twenty pieces `pcs α f (E f) Φs k` sum to `nsum` (`pcs_sum`),
each is `C⁶` and `ℋ⁶` (`NS6.pieces`), and the `ℋ⁶`-closure of a finite sum of such pieces is
`NS6.hkMem_sum_range`.

The only datum of `NS6.Data` not literally a field of `L6Ctx` is the `ℋ⁶ × ℋ⁶` product rule
`mulSm` (the tree's `N6.prod_field6` is stated with an existentially quantified `α₂`; the
underlying `N6.prod_field_of6` is `α`-free on `(0,1]`, and it is *that* statement which is
instantiated here) and the `ℋ⁶`-membership of the angular moment `FK f`, which is the
`α`-free `Npair6BWork.fk_hkMem`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Row6.NS6.Pieces
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem
import Submission.Work.FTS.StrongPersist.N6.Prod6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **The level-six product rule of Elgindi, in the `α`-free form on `(0,1]`.**

The tree's `N6.prod_field6` states the `ℋ⁶`-product rule with an existentially quantified
`α₂`; its proof (and the underlying `N6.prod_field_of6`) is valid for every `α ∈ (0,1]`, which
is the form below.  (`N6.prod_field_of6` is instantiated with the two analytic inputs
`N6.prod_majorant6` and `N6.exc_bound6`.) -/
theorem hkMem_mul_of6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u v : Fn}
    (hu : Work.FTS.VocabO.HQo α 6 u) (hv : Work.FTS.VocabO.HQo α 6 v) :
    Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) := by
  obtain ⟨K, hK, hMaj⟩ := Work.FTS.StrongPersist.N6.prod_majorant6
  obtain ⟨Ce, hCe, hExc⟩ := Work.FTS.StrongPersist.N6.exc_bound6
  obtain ⟨C, hC, hfield⟩ :=
    Work.FTS.StrongPersist.N6.prod_field_of6 ⟨K, hK, hMaj⟩ ⟨Ce, hCe, hExc⟩
  exact (hfield α hα hα1 u v hu hv).1

theorem nsumData (Ce : ℝ) : ∀ α ∈ Set.Ioc 0 1,
    ∀ (g Φ : Work.FTS.Galerkin.Fam) (τ M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (Φs : Work.FTS.Galerkin.Fn),
      0 ≤ τ →
      Work.FTS.StrongPersist.L6Ctx (Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1)
        α M Ce Cs E Φs g Φ τ →
      Work.Spaces.HkMem α 6 (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs) ∧
      ContDiffOn ℝ 6 (Function.uncurry (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α
          (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)) Φs))
        Work.FTS.EllipticEst.Q0 := by
  intro α hαIoc g Φ τ M Cs E Φs hτ hctx
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the slice and the perturbation stream function
  set f : Fn := Work.FTS.Galerkin.slice g τ with hf
  set Ef : Fn := E f with hEf
  have hreg : Work.FTS.StrongPersist.H6Adm α f := hctx.hreg
  have hell : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f (Work.FTS.Galerkin.slice Φ τ) :=
    hctx.hell
  have hstar6 : Work.FTS.StrongPersist.StarPkg6 α Cs Φs := hctx.hstar6
  -- the angular moment `FK f` is honest in `ℋ⁶` (the `α`-free membership)
  have hkfm : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    fk_hkMem α hαIoc f hreg.reg.1 hreg.reg.2
  -- the `ℋ⁶ × ℋ⁶` product rule of the open-quadrant class, for this `α`
  have hmulSm : ∀ (u v : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.Spaces.HkMem α 6 u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 6 v →
      Work.Spaces.HkMem α 6 (fun z θ => u z θ * v z θ) :=
    fun u v hus hum hvs hvm => hkMem_mul_of6 hα0 hα1 ⟨hus, hum⟩ ⟨hvs, hvm⟩
  -- the bundled slice data
  have D : Work.FTS.StrongPersist.H6Row6.NS6.Data α Ce Cs f Ef Φs :=
    { hα := hα0
      hα1 := hα1
      fsm := hreg.reg.1
      fm := hreg.reg.2
      f7 := hctx.h7
      Efsm := hell.hell.smooth
      Φssm := hell.hstar.smooth
      l12 := hreg.l12
      star := hstar6
      ell := hell.hell
      kfm := hkfm
      hadm := hreg
      mulSm := hmulSm }
  -- the twenty pieces, and their finite sum
  have hpcs := Work.FTS.StrongPersist.H6Row6.NS6.pieces D
  have hsum := Work.FTS.StrongPersist.H6Row6.NS6.hkMem_sum_range 20
    (Work.FTS.StrongPersist.H6Row6.pcs α f Ef Φs)
    (fun k hk => (hpcs k hk).1) (fun k hk => (hpcs k hk).2)
  refine ⟨?_, ?_⟩
  · rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.2
  · rw [Work.FTS.StrongPersist.H6Row6.pcs_sum]
    exact hsum.1

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
