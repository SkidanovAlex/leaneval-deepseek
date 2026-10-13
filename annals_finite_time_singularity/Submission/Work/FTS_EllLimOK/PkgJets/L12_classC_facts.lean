import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS_EllLimOK.PkgJets.ThetaBoundBasic
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FM.Core2
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

/-!
# The four analytic facts about `L₁₂` on the linear elliptic class `ClassC`

`L₁₂(g)(z) = ∫_z^∞ ∫_θ K(θ) g(s,θ)/s dθ ds` is the radial `L₁₂`-transform of the
fundamental model, and `L12dens g s = ∫_θ K(θ) g(s,θ)/s dθ` is its angular density.  For a
datum `g` of the linear elliptic class `Work.FTS.ClassC.ClassC α` the present lemma collects
the four analytic facts every consumer of the `PkgJets` chapter needs:

* `L12dens g ∈ L¹((0,∞))`,
* `∂_z L₁₂(g)(z) = -L12dens g z` for every `z > 0`,
* `L₁₂(g)` is continuous on `[0,1]`,
* `L₁₂(g)(z) → 0` as `z → ∞`.

The proof is an assembly of three facts already in the tree:

1. `ClassC` supplies *continuity* of the datum on the open quadrant `Q0` (`hg.reg`, open-quadrant
   `C^∞`) and `ℋ⁴`-honesty (`hg.mem`, `ℋ⁷`, restricted by the pointwise monotonicity
   `HkMem_mono_le` of the `ℋ`-integrand).  Those are exactly the two hypotheses of
   `L12dens_integrableOn_of_continuousOn`, which gives the first conjunct.  No smoothness
   (let alone analyticity) of `g` is used here — only continuity on `Q0`.
2. The derivative conjunct is `HasDerivAt_L12_of_Fstar_facts`, applied to the all-order
   smoothness of the angular moment `F_*(g)` on `(0,∞)` (`hg.fsm`, one of the new fields of
   `ClassC`, and the reason `ClassC` was introduced: the old `GalClass` lacked it).  Its second
   hypothesis, the integrability of `r ↦ F_*(g)(r)/r`, is *not* independent: `L12dens` is
   `3·F_*/·` (`L12dens_eq_three_Fstar_div`), so it is a consequence of the first conjunct.
3. The value `L₁₂(g)(0) = 0`, together with the first conjunct, is all that
   `Work.Elliptic.L12_values` needs to produce the last two conjuncts: the tail integral of an
   `L¹`-function is continuous on `[0,1]` and tends to `0` at `+∞`.  The vanishing of the
   `L₁₂`-mode at `z = 0` is the class field `hg.l12`.

`Work.Construction.L12`/`Work.Construction.L12dens` are definitionally `Work.Elliptic.L12`/
`Work.Elliptic.L12dens` (they are `Work.FM.L12 Spaces.K`/`Work.FM.L12dens Spaces.K`, and
`Spaces.K = Elliptic.Ktheta = 3 sinθ cos²θ`), so all three facts transfer by `rfl`-level
definitional unfolding; the only things that are *not* definitional are the two scalar
identities `L12dens = 3·F_*/·` and `3·F_*/· = L12dens`, which are closed by `ring`.
-/

theorem L12_classC_facts {α : ℝ} {g : ℝ → ℝ → ℝ} (hg : Work.FTS.ClassC.ClassC α g) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) ∧
    (∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
      (-(Work.Construction.L12dens g z)) z) ∧
    ContinuousOn (fun z => Work.Construction.L12 g z) (Set.Icc 0 1) ∧
    Filter.Tendsto (fun z => Work.Construction.L12 g z) Filter.atTop (nhds 0) := by
  -- `ClassC` gives continuity on the open quadrant and `ℋ⁴`-honesty
  have hcont : ContinuousOn (Function.uncurry g) Work.FTS.EllipticEst.Q0 := hg.reg.continuousOn
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hg.reg (by norm_num) hg.mem
  -- (1) the density is `L¹` on `(0,∞)`
  have hint : MeasureTheory.IntegrableOn (Work.Construction.L12dens g) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem4
  have hintE : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi 0) := hint
  -- `F_*/·` is integrable: it is `L12dens/3` (`L12dens = 3·F_*/·`), off the null point `0`
  have hFint : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) := by
    have h3 : MeasureTheory.IntegrableOn (fun r => Work.Elliptic.L12dens g r / 3) (Set.Ioi 0) :=
      hintE.div_const 3
    refine MeasureTheory.IntegrableOn.congr_fun_ae h3 ?_
    filter_upwards with r
    rw [Work.Elliptic.L12dens_eq_three_Fstar_div g r]
    ring
  -- (2) the derivative, from the fundamental theorem of calculus for the tail integral
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => Work.Construction.L12 g z)
      (-(Work.Construction.L12dens g z)) z := by
    intro z hz
    have h := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g (fun m => hg.fsm m) hFint z hz
    have hval : 3 * Work.Elliptic.Fstar g z / z = Work.Construction.L12dens g z := by
      have h1 : Work.Construction.L12dens g z = 3 * (Work.Elliptic.Fstar g z / z) :=
        Work.Elliptic.L12dens_eq_three_Fstar_div g z
      rw [h1]; ring
    exact h.congr_deriv (by rw [hval])
  -- (3)+(4) continuity on `[0,1]` and decay at `+∞`, from `L₁₂(g)(0) = 0` and `L¹`-ness
  have h0 : Work.Elliptic.L12 g 0 = 0 := hg.l12
  obtain ⟨-, htend, hcontIcc⟩ := Work.Elliptic.L12_values g hintE h0
  exact ⟨hint, hderiv, hcontIcc, htend⟩

end Work.FTS_EllLimOK.PkgJets
