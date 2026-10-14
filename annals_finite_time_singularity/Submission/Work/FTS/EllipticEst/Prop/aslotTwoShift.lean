import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AeS1.Assembly
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_bnd
import Submission.Work.FTS.EllipticEst.Cores.step2Ae_fts
import Submission.Work.FTS.EllipticEst.Final.Level0
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.Prop.Level0
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoShift
import Submission.Work.FTS.EllipticEst.TT.weakAngularTermClean
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EpsEngine.mixed_logCoords
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
-- ===== merged: Submission.Work.FTS.EllipticEst.EllGap.ellWeak0Clean =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.EllGap

/-- The level-`0` (`η`-weighted) elliptic estimate `TT.EllWeak0` (Elgindi, `prop:L2` + Steps 1-2 of
`prop:H2`). Pure copying job: see `Submission/Work/FTS/EllipticEst/EllGap/NOTES_ellWeak0Clean.md`
for the complete recipe (which declarations to copy from which file, and the three arity fixes
needed because `TT.EllWeakPos` gained a tenth field `memZPth2`). Nothing new has to be proved.

The copy has in fact already been made in the tree, under the `Prop` namespace, in exactly the
`TT.EllWeakPos`-flavoured class the recipe asks for (so the forbidden `AeData` route of
`Prop/ellWeak0Clean.lean` is *not* used):

* `Submission/Work/FTS/EllipticEst/Prop/l2etaL0Asm.lean` — `Prop.L0.l2eta_weak_of_pieces`, the
  assembly of the level-`0` estimate from the four analytic pieces (verbatim copy of
  `TT.l2eta_weak_of_pieces`, the original module being over the build guard's per-file size
  limit), already carrying the tenth `memZPth2` hypothesis in its curried conclusion;
* `Prop.l0_first` (`Prop/l0_first.lean`, via the arity-fixed bridge `Prop.aeData_of_ellWeakPos`),
  `Prop.l0_grad` (`Prop/l0_grad.lean`) and `Prop.l0_second` (`Prop/l0_second.lean`, from
  `Prop.i1_bare_hh` — the copy of `TT.target_of_mixedHon`'s `I₁` coercivity, which consumes
  precisely the tenth field `EllWeakPos.memZPth2`) — the three analytic inputs;
* `TT.weakAngularTermClean` — the (already clean) angular term.

`Prop.level0` (`Prop/Level0.lean`) is their assembly into the exact statement below, and
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).  Since the
statement of `Prop.level0` is *syntactically identical* to the one requested here, its proof is
re-exported rather than reproduced line by line. -/
theorem ellWeak0Clean : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C :=
  Work.FTS.EllipticEst.Prop.level0

end Work.FTS.EllipticEst.EllGap
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

local notation "Aof" => Work.FTS.EllipticEst.H2W.Aof
local notation "Iz" => Work.Spaces.Iz
local notation "Iθ" => Work.Spaces.Iθ

/-- `z²∂_z²Ψ` is smooth on the open quadrant as soon as `Ψ` is. -/
theorem aofSmoothOpen {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Aof Ψ) :=
  smoothOpen_zsq_mul (hΨ.pzIter 2)

/-- **The `ℋ⁰`-honesty of `D_z (z²∂_z²Ψ)`** for a level-`2` weak datum: the `i = 1` pure summand
of `HkIntegrand α 2 (Aof Ψ)` dominates the weighted square of `D_z (Aof Ψ)`. -/
theorem hkMem_zero_Dz_Aof {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Aof Ψ)) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := smoothOpen_of_forall h.smooth
  exact HkMem_zero_of_pointwise (c := 1) zero_le_one ((aofSmoothOpen hΨ).Dz) h.memA
    (fun z θ hz hθ hlt => by
      rw [HkIntegrand_zero_apply]
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, one_mul] using
        Work.Spaces.sq_le_HkIntegrand_z α 2 (Aof Ψ) z θ 1 (by norm_num))

/-- **The two vanishing endpoint traces of `θ ↦ D_z (z²∂_z²Ψ)(z,θ)`** for a level-`2` weak datum,
a.e. in `z`.  This is the `θ`-flux input of the integrations by parts for the twisted datum
`(Aof Ψ, Gof F)`: it discharges the `hMixS`/`hMixO` hypotheses of
`aslotTwoShift_aeDzTrace_gam` (`hMixO` is `TT.gammaHonesty`, `hMixS` is
`aslotTwoShift_mixedSliceHon`, and the `ℋ⁰`-honesty of `D_z (Aof Ψ)` is `hkMem_zero_Dz_Aof`). -/
theorem aof_tendsto_zero {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => z * Work.Spaces.pz (Aof Ψ) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => z * Work.Spaces.pz (Aof Ψ) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α (Aof Ψ)
      (Work.FTS.EllipticEst.H2W.Gof F) :=
    Work.FTS.EllipticEst.H2W.AeDataAof α F Ψ hα hα4 h
  exact aslotTwoShift_aeDzTrace_gam α (Aof Ψ) (Work.FTS.EllipticEst.H2W.Gof F) hAe
    (hkMem_zero_Dz_Aof h) (aslotTwoShift_mixedSliceHon hα hα4 h)
    (Work.FTS.EllipticEst.TT.gammaHonesty hα hα4 h)






/-! ## The assembly of the target from the level-`0` estimate -/






end Work.FTS.EllipticEst.Prop
end
