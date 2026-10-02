/-
# `Work.MandelWire.endgame_at` — the pointed endgame of the mandelbar theorem

Area `Submission/Work/MandelWire/`.  This is item **W8** of
`Submission/Work/NOTES_LEAD_mandelbar_wire.md` §B.3: the *pointed* copy of
`Work.Final.FinalInputs.endgame_hypotheses` + `Work.Final.mandelbar_not_path_connected_of_inputs`
at a **free** parameter `c₀` (with its root-arc data `A : Work.Final.RootArc c₀` as a binder,
instead of the opaque `Work.FinalFix.c₀Of` of an existential root).

The only difference with respect to `Work.Final.Main` is the source of the non-realness of `c₀`:
there it came from the root export (`Work.FinalFix.nonreal_c₀Of`), here it is the derived
`Work.FinalFix.nonreal A.d` — the non-realness of the parameter of *any* root-parabolic arc,
which does not mention `Classical.choose`.  Everything else is the delivered glue of
`Submission/Work/Final/Glue.lean`:

* `hwin` — `Work.Final.window_separation` (Landing arithmetic);
* `hθ`  — `Work.Final.notMem_closure_top_paramRay_windowAngle` (Goldberg–Milnor);
* `hq`  — non-realness (`c₀ ≠ 1/4`);
* `hreal` — the real-ray clause at `1/4` (`Work.Final.quarter_mem_closure_paramRay_zero`,
  `notMem_closure_paramRay_zero_of_im_ne_zero`);
* `hp`  — the limit point of the window-angle ray, at `1/4`
  (`Work.Final.exists_limitPoint_windowAngle`, using `repAngle_quarter`);
* `hLB` — the `noPath` hypothesis, used verbatim;
* `hX`  — `Work.Final.hX_of_twoSided`, applied to the GATE `twoSided` hypothesis.

The endgame itself is `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch` (Jordan form
discharged).
-/
import Mathlib
import Submission.Work.MandelWire.Deps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelWire

/-- **The pointed endgame.**  From the root-arc data at an arbitrary parameter `c₀`, the two
residuals `noPath` and `twoSided` of `NOTES_LEAD_mandelbar_arc_top.md` §2.3, and the three
delivered parameter-plane inputs (`nakane`, `gm`, `repAngle`, plus the quarter row
`repAngle_quarter`), the mandelbar is not path-connected.  This is
`Work.Final.mandelbar_not_path_connected_of_inputs` with the root bundle replaced by the pointed
`RootArc` data (`nonreal` derived from `A.d`). -/
theorem endgame_at {c₀ : ℂ} (A : Work.Final.RootArc c₀) (Nm : Set ℂ)
    (noPath : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ LeanEval.ComplexAnalysis.Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ Nm))
    (twoSided : Work.GATE.TwoSided c₀ Nm)
    (nakane : Work.ParamRays.NakaneInput) (gm : Work.FSeed.RepellingRayParamStable)
    (repAngle : Work.Final.ParamAngleRepelling c₀)
    (repAngle_quarter : Work.Final.ParamAngleRepelling (1 / 4 : ℂ)) :
    ¬ IsPathConnected LeanEval.ComplexAnalysis.Mandelbar := by
  -- `c₀` is non-real, from the root-parabolic structure alone (no `Classical.choose`).
  have hnonreal : c₀.im ≠ 0 := Work.FinalFix.nonreal A.d
  have hq : c₀ ≠ (1 / 4 : ℂ) := by
    intro h
    exact hnonreal (by rw [h]; simp)
  have hN := Work.ParamRaysCrit.nakaneData nakane
  obtain ⟨p, hpMb, hpcl, hpq, -⟩ :=
    Work.Final.exists_limitPoint_windowAngle hN gm repAngle_quarter
  exact Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch Work.ParamRays.Phi hN c₀ Nm
    Work.Final.alpha1 Work.Final.alpha2 Work.Final.windowAngle Work.Final.windowEps
    Work.Final.window_separation
    (Work.Final.notMem_closure_top_paramRay_windowAngle hN gm repAngle)
    hq
    ⟨Work.ParamRays.quarter_mem,
      by rw [Work.Final.top_paramRay_eq hN 0]
         exact Work.Final.quarter_mem_closure_paramRay_zero nakane,
      by rw [Work.Final.top_paramRay_eq hN 0]
         exact Work.Final.notMem_closure_paramRay_zero_of_im_ne_zero nakane hnonreal⟩
    ⟨p, hpMb, hpcl, hpq⟩
    noPath
    (Work.Final.hX_of_twoSided twoSided)

end Work.MandelWire
