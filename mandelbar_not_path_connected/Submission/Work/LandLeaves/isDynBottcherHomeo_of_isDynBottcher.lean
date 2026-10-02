import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.SeedDyn.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **Every Böttcher coordinate of `T_c` is a Böttcher homeomorphism.**

The characterisation `Work.ParamRays.IsDynBottcher c φ` (continuity on the escaping set, the
functional equation `φ (T_c z) = conj (φ z) ^ 2`, and asymptotics `φ z ~ z` at infinity) does
*not* by itself mention injectivity or surjectivity.  Those two extra properties are nonetheless
forced:

* by `dynBottcherOnlyOnMandelbar` the existence of `φ` puts `c` in the mandelbar;
* at `c ∈ M*` the construction of `Work.SeedDyn` produces a Böttcher *homeomorphism*
  `Work.SeedDyn.isDynBottcherHomeo hc : Work.Landing.IsDynBottcherHomeo c (dynPhiOf c)`;
* the two coordinates `φ` and `dynPhiOf c` agree pointwise on the escaping set
  (`Work.ParamRays.isDynBottcher_unique`), so injectivity and surjectivity transfer. -/
theorem isDynBottcherHomeo_of_isDynBottcher {c : ℂ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) : Work.Landing.IsDynBottcherHomeo c φ := by
  have hc : c ∈ Mandelbar := dynBottcherOnlyOnMandelbar c ⟨φ, hφ⟩
  have hex : Work.ParamRays.DynBottcherExists c := ⟨φ, hφ⟩
  obtain ⟨hφ₀, hinj, hsurj⟩ := Work.SeedDyn.isDynBottcherHomeo hc
  refine ⟨hφ, ?_, ?_⟩
  · intro z w hz hw h
    refine hinj z w hz hw ?_
    rw [Work.ParamRays.dynPhiOf_eq_of_isDynBottcher hex hφ hz,
      Work.ParamRays.dynPhiOf_eq_of_isDynBottcher hex hφ hw]
    exact h
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hsurj w hw
    exact ⟨z, hz, by
      rw [← Work.ParamRays.dynPhiOf_eq_of_isDynBottcher hex hφ hz]; exact hzw⟩

end Work.LandLeaves
