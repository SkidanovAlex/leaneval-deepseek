import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.HALG.fibrationSetup
import Submission.Work.Pi6.HALG.rangeInputsY
import Submission.Work.Pi6.HALG.rangeInputsZ
import Submission.Work.Pi6.HALG.stageB
import Submission.Work.Pi6.HALG.stageBmod2
import Submission.Work.Pi6.HALG.stagePH5
import Submission.Work.Pi6.HALG.stageC
import Submission.Work.Pi6.HALG.stageCmod2
import Submission.Work.Pi6.HALG.cyclicZ
import Submission.Work.Pi6.HALG.bocksteinTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA HALG — the homology algebra of the killing tower (`H₅Y ≅ ℤ/2`, `H₆Z ≅ ℤ/12`)

`Work.Pi6.homologyAlg` assembles the areas' results:
`Work.Pi6.HALG.stageB` (`H₅(Y;ℤ) ≅ ℤ/2`, `|H₆(Y;ℤ)| = 6`), `Work.Pi6.HALG.stageBmod2`
(`|H₇(Y;𝔽₂)| = 2`, `H₇(Y;ℤ) = 2·H₇(Y;ℤ)`), `Work.Pi6.HALG.stagePH5` (`H₅(P₅;ℤ) ≅ ℤ/2`),
`Work.Pi6.HALG.stageC` (`|H₆(Z;ℤ)| = 12`), `Work.Pi6.HALG.stageCmod2` (`|H₆(Z;𝔽₂)| = 2`),
`Work.Pi6.HALG.cyclicZ` (order `12` plus `Z/2Z` of order `2` force cyclicity) and the shared
mod-2 Bockstein input `Work.Pi6.HALG.bocksteinTwo`.
-/

namespace Work.Pi6

theorem homologyAlg (hR : Work.Pi6.SerreRangeLES) (hE : Work.Pi6.EFacts)
    (hZt : Work.Pi6.EMTableZ) (hT : Work.Pi6.TowerPi) : Work.Pi6.HomologyAlg := by
  intro P3 instP3 g3 h3 P4 instP4 g4 h4 hK4
  obtain ⟨h5Y, h6Y⟩ := HALG.stageB hR hE hZt hT P3 g3 h3 P4 g4 h4 hK4
  refine ⟨h5Y, ?_⟩
  intro P5 instP5 g5 h5 hK5 hf
  obtain ⟨h7mod2, h7div⟩ :=
    HALG.stageBmod2 HALG.bocksteinTwo hR hE hZt hT P3 g3 h3 P4 g4 h4 hK4 h5Y h6Y
  obtain ⟨h5P5⟩ := HALG.stagePH5 hR hT P3 g3 h3 P4 g4 h4 P5 g5 h5 h5Y
  have hcard : Nat.card ↥(HR ℤ (Zcov g3 g4 g5) 6) = 12 :=
    HALG.stageC hR hZt hT P3 g3 h3 P4 g4 h4 hK4 P5 g5 h5 hK5 h5Y h6Y h7div
  have hmod2 : Nat.card ↥(HR (ZMod 2) (Zcov g3 g4 g5) 6) = 2 :=
    HALG.stageCmod2 HALG.bocksteinTwo hR hZt hT P3 g3 h3 P4 g4 h4 hK4
      P5 g5 h5 hK5 hf h5Y h6Y h7mod2 ⟨h5P5⟩
  obtain ⟨h5Z, -, -⟩ := HALG.rangeInputsZ hT P3 g3 h3 P4 g4 h4 P5 g5 h5
  have h5Zs : Subsingleton ↥(HR ℤ (Zcov g3 g4 g5) 5) :=
    ModuleCat.subsingleton_of_isZero (h5Z 5 (by norm_num) (by norm_num))
  exact ⟨HALG.cyclicZ HALG.bocksteinTwo (Zcov g3 g4 g5) hcard hmod2 h5Zs, hcard⟩

end Work.Pi6
