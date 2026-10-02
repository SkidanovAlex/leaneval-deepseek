/-
# SeedExist — the Leau–Fatou flower at the seed

The `FatouParabolic`/`FatouCoordFix` area supplies `exists_parabolicFlowerFix`: at a simple
parabolic point `z₁` of `F c = (T_c)^[10]` (with `F''(z₁) ≠ 0`) there is a repaired Leau–Fatou
flower `ParabolicFlowerFix (F c) ((T_c)^[5]) z₁`, i.e. an attracting petal `Pa` with its
antiholomorphic Fatou coordinate, a `g`-invariant half-petal `Pg`, and the Abel equation
`φa ∘ F = φa + 1` on `Pa`.

This file instantiates that existence theorem at a `RootSeedData`: the seed carries exactly the
hypotheses `deriv F z₁ = 1`, `F''(z₁) ≠ 0`, `(T_c)^[5] z₁ = z₁`, and the differentiability of `F`,
of `star ∘ (T_c)^[5]`, and `g ∘ g = F` are the lemmas of `Work.Final.RootArc`.
-/
import Submission.Work.SeedExist.Setup
import Submission.Work.Final.RootArc
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The Leau–Fatou flower at the seed**: the repaired parabolic flower of
`F c = (T_c)^[10]` at `z₁`, with second return map `g = (T_c)^[5]`. -/
noncomputable def flowerOf (S : RootSeedData) :
    Work.FatouCoordFix.ParabolicFlowerFix (Work.FSeed.F S.c) ((Tantibar S.c)^[5]) S.z₁ :=
  Classical.choice (Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix
    (Work.FSeed.F S.c) ((Tantibar S.c)^[5]) S.z₁
    (Work.Final.differentiable_F S.c)
    (Work.Final.differentiable_star_Tantibar_five S.c)
    (Work.Final.Tantibar_five_comp_self S.c)
    (Work.Final.Tantibar_five_fix S.g_fix)
    S.mult_one S.simple S.g_fix)

/-- The petal `Pa` of the flower lies in the filled Julia set. -/
theorem flowerOf_Pa_subset_K (S : RootSeedData) : (flowerOf S).Pa ⊆ Work.EL.K S.c :=
  Work.ELRig.Pa_subset_K (fl := Work.FatouCoordFix.ParabolicFlowerFix.toParabolicFlower (flowerOf S))

end Work.SeedExist

end
