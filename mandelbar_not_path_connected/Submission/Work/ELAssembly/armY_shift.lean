import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELAssembly.pullD_pair

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## The shift of the level-`(n+1)` arm pairs of the `b₂`-nest under `(Tantibar c)^[6]`

The three arm pairs `Za n`, `Zb n`, `Zc n` of the nest at `b₂` have first angles
`armA1 n`, `armB1 n`, `armC1 n`.  The level-`(n+1)` first angles are carried back to the
level-`n` first angles by the sixth iterate of the angle-doubling map
(`Work.ELAssembly.pullD_pair`), and landing is equivariant under the iterates of `Tantibar c`
(`Work.ELNest.landsN_iterate`, whose one-step case is `Work.ELTop.landsN_map`).  Since a ray
lands at most once (`Work.ELNest.landsN_unique`), the images of the level-`(n+1)` landing
points are the level-`n` landing points.

Only the *first* angle of each pair is used: the co-landing field `lands_a` together with the
angle specification `Zaa`/`Zba`/`Zca` pins the landing point `y` down. -/

/-- **The level-`(n+1)` arm-`A` landing point maps to the level-`n` one.** -/
theorem armY_shift {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) :
    (∀ n : ℕ, ((LeanEval.ComplexAnalysis.Tantibar c)^[6]) ((N.Za (n + 1)).y) = (N.Za n).y) ∧
    (∀ n : ℕ, ((LeanEval.ComplexAnalysis.Tantibar c)^[6]) ((N.Zb (n + 1)).y) = (N.Zb n).y) ∧
    (∀ n : ℕ, ((LeanEval.ComplexAnalysis.Tantibar c)^[6]) ((N.Zc (n + 1)).y) = (N.Zc n).y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    -- the first angle of the level-`(n+1)` pair, pushed forward by `(Tantibar c)^[6]`
    have hlan := Work.ELNest.landsN_iterate d.hN d.bottcher 6
      (N.Zaa (n + 1) ▸ (N.Za (n + 1)).lands_a)
    -- its angle is `T^[6] (armA1 (n+1)) = armA1 n`
    rw [(pullD_pair n).1] at hlan
    -- the defining property of `(Za n).y`: it is the landing point of the same ray
    have h2 : Work.EL.LandsN d.hN (Work.ELNest.armA1 n) ((N.Za n).y) :=
      N.Zaa n ▸ (N.Za n).lands_a
    exact (Work.ELNest.landsN_unique h2 hlan).symm
  · intro n
    have hlan := Work.ELNest.landsN_iterate d.hN d.bottcher 6
      (N.Zba (n + 1) ▸ (N.Zb (n + 1)).lands_a)
    rw [(pullD_pair n).2.2.1] at hlan
    have h2 : Work.EL.LandsN d.hN (Work.ELNest.armB1 n) ((N.Zb n).y) :=
      N.Zba n ▸ (N.Zb n).lands_a
    exact (Work.ELNest.landsN_unique h2 hlan).symm
  · intro n
    have hlan := Work.ELNest.landsN_iterate d.hN d.bottcher 6
      (N.Zca (n + 1) ▸ (N.Zc (n + 1)).lands_a)
    rw [(pullD_pair n).2.2.2.2.1] at hlan
    have h2 : Work.EL.LandsN d.hN (Work.ELNest.armC1 n) ((N.Zc n).y) :=
      N.Zca n ▸ (N.Zc n).lands_a
    exact (Work.ELNest.landsN_unique h2 hlan).symm

end Work.ELAssembly
