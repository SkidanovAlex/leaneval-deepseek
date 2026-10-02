/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# The critical orbit and the petals of the root-parabolic seed

This module exports, for the areas that consume the root-parabolic seed, the fact that the
critical orbit of the tenth iterate `F c = (T_c)^[10]` eventually reaches the `g`-invariant
half-petal `Pg` of a flower (`g = (T_c)^[5]`) — part (ii) of the request of the lead
(`NOTES_LEAD_mandelbar_seed.md` §6.4, `Work.SeedExist.FatouCritInBasin`).

Everything here is an immediate consequence of the `enters_Pg` field of the flower: the critical
orbit of `F c` converges to the parabolic point `z₁` without attaining it (`RootParabolic.crit`),
so it enters `Pg`, and then a fortiori enters every forward image `(T_c)^[j] '' Pg` with `j < 5`.

Part (i) of the same request — that the critical *point* `0` lies in the immediate basin of the
parabolic cycle, stated as
`∃ i < 5, ∃ x ∈ fl.Pg, (Tantibar c)^[i] x ∈ connectedComponentIn (interior (filledJulia c)) 0` —
is the dynamical content of Fatou's theorem localised at `0`: it is *not* an immediate consequence
of the flower fields.  It is what `Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_polynomialMap`
(the petal/Liouville core of this area) establishes, in the form "a critical point of `F` lies in
the basin of `z₁`"; see `Submission/Work/FatouParabolic/NOTES.md` §4 for the precise relation and
the missing identification of the immediate basin with the component of `0`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.FQC.Petal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-- **(ii) of the lead's request**: if the critical orbit of the tenth iterate `F c` converges to
the parabolic point `z₁` without attaining it, then some point of that orbit lies in the
`g`-invariant half-petal `Pg` of the flower at `z₁`. -/
theorem critOrbit_enters_Pg {c z : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z)
    (hconv : Tendsto (fun n : ℕ => (Work.EL.F c)^[n] c) atTop (𝓝 z))
    (hne : ∀ n : ℕ, (Work.EL.F c)^[n] c ≠ z) :
    ∃ N : ℕ, (Work.EL.F c)^[N] c ∈ fl.Pg :=
  fl.enters_Pg c hconv hne

/-- **(ii) of the lead's request, in the form stated there**: some point of the critical orbit of
`F c` lies in a forward image `(T_c)^[j] '' Pg` with `j < 5`. -/
theorem critOrbit_enters_image_Pg {c z : ℂ}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.EL.F c) ((Tantibar c)^[5]) z)
    (hconv : Tendsto (fun n : ℕ => (Work.EL.F c)^[n] c) atTop (𝓝 z))
    (hne : ∀ n : ℕ, (Work.EL.F c)^[n] c ≠ z) :
    ∃ N j : ℕ, j < 5 ∧ (Work.EL.F c)^[N] c ∈ (Tantibar c)^[j] '' fl.Pg := by
  obtain ⟨N, hN⟩ := critOrbit_enters_Pg fl hconv hne
  exact ⟨N, 0, by norm_num, by simpa using hN⟩

/-- The same statement from the petal interface `Work.FQC.PetalInput` of the root-parabolic
data, which is the form in which the deformation area carries the fundamental domain. -/
theorem critOrbit_enters_image_Pg_of_petalInput {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) :
    ∃ N j : ℕ, j < 5 ∧ (Work.EL.F c)^[N] c ∈ (Tantibar c)^[j] '' hpetal.Pg := by
  obtain ⟨N, hN⟩ := hpetal.enters_Pg c d.crit.1 d.crit.2
  exact ⟨N, 0, by norm_num, by simpa using hN⟩

end

end Work.FatouParabolic
