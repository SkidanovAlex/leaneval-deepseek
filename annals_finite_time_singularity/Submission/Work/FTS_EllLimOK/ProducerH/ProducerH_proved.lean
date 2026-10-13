/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ProducerH.ProducerH_proved` — the honest fields from route (b)

The lead's ruling installs `RulingELF.ProducerH` — the bundle of the three producers `L1`, `L2`,
`L3` from the level-`8` existence class:

* `pkgCos_of_ellClassOk` (`L1`) — `PkgCos`: `PhiTil α g (E g)/cos θ ∈ ℋ⁰` (Hardy at `π/2`);
* `pkgMemSqH_of_ellClassOk` (`L2`) — `PkgMemSqH`: the two `ℋ⁰`-memberships with the quadratic bound
  `Ce·Xn6²` and the `z`-local slice bound;
* `pkgBoxH_of_ellClassOk2` (`L3`) — `PkgBoxH`: closed-box `C²` with sup bounds `K·Xn6` and a
  Hölder-`β` modulus of the second derivative (boundary Schauder at the angular edges).

The three are bundled here, taking the minimum of the three `α`-thresholds and monotonicity of the
frozen packages in `Ce` (`ClassC.A4.EllPkgGo_mono`, `ClassC.A4.EllPkgK_mono`) to pass to the common
constant `max Ce Ce'`.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.pkgCos_of_ellClassOk
import Submission.Work.FTS_EllLimOK.ProducerH.pkgMemSqH_of_ellClassOk
import Submission.Work.FTS_EllLimOK.ProducerH.pkgBoxH_of_ellClassOk2
import Submission.Work.FTS.ClassC.A4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_EllLimOK.ProducerH

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The honest fields from route (b)**: `L1 ∧ L2 ∧ L3` as the single bundle
`RulingELF.ProducerH`. -/
theorem ProducerH_proved : Work.FTS_EllLimOK.RulingELF.ProducerH := by
  obtain ⟨α1, hα1, hL1⟩ := pkgCos_of_ellClassOk
  obtain ⟨α2, hα2, hL2⟩ := pkgMemSqH_of_ellClassOk
  obtain ⟨α3, hα3, hL3⟩ := pkgBoxH_of_ellClassOk2
  refine ⟨min (min α1 α2) α3, lt_min (lt_min hα1 hα2) hα3, fun α hα hle Ce E hE => ?_⟩
  have h1 : α ≤ α1 := le_trans hle (le_trans (min_le_left (min α1 α2) α3) (min_le_left α1 α2))
  have h2 : α ≤ α2 := le_trans hle (le_trans (min_le_left (min α1 α2) α3) (min_le_right α1 α2))
  have h3 : α ≤ α3 := le_trans hle (min_le_right (min α1 α2) α3)
  obtain ⟨Ce₂, hCe₂, hmemsq⟩ := hL2 α hα h2 Ce E hE
  refine ⟨Ce₂, hCe₂, ?_, hL1 α hα h1 E (fun g hg => (hE g hg).1), hmemsq, hL3 α hα h3 Ce E hE⟩
  -- `HasPkg` at the larger constant, by monotonicity of the two packages
  intro g hg
  obtain ⟨-, hGo, hK⟩ := hE g hg
  exact ⟨Work.FTS.ClassC.EllPkgGo_mono hα hGo (le_max_left _ _),
    Work.FTS.ClassC.EllPkgK_mono hK (le_max_left _ _)⟩

end Work.FTS_EllLimOK.ProducerH
