/-
# `Work.FTS.RegPkgGal.PartsAssembly` — the deliverable with the primitive R5 hypothesis

**THE HEADLINE, IN THE FORM THE LEAD CAN INSTANTIATE.**  `R5Parts α S g Φ` (`R5Parts.lean`) bundles
the constituents of the right-hand side of the fake-time equation; `R5Slot_of_R5Parts` turns them into
the composite interface; composing with `GalMinAssembly.forall_regPkg_of_galMin` gives the package

    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g)

from (i) the reduced bundle `GalMin` — whose class data is now the *single* conjunct
`St1Class α S g` (`St1Class.lean`) — and (ii) `R5Parts`, i.e. the primitive R5 data (the `Jet`s and
`z`-differentiabilities of `𝓛_Γ^T(g)(τ)`, `N₀`, `N`, `N_*`, the bound and `τ`-modulus of `mubar`, and
the three boundary values), with **no** hypothesis that restates the conclusion.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE DELIVERABLE, ON THE PRIMITIVE R5 INPUT.**  See the module docstring. -/
theorem forall_regPkg_of_parts {α : ℝ} {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, GalMin α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  refine forall_regPkg_of_galMin (g := g) (Φ := Φ) H (fun S hS => ?_)
  obtain ⟨Lz7, hH⟩ := H S hS
  exact R5Slot_of_R5Parts (g := g) (Φ := Φ) hH.hα hH.hα13 hH.hS (H5 S hS)

end Work.FTS.RegPkgGal
