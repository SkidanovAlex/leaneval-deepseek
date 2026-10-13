/-
# `Work.FTS.RegPkgGal.GalMinAssembly` — the deliverable on the reduced input

**THE HEADLINE OF THE AREA (reduced-input form).**  `GalMinConv.galHyp_of_galMin` turns the reduced
bundle `GalMin` plus the R5 slot into `GalHyp`; composing with
`Assembly.regPkg_of_galerkin` gives the shape promised by design §4 item 10,

  `∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g)`,

from the input side on which no hypothesis is the conclusion of an R-lemma any more: the five
sup/`z`/`τ`/`∂_z`-quantities are *derived* in `GalMinConv` (`Der.sup_extG`, `Der.sup2_extG`,
`Der.hzmod`, `Der.hzmodp`, `Der.htaumod`, `Der.htaumodp`).

The class-data exports that remain are exactly: `StData` / `StData2` (the `Γ`-vanishing and the
two Taylor conditions at `z = 0`), the two angular moduli `hhθ`/`hhθp`, the frozen interior class
`RegQ (pExp α) 4` with the uniform `ℋ⁴` bound, and the R5 slot (the Jet of the right-hand side, its
three boundary values and its `z`-differentiability).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.Assembly

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

/-- **THE DELIVERABLE, ON THE REDUCED INPUT.**  See the module docstring. -/
theorem forall_regPkg_of_galMin {α : ℝ} {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, GalMin α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, ∃ N0 : ℝ, R5Slot α S g Φ N0) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  intro S hS
  obtain ⟨Lz7, hH⟩ := H S hS
  obtain ⟨N0, h5⟩ := H5 S hS
  obtain ⟨M, Lz, Lθ, Lt, Nz, Nθ, Nt, hgal⟩ := galHyp_of_galMin hH h5
  exact regPkg_of_galerkin hgal h5

end Work.FTS.RegPkgGal
