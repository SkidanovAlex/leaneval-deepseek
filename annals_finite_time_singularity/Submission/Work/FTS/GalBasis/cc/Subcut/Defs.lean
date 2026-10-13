/-
# `Work.FTS.GalBasis.cc.Subcut.Defs` — the localised pieces of `HkSq_sub_psiCut_tendsto`

The complement `χ_N = 1 - ψ N` of the cutoff family has all its mixed `D`-derivatives up to
order `4` supported on the union of

* the `z`-strips `Uz N = {z ∉ Ioo (plo N) (phiN N)}` and
* the angular strips `Ut N = {θ ∉ Ioo (qlo N) (qhi N)}`,

i.e. on `UN N := {p | p.1 ∈ Uz N ∨ p.2 ∈ Ut N}` (this is the statement of `chi_facts`), and the
`θ`-derivatives of `χ_N` are in addition supported on the two angular layers

  `LN N = Icc (tlo N) (2/(N+1)) ∪ Icc (π/2 - 2/(N+1)) (thi N)`

(`CutSpec.lay`).  This module only fixes those three set families (and their measurability), so
that the pieces of the proof of `HkSq_sub_psiCut_tendsto` can be stated uniformly.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Submission.Work.FTS.GalBasis.cc.CutDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

set_option autoImplicit false

/-- The `z`-part of the localisation set `U_N`: the complement of the open plateau
`(plo N, phiN N) = (2/(N+1), N+1)` in the radial variable. -/
def Uz (N : ℕ) : Set ℝ := {z | z ∉ Set.Ioo (plo N) (phiN N)}

/-- The `θ`-part of the localisation set `U_N`: the complement of the open plateau
`(qlo N, qhi N) = (2/(N+1), π/2 - 2/(N+1))` in the angular variable. -/
def Ut (N : ℕ) : Set ℝ := {θ | θ ∉ Set.Ioo (qlo N) (qhi N)}

/-- **The localisation set** `U_N ⊂ ℝ × ℝ`: the mixed derivatives `D_z^bD_θ^a χ_N` (`a+b ≤ 4`)
can be non-zero only here. -/
def UN (N : ℕ) : Set (ℝ × ℝ) := {p | p.1 ∈ Uz N ∨ p.2 ∈ Ut N}

/-- **The two angular layers of the cutoff**: the `θ`-derivatives of `χ_N` vanish off `LN N`. -/
def LN (N : ℕ) : Set ℝ :=
  Set.Icc (tlo N) (2 / ((N : ℝ) + 1)) ∪ Set.Icc (Real.pi / 2 - 2 / ((N : ℝ) + 1)) (thi N)

/-! ## Measurability -/

theorem measurableSet_Uz (N : ℕ) : MeasurableSet (Uz N) :=
  measurableSet_Ioo.compl

theorem measurableSet_Ut (N : ℕ) : MeasurableSet (Ut N) :=
  measurableSet_Ioo.compl

theorem measurableSet_UN (N : ℕ) : MeasurableSet (UN N) :=
  ((measurableSet_Uz N).preimage measurable_fst).union
    ((measurableSet_Ut N).preimage measurable_snd)

theorem measurableSet_LN (N : ℕ) : MeasurableSet (LN N) :=
  measurableSet_Icc.union measurableSet_Icc

end Work.FTS.GalBasis.cc
