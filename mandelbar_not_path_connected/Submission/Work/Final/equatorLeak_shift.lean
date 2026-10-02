import Mathlib
import Submission.Work.Final.Defs
import Submission.Work.Final.RootArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The equator leak shifts to the real translates `x`, `x + 1/2`, `x + 1`

`RootArc.EquatorLeak A` says that the repelling equator `E = Ψ '' ℝ` of the parabolic point `z₁`
is not contained in the filled Julia set `Work.EL.K c`: some `Ψ (x : ℂ)`, `x : ℝ`, is *outside*
`K c`.

The equivariance of the repelling coordinate `Ψ` (`ParabolicFlower.Ψ_shift`, `Ψ_anti`) turns the
real translate `x + 1/2` into the antiholomorphic square root `g = (T_c)^5` of the point `Ψ x`,
and the translate `x + 1` into the second return map `F c = (T_c)^{10}`.  Since the escape set
`K cᶜ` is forward invariant under `T_c` (a tail of a bounded orbit is bounded), both images stay
outside `K c`.  Hence the equator leak propagates to all three points of the real translate.
-/

open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Forward invariance of the escape set of `T_c` -/

/-- The filled Julia set `Work.EL.K c` of the unicritical map `T_c` consists of the points with
bounded orbit; adding or removing the *single* first point of an orbit does not change boundedness,
so it is invariant under `T_c`.  (We only need the direction `T_c z ∈ K → z ∈ K` below, but the
equivalence is the natural statement and costs nothing.) -/
theorem mem_K_iff_Tantibar_mem_K (c z : ℂ) :
    z ∈ Work.EL.K c ↔ Tantibar c z ∈ Work.EL.K c := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun n => by rw [← Work.ParamRays.orbit_one_add]; exact hM (n + 1)⟩
  · rintro ⟨M, hM⟩
    refine ⟨max M ‖z‖, fun n => ?_⟩
    match n with
    | 0 => simp
    | (k + 1) => rw [Work.ParamRays.orbit_one_add]; exact le_trans (hM k) (le_max_left _ _)

/-- The escape set is forward invariant: a point outside `Work.EL.K c` keeps all its `T_c`-iterates
outside `Work.EL.K c`. -/
theorem notMem_K_iterate {c z : ℂ} (hz : z ∉ Work.EL.K c) (n : ℕ) :
    (Tantibar c)^[n] z ∉ Work.EL.K c := by
  induction n with
  | zero => simpa using hz
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact fun hmem => ih ((mem_K_iff_Tantibar_mem_K c ((Tantibar c)^[k] z)).mpr hmem)

/-! ## The lemma -/

/-- **The equator leak propagates along the real translates.**  If some point `Ψ (x : ℂ)` of the
repelling equator of the parabolic point escapes to infinity, then so do its images under the
antiholomorphic square root `g = (T_c)^5` and under the second return map `F c = (T_c)^{10}`, which
are exactly `Ψ (x + 1/2)` and `Ψ (x + 1)` by the equivariance of `Ψ`. -/
theorem equatorLeak_shift {c : ℂ} (A : Work.Final.RootArc c)
    (h : Work.Final.RootArc.EquatorLeak A) :
    ∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c ∧
      A.fl.Ψ ((x : ℂ) + 1 / 2) ∉ Work.EL.K c ∧
      A.fl.Ψ ((x : ℂ) + 1) ∉ Work.EL.K c := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, hx, ?_, ?_⟩
  · have hΨ : A.fl.Ψ ((x : ℂ) + 1 / 2) = (Tantibar c)^[5] (A.fl.Ψ (x : ℂ)) := by
      have hh := A.fl.Ψ_anti (x : ℂ)
      simpa using hh
    rw [hΨ]
    exact notMem_K_iterate hx 5
  · have hΨ : A.fl.Ψ ((x : ℂ) + 1) = (Tantibar c)^[10] (A.fl.Ψ (x : ℂ)) :=
      (A.fl.Ψ_shift (x : ℂ)).trans (congrFun (Work.EL.F_eq_tantibar c) (A.fl.Ψ (x : ℂ)))
    rw [hΨ]
    exact notMem_K_iterate hx 10

end Work.Final
