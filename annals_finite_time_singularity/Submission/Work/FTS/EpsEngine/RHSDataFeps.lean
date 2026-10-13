/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/RHSDataFeps.lean` — `RHSData` for the scheme's right-hand side,
# from the TRACE data of the right-hand side alone

This module completes the reduction of the `(H4)` chapter (`EpsEngine/NOTES_HkMemIterAll.md`).
Collecting the three proved producers

* `Feps_data_of_xball` (`FepsData.lean`) — `SmoothOpen`, `HkMem α 6` and ONE `ℋ⁶`-size constant
  `Ce'` for `Feps u` on the `XBall` class (no trace hypothesis),
* `perz_Feps_of_traces` (`RHSDataPerz.lean`) — the per-`z` energy bound, from the size fields via
  the proved `HkIntegrand_perz_RHS`,
* `Feps_gates_of_xball_curve` (`Feps_gates_of_xball_curve.lean`) — the `meas`/`joint`/`sup` gates
  for an `XBall` curve,

the per-curve data `RHSData α 4 T B (Feps α ρ ε Φs E) g₀ n` is produced with the **single** extra
input

    ∀ s ∈ Icc 0 T, BdryTraces α 6 (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ n) s)) .

That input is the class-`C`/flatness item of the local step (see `NOTES_HkMemIterAll.md` §2/§2.bis
for the exact interface it needs).  With `RHSData` in hand, `HkMem_iter_all` and the two ball
clauses (`EpsEngine/HkMemIterAll.lean`) are unconditional in the size data, and
`HkMem_limFam_of_slot_conv` closes the limit step modulo the slot convergence.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.HkMemIterAll
import Submission.Work.FTS.EpsEngine.RHSDataPerz
import Submission.Work.FTS.EpsEngine.Feps_gates_of_xball_curve

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps.EpsLocalPStar (iter)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`RHSData` for the scheme's right-hand side, from its trace data.**  For every Picard index
`n`: if the curve `s ↦ slice (iter (Feps …) g₀ n) s` lies in the `XBall` invariant, is
`EpsSq`-Lipschitz in `s`, and the right-hand side has the trace data `BdryTraces α 6` at every
point of the curve, then the per-curve data `RHSData α 4 T B (Feps …) g₀ n` holds (with a constant
`B` depending only on `α, ε, C₀, Ce, Cs, R`). -/
theorem exists_RHSData_feps_of_traces {α C₀ Ce Cs R Lw ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hLw : 0 ≤ Lw) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        XBall α ρ ε R C₀ (slice (iter (Feps α ρ ε Φs E) g₀ n) s)) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.StrongEps.EpsSq α (fun z θ =>
          slice (iter (Feps α ρ ε Φs E) g₀ n) s z θ
            - slice (iter (Feps α ρ ε Φs E) g₀ n) t z θ)
          ≤ Lw * (s - t) ^ 2) →
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Work.FTS.Nonlin.BdryTraces α 6
          (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) g₀ n) s))) →
      RHSData α 4 T B (Feps α ρ ε Φs E) g₀ n := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  refine ⟨Ce', hCe'pos, ?_⟩
  intro n hP hEq htr
  -- the per-`z` field, from the size data
  obtain ⟨Cz, hCzpos, hCz⟩ := perz_Feps_of_traces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (R := R) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
    (F₀ := fun s => slice (iter (Feps α ρ ε Φs E) g₀ n) s)
    hρ hα hε hε1 hR hT hEll hstar hml hP htr
  -- the three gates
  have hgates := Feps_gates_of_xball_curve (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := T) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
    (g := iter (Feps α ρ ε Φs E) g₀ n) hα hρ hε hε1 hEll hstar hml hR hLw hP hEq
  refine ⟨fun s hs => (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).1,
    fun s hs => Work.FTS.OpenPkg.HkMem_mono_open
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).1 4 (by norm_num)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.1,
    fun s hs => le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.1)
      (hFeps (slice (iter (Feps α ρ ε Φs E) g₀ n) s) (hP s hs)).2.2,
    hgates.1, hgates.2.1, hgates.2.2,
    fun z hz => ⟨Cz * (1 + (Work.Spaces.w z) ^ 2),
      fun s hs => hCz z hz s hs⟩⟩

end Work.FTS.EpsEngine
