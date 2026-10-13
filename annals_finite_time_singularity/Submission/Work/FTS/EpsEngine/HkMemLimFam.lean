/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/HkMemLimFam.lean` — `(H4)(b)`: the LIMIT slice of the projected
# scheme is `ℋ⁴`-honest

This module assembles the limit step of the `(H4)` chapter (`NOTES_HkMemIterAll.md`), combining

* `exists_RHSData_feps_of_traces` (`RHSDataFeps.lean`) — the per-curve right-hand-side data,
  from the trace data of the right-hand side alone,
* `HkMem_iter_all` (`HkMemIterAll.lean`) — the iterate-wise `ℋ⁴`-honesty and the uniform norm
  bound,
* `tendsto_mixed_epsIter_limFam` (proved) — the pointwise convergence of the mixed SLOTS of the
  iterates to those of the limit (`j + i ≤ 4`),
* `smoothOpen_limFam_slice` (`LimSmoothOpen.lean`, proved) — `C^∞` on the quadrant of the limit
  slice,
* `HkMem_limFam_of_slot_conv` (`HkMemIterAll.lean`) — Fatou (`StrongEps.HkMem_of_tendsto`).

The per-`z` input of the Fatou step (uniform in the iterate index) is taken as the explicit
hypothesis `hz`; on the route it is produced by `perz_iter_slice_le_of_RHS` from the per-`z` bound
of the right-hand side (which `perz_Feps_of_traces` supplies, uniformly in the Picard index).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.RHSDataFeps
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps.EpsLocalPStar (iter)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`(H4)(b)` for the projected scheme.**  If every Picard iterate stays in the `X`-ball, is
`EpsSq`-Lipschitz in the fake time, satisfies the geometric pair bound and the mollified form, and
the right-hand side has the trace data `BdryTraces α 6` along every iterate curve, then the limit
slice is `ℋ⁴`-honest (given the per-`z` bound of the iterates, uniform in the index). -/
theorem HkMem_epsLim_of_traces {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (h₀mem : Work.Spaces.HkMem α 4 h₀)
    (hδ : 0 ≤ δ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E h₀ n) s z θ - slice (epsIter α ρ ε Φs E h₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E h₀ n) s z θ - slice (epsIter α ρ ε Φs E h₀ m) s z θ)
        ≤ q ^ n)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n s) z θ
          - epsC α ρ ε Φs E h₀ n s * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E h₀ N) s z θ)
        Filter.atTop (nhds (slice (epsLim α ρ ε Φs E h₀) s z θ)))
    (htr : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      Work.FTS.Nonlin.BdryTraces α 6 (Feps α ρ ε Φs E (slice (epsIter α ρ ε Φs E h₀ n) s)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (slice (epsIter α ρ ε Φs E h₀ n) τ) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 (slice (epsLim α ρ ε Φs E h₀) τ) := by
  -- ## the per-curve right-hand-side data, from the trace data
  obtain ⟨B, hBpos, hRH⟩ :=
    exists_RHSData_feps_of_traces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := h₀)
      hρ hα hε hε1 hR hLw hδ hEll hstar hml
  -- ## the iterate-wise `ℋ⁴`-honesty and the uniform norm bound
  have hiter := HkMem_iter_all (α := α) (B := B)
    (F := Feps α ρ ε Φs E) (h₀ := h₀) (k := 4) (T := δ) (τ := τ)
    hτ.1 hτ.2 hδ hBpos.le h0 h₀mem
    (fun n => (hP n τ hτ).smoothOpen)
    (fun n => hRH n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht)
      (fun s hs => htr n s hs))
  have hbd : ∀ n : ℕ,
      Work.Spaces.HkNorm α 4 (slice (iter (Feps α ρ ε Φs E) h₀ n) τ)
        ≤ Work.Spaces.HkNorm α 4 h₀ + B * τ := fun n => (hiter n).2
  -- ## the slot convergence and the smoothness of the limit slice
  have hslot := tendsto_mixed_epsIter_limFam (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
    hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  have hsmf : Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E h₀) τ) :=
    smoothOpen_limFam_slice (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
      (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := h₀)
      hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  -- ## Fatou
  exact (Work.FTS.EpsEngine.HkMem_limFam_of_slot_conv (α := α)
    (B := Work.Spaces.HkNorm α 4 h₀ + B * τ) (F := Feps α ρ ε Φs E) (h₀ := h₀) (k := 4) (τ := τ)
    (fun n => (hiter n).1) hbd
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hP n τ hτ).smoothOpen 4)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmf 4)
    (fun j i hji z θ hzq => hslot j i hji z θ hzq.1 hzq.2) hz).1

end Work.FTS.EpsEngine
