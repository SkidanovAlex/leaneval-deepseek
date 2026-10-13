/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/H4Feps.lean` — the `(H4)` chapter for `Feps`, TRACE-FREE

Using the finding of `Submission/Work/FTS/EpsEngine/PerzNoTraces.lean` (the hypothesis
`BdryTraces α 6` of the `z`-slot per-`z` bound is declared but never used) and the trace-free
per-curve data `exists_RHSData_feps_noTraces`, the whole `(H4)` chapter of the local step becomes
*unconditional in the trace data*:

* `HkMem_iter_feps` — `(H4)(a)`: every raw Picard slice is `ℋ⁴`-honest, with a uniform norm bound,
  from the `XBall` curve invariant and the `EpsSq`-time-Lipschitz bound ONLY;
* `HkMem_epsLim_noTraces` — `(H4)(b)`: the limit slice is `ℋ⁴`-honest, from the same data plus the
  geometric pair bound, the mollified form, the slot convergence, and the per-`z` bound `hz` of the
  iterates (which is *not* a trace condition — it is supplied on the route by
  `perz_iter_slice_le_of_RHS_data`, a genuine Cauchy–Schwarz/averaging estimate).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.HkMemIterAll
import Submission.Work.FTS.EpsEngine.RHSDataFepsNoTraces
import Submission.Work.FTS.EpsEngine.HkMemLimFam
import Submission.Work.FTS.EpsEngine.tendsto_mixed_epsIter_limFam
import Submission.Work.FTS.EpsEngine.LimSmoothOpenEngine

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
open Work.FTS.EpsEngine (epsIter epsLim)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`(H4)(a)` for `Feps`, trace-free.**  If the `n`-th Picard curve of the projected scheme stays
in `XBall` and is `EpsSq`-Lipschitz in the fake time, then every raw Picard slice at `τ` is
`ℋ⁴`-honest, with `HkNorm α 4 ≤ HkNorm α 4 g₀ + B τ`. -/
theorem HkMem_iter_feps {α C₀ Ce Cs R Lw ε δ τ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (h0smo : Work.FTS.EllipticEst.SmoothOpen g₀) (h0mem : Work.Spaces.HkMem α 4 g₀)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hτδ : τ ≤ δ)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (iter (Feps α ρ ε Φs E) g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (iter (Feps α ρ ε Φs E) g₀ n) s z θ
          - slice (iter (Feps α ρ ε Φs E) g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      Work.Spaces.HkMem α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ) ∧
      Work.Spaces.HkNorm α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ)
        ≤ Work.Spaces.HkNorm α 4 g₀ + B * τ := by
  obtain ⟨B, hBpos, hRH⟩ :=
    exists_RHSData_feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hδ hEll hstar hml
  refine ⟨B, hBpos, ?_⟩
  exact HkMem_iter_all (α := α) (B := B) (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4)
    (T := δ) (τ := τ) hτ hτδ hδ hBpos.le h0smo h0mem
    (fun n => (hP n τ ⟨hτ, hτδ⟩).smoothOpen)
    (fun n => hRH n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))

/-- **`(H4)(b)` for `Feps`, trace-free.**  The limit slice is `ℋ⁴`-honest, given the per-`z` bound
`hz` of the iterates (uniform in the Picard index) — which is *not* a trace condition. -/
theorem HkMem_epsLim_noTraces {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen g₀) (h₀mem : Work.Spaces.HkMem α 4 g₀)
    (hδ : 0 ≤ δ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E g₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E g₀ n) s z θ - slice (epsIter α ρ ε Φs E g₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E g₀ n) s z θ - slice (epsIter α ρ ε Φs E g₀ m) s z θ)
        ≤ q ^ n)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E g₀ (n + 1)) s z θ
        = g₀ z θ + Work.FTS.StrongEps.Jeps ρ ε (epsPsi α ρ ε Φs E g₀ n s) z θ
          - epsC α ρ ε Φs E g₀ n s * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E g₀ N) s z θ)
        Filter.atTop (nhds (slice (epsLim α ρ ε Φs E g₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (slice (epsIter α ρ ε Φs E g₀ n) τ) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 (slice (epsLim α ρ ε Φs E g₀) τ) := by
  obtain ⟨B, hBpos, hRH⟩ :=
    exists_RHSData_feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
      (Lw := Lw) (ε := ε) (T := δ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
      hρ hα hε hε1 hR hLw hδ hEll hstar hml
  have hiter := HkMem_iter_all (α := α) (B := B)
    (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4) (T := δ) (τ := τ)
    hτ.1 hτ.2 hδ hBpos.le h0 h₀mem
    (fun n => (hP n τ hτ).smoothOpen)
    (fun n => hRH n (fun s hs => hP n s hs) (fun s hs t ht => hEq n s hs t ht))
  have hbd : ∀ n : ℕ,
      Work.Spaces.HkNorm α 4 (slice (iter (Feps α ρ ε Φs E) g₀ n) τ)
        ≤ Work.Spaces.HkNorm α 4 g₀ + B * τ := fun n => (hiter n).2
  have hslot := tendsto_mixed_epsIter_limFam (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := g₀)
    hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  have hsmf : Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E g₀) τ) :=
    smoothOpen_limFam_slice (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
      (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (h₀ := g₀)
      hα hρ hε hε1 hEll hstar hml hR hLw h0 hq0 hq1 hP hEq hpair hmoll hconv hτ
  exact (Work.FTS.EpsEngine.HkMem_limFam_of_slot_conv (α := α)
    (B := Work.Spaces.HkNorm α 4 g₀ + B * τ) (F := Feps α ρ ε Φs E) (h₀ := g₀) (k := 4)
    (τ := τ)
    (fun n => (hiter n).1) hbd
    (fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hP n τ hτ).smoothOpen 4)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsmf 4)
    (fun j i hji z θ hzq => hslot j i hji z θ hzq.1 hzq.2) hz).1

end Work.FTS.EpsEngine
