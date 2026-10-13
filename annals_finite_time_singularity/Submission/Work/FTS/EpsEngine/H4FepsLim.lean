/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/H4FepsLim.lean` — `(H4)(b)` for `Feps`, completely unconditional

The `perz`-input `hz` of `HkMem_epsLim_noTraces` is produced by the proved child
`Work.FTS.EpsEngine.perz_iter_feps_le` (a genuine Cauchy–Schwarz/averaging estimate, not a trace
condition), and the datum's per-`z` bound by `HkIntegrand_perz_le_noTraces`.  Hence the limit slice
of the projected scheme is `ℋ⁴`-honest from the `XBall` invariant curve alone.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.H4Feps
import Submission.Work.FTS.EpsEngine.perz_iter_feps_le

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

/-- **`(H4)(b)` for `Feps`, completely unconditional** (the per-`z` bound `hz` is produced by the
proved child `perz_iter_feps_le`, and the datum's is by `HkIntegrand_perz_le_noTraces`). -/
theorem HkMem_epsLim_feps {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Fn} {E : Fn → Fn} {ε : ℝ} {g₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen g₀) (h₀mem : Work.Spaces.HkMem α 6 g₀)
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
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    Work.Spaces.HkMem α 4 (slice (epsLim α ρ ε Φs E g₀) τ) := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_perz_le_noTraces
  have h0perz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g₀ z θ) ≤ Bz :=
    fun z hz => ⟨Cz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α g₀) ^ 2,
      hCz α g₀ hα h0 h₀mem z hz⟩
  have hzit := perz_iter_feps_le (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R)
    (Lw := Lw) (ε := ε) (τ := τ) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    hρ hα hε hε1 hR hLw hτ.1 hEll hstar hml
    (fun n s hs => hP n s ⟨hs.1, le_trans hs.2 hτ.2⟩)
    (fun n s hs t ht => hEq n s ⟨hs.1, le_trans hs.2 hτ.2⟩ t ⟨ht.1, le_trans ht.2 hτ.2⟩)
    h0perz
  have hmem4 : Work.Spaces.HkMem α 4 g₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open h0 4 (by norm_num) h₀mem
  exact HkMem_epsLim_noTraces (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs)
    (Lw := Lw) (δ := δ) (q := q) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (g₀ := g₀)
    hα hρ hε hε1 hEll hstar hml hR hLw h0 hmem4 hδ hq0 hq1 hP hEq hpair hmoll hconv hτ
    (fun z hz => hzit z hz)

end Work.FTS.EpsEngine
