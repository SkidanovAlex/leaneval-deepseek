/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/RHSDataFepsNoTraces.lean` — `RHSData` for the scheme's
# right-hand side, with NO trace input

This is the trace-free form of `Submission/Work/FTS/EpsEngine/RHSDataFeps.lean`, using the
finding of `Submission/Work/FTS/EpsEngine/PerzNoTraces.lean`: the `perz` field of `RHSData`
does **not** need the boundary-trace data `BdryTraces α 6 (Feps …)` (the hypothesis is declared
but unused in `E5Aux.HkIntegrand_zslot_perz_le`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.HkMemIterAll
import Submission.Work.FTS.EpsEngine.PerzNoTraces
import Submission.Work.FTS.EpsEngine.FepsData
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

/-- **The per-`z` energy bound of the projected scheme's right-hand side, trace-free form** (the
analogue of `HkIntegrand_perz_RHS` without the `htr` hypothesis). -/
theorem HkIntegrand_perz_RHS_noTraces {α Ce T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 ≤ T) (hCe : 0 ≤ Ce)
    (hreg : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hmem : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s))
    (hbd6 : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) ≤ Ce) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc 0 T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_perz_le_noTraces
  refine ⟨C, hCpos, ?_⟩
  intro z hz s hs
  refine le_trans (hC α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) hα (hreg s hs) (hmem s hs)
    z hz) ?_
  have h1 : (1 : ℝ) ≤ 1 + Ce := by linarith
  have h2 : (1 : ℝ) + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)
      ≤ 1 + Ce := by linarith [hbd6 s hs]
  have h3 : (0 : ℝ)
      ≤ 1 + Work.FTS.StrongGlobal.Xn6 α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) := by
    have := Work.Spaces.HkNorm_nonneg α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s)
    rw [Work.FTS.StrongGlobal.Xn6]
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2)
    (mul_nonneg hCpos.le (by positivity))

/-- **The per-`z` energy bound of the scheme's right-hand side along an `XBall` curve, with no
trace input.** -/
theorem perz_Feps_noTraces {α C₀ Ce Cs R ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F₀ : ℝ → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hX : ∀ s ∈ Set.Icc (0 : ℝ) T, XBall α ρ ε R C₀ (F₀ s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  set G : Fam := fun z θ s => F₀ s z θ with hG
  have hslice : ∀ s : ℝ, slice G s = F₀ s := fun s => rfl
  have hRH : ∀ s : ℝ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E G s = Feps α ρ ε Φs E (F₀ s) := by
    intro s
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice, hslice s]
  obtain ⟨C, hCpos, hC⟩ :=
    HkIntegrand_perz_RHS_noTraces (α := α) (Ce := Ce') (T := T) (ε := ε) (ρ := ρ) (Φs := Φs)
      (E := E) (g := G) hα hε hε1 hT hCe'pos.le
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).1)
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).2.1)
      (fun s hs => by
        rw [Work.FTS.StrongGlobal.Xn6, hRH s]
        exact (hFeps (F₀ s) (hX s hs)).2.2)
  refine ⟨C * (1 + Ce') ^ 2, by positivity, ?_⟩
  intro z hz s hs
  have h := hC z hz s hs
  rw [hRH s] at h
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ)
      ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Ce') ^ 2 := h
    _ = C * (1 + Ce') ^ 2 * (1 + (Work.Spaces.w z) ^ 2) := by ring

/-- **`RHSData` for the scheme's right-hand side, with NO trace input.**  For every Picard index
`n`: if the curve `s ↦ slice (iter (Feps …) g₀ n) s` lies in the `XBall` invariant and is
`EpsSq`-Lipschitz in `s`, then the per-curve data `RHSData α 4 T B (Feps …) g₀ n` holds, with a
constant `B` depending only on `α, ε, C₀, Ce, Cs, R`. -/
theorem exists_RHSData_feps_noTraces {α C₀ Ce Cs R Lw ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
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
      RHSData α 4 T B (Feps α ρ ε Φs E) g₀ n := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  refine ⟨Ce', hCe'pos, ?_⟩
  intro n hP hEq
  obtain ⟨Cz, hCzpos, hCz⟩ := perz_Feps_noTraces (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (R := R) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
    (F₀ := fun s => slice (iter (Feps α ρ ε Φs E) g₀ n) s)
    hρ hα hε hε1 hR hT hEll hstar hml hP
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
