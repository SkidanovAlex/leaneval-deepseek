/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/RHSDataPerz.lean` — the `perz` field of `RHSData` for the
# scheme's right-hand side, reduced to its TRACE data

`Work.FTS.EpsEngine.Feps_data_of_xball` discharges the `smo`/`mem`/`bd` fields of `RHSData` (and
the `ℋ⁶`-membership that `HkIntegrand_perz_RHS` needs).  This module supplies the remaining
*size*-shaped field, namely the per-`z` energy bound of the interval-integral lemma
(`Work.FTS.EpsEngine.HkMem_intervalIntegralPerz`'s `hperz`), for the family of right-hand sides
along a curve of `XBall` profiles:

    ∀ z ∈ Iz, ∃ Cz, ∀ s ∈ Icc 0 T, ∫_θ HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ ≤ Cz .

By `HkIntegrand_perz_RHS` (proved) this follows from four items, of which three are *produced*
here by `Feps_data_of_xball` (`SmoothOpen`, `HkMem α 6`, the uniform `ℋ⁶`-size bound) and the
fourth — `BdryTraces α 6 (Feps …)` — is the **single** remaining input of the `(H4)` chapter.

Everything here is `sorry`-free.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.FepsData
import Submission.Work.FTS.EpsEngine.HkIntegrand_perz_RHS

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

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` energy bound of the scheme's right-hand side along an `XBall` curve, from its
trace data.**  The curve is `s ↦ F₀ s` (in the engine, `F₀ s = slice (iter Feps g₀ n) s`), all of
whose points lie in the `XBall` invariant; the only non-size input is `BdryTraces α 6` of the
right-hand side at every point of the curve. -/
theorem perz_Feps_of_traces {α C₀ Ce Cs R ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {F₀ : ℝ → Fn}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E)
    (hX : ∀ s ∈ Set.Icc (0 : ℝ) T, XBall α ρ ε R C₀ (F₀ s))
    (htr : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.BdryTraces α 6 (Feps α ρ ε Φs E (F₀ s))) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (Feps α ρ ε Φs E (F₀ s)) z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) := by
  obtain ⟨Ce', hCe'pos, hFeps⟩ :=
    Feps_data_of_xball (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (R := R) (ε := ε)
      (ρ := ρ) (Φs := Φs) (E := E) hρ hα hε hε1 hR hEll hstar hml
  -- the family whose `s`-slice is `F₀ s`
  set G : Fam := fun z θ s => F₀ s z θ with hG
  have hslice : ∀ s : ℝ, slice G s = F₀ s := fun s => rfl
  have hRH : ∀ s : ℝ, Work.FTS.StrongEps.epsRHSP α ρ ε Φs E G s = Feps α ρ ε Φs E (F₀ s) := by
    intro s
    rw [Work.FTS.EpsEngine.epsRHSP_eq_Feps_slice, hslice s]
  obtain ⟨C, hCpos, hC⟩ :=
    HkIntegrand_perz_RHS (α := α) (Ce := Ce') (T := T) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E)
      (g := G) hα hε hε1 hT hCe'pos.le
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).1)
      (fun s hs => by rw [hRH s]; exact (hFeps (F₀ s) (hX s hs)).2.1)
      (fun s hs => by rw [hRH s]; exact htr s hs)
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

end Work.FTS.EpsEngine
